/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/lbool.h"
#include "util/sstream.h"
#include "util/fresh_name.h"
#include "kernel/instantiate.h"
#include "library/scoped_ext.h"
#include "library/kernel_serializer.h"
#include "library/reducible.h"
#include "library/aliases.h"
#include "library/tc_multigraph.h"
#include "library/protected.h"
#include "library/class.h"
#include "library/attribute_manager.h"

namespace lean {
enum class class_entry_kind { Class, Instance, TransInstance, DerivedTransInstance };
struct class_entry {
    class_entry_kind m_kind;
    name             m_class;
    name             m_instance; // only relevant if m_kind == Instance
    unsigned         m_priority; // only relevant if m_kind == Instance
    name             m_source;   // for TransInstance and DerivedTransInstance, we also store the source class
    class_entry():m_kind(class_entry_kind::Class), m_priority(0) {}
    explicit class_entry(name const & c):m_kind(class_entry_kind::Class), m_class(c), m_priority(0) {}
    class_entry(class_entry_kind k, name const & c, name const & i, unsigned p):
        m_kind(k), m_class(c), m_instance(i), m_priority(p) {}
    class_entry(name const & src, name const & tgt, name const & i, unsigned p):
        m_kind(class_entry_kind::TransInstance), m_class(tgt), m_instance(i), m_priority(p), m_source(src) {}
    class_entry(name const & src, name const & tgt, name const & i):
        m_kind(class_entry_kind::DerivedTransInstance), m_class(tgt), m_instance(i),
        m_priority(0), m_source(src) {}

    static class_entry mk_trans_inst(name const & src, name const & tgt, name const & i, unsigned p) {
        return class_entry(src, tgt, i, p);
    }
    static class_entry mk_derived_trans_inst(name const & src, name const & tgt, name const & i) {
        return class_entry(src, tgt, i);
    }
};

struct class_state {
    typedef name_map<list<name>> class_instances;
    typedef name_map<unsigned>   instance_priorities;
    class_instances       m_instances;
    class_instances       m_derived_trans_instances;
    instance_priorities   m_priorities;
    name_set              m_derived_trans_instance_set;
    tc_multigraph         m_mgraph;

    class_state():m_mgraph("transitive instance") {}

    unsigned get_priority(name const & i) const {
        if (auto it = m_priorities.find(i))
            return *it;
        else
            return LEAN_DEFAULT_PRIORITY;
    }

    bool is_instance(name const & i) const {
        return m_priorities.contains(i);
    }

    bool is_derived_trans_instance(name const & i) const {
        return m_derived_trans_instance_set.contains(i);
    }

    list<name> insert(name const & inst, unsigned priority, list<name> const & insts) const {
        if (!insts)
            return to_list(inst);
        else if (priority >= get_priority(head(insts)))
            return list<name>(inst, insts);
        else
            return list<name>(head(insts), insert(inst, priority, tail(insts)));
    }

    void add_class(name const & c) {
        auto it = m_instances.find(c);
        if (!it)
            m_instances.insert(c, list<name>());
    }

    void add_instance(name const & c, name const & i, unsigned p) {
        auto it = m_instances.find(c);
        if (!it) {
            m_instances.insert(c, to_list(i));
        } else {
            auto lst = filter(*it, [&](name const & i1) { return i1 != i; });
            m_instances.insert(c, insert(i, p, lst));
        }
        m_priorities.insert(i, p);
    }

    void add_trans_instance(environment const & env, name const & src, name const & tgt, name const & i, unsigned p) {
        add_instance(tgt, i, p);
        m_mgraph.add1(env, src, i, tgt);
    }

    void add_derived_trans_instance(environment const & env, name const & src, name const & tgt, name const & i) {
        auto it = m_derived_trans_instances.find(tgt);
        if (!it) {
            m_derived_trans_instances.insert(tgt, to_list(i));
        } else {
            auto lst = filter(*it, [&](name const & i1) { return i1 != i; });
            m_derived_trans_instances.insert(tgt, cons(i, lst));
        }
        m_derived_trans_instance_set.insert(i);
        m_mgraph.add1(env, src, i, tgt);
    }
};

static name * g_class_name = nullptr;
static std::string * g_key = nullptr;

struct class_config {
    typedef class_state state;
    typedef class_entry entry;
    static void add_entry(environment const & env, io_state const &, state & s, entry const & e) {
        switch (e.m_kind) {
        case class_entry_kind::Class:
            s.add_class(e.m_class);
            break;
        case class_entry_kind::Instance:
            s.add_instance(e.m_class, e.m_instance, e.m_priority);
            break;
        case class_entry_kind::TransInstance:
            s.add_trans_instance(env, e.m_source, e.m_class, e.m_instance, e.m_priority);
            break;
        case class_entry_kind::DerivedTransInstance:
            s.add_derived_trans_instance(env, e.m_source, e.m_class, e.m_instance);
            break;
        }
    }
    static name const & get_class_name() {
        return *g_class_name;
    }
    static std::string const & get_serialization_key() {
        return *g_key;
    }
    static void  write_entry(serializer & s, entry const & e) {
        s << static_cast<char>(e.m_kind);
        switch (e.m_kind) {
        case class_entry_kind::Class:
            s << e.m_class;
            break;
        case class_entry_kind::Instance:
            s << e.m_class << e.m_instance << e.m_priority;
            break;
        case class_entry_kind::TransInstance:
            s << e.m_source << e.m_class << e.m_instance << e.m_priority;
            break;
        case class_entry_kind::DerivedTransInstance:
            s << e.m_source << e.m_class << e.m_instance;
            break;
        }
    }
    static entry read_entry(deserializer & d) {
        entry e; char k;
        d >> k;
        e.m_kind = static_cast<class_entry_kind>(k);
        switch (e.m_kind) {
        case class_entry_kind::Class:
            d >> e.m_class;
            break;
        case class_entry_kind::Instance:
            d >> e.m_class >> e.m_instance >> e.m_priority;
            break;
        case class_entry_kind::TransInstance:
            d >> e.m_source >> e.m_class >> e.m_instance >> e.m_priority;
            break;
        case class_entry_kind::DerivedTransInstance:
            d >> e.m_source >> e.m_class >> e.m_instance;
            break;
        }
        return e;
    }
    static optional<unsigned> get_fingerprint(entry const & e) {
        switch (e.m_kind) {
        case class_entry_kind::Class:
            return some(e.m_class.hash());
        case class_entry_kind::Instance:
        case class_entry_kind::TransInstance:
            return some(hash(hash(e.m_class.hash(), e.m_instance.hash()), e.m_priority));
        case class_entry_kind::DerivedTransInstance:
            return some(hash(e.m_class.hash(), e.m_instance.hash()));
        }
        lean_unreachable();
    }
};

template class scoped_ext<class_config>;
typedef scoped_ext<class_config> class_ext;

static void check_class(environment const & env, name const & c_name) {
    env.get(c_name);
}

static void check_is_class(environment const & env, name const & c_name) {
    class_state const & s = class_ext::get_state(env);
    if (!s.m_instances.contains(c_name))
        throw exception(sstream() << "'" << c_name << "' is not a class");
}

name get_class_name(environment const & env, expr const & e) {
    if (!is_constant(e))
        throw exception("class expected, expression is not a constant");
    name const & c_name = const_name(e);
    check_is_class(env, c_name);
    return c_name;
}

environment add_class(environment const &env, name const &n, bool persistent) {
    check_class(env, n);
    return class_ext::add_entry(env, get_dummy_ios(), class_entry(n), persistent);
}

void get_classes(environment const & env, buffer<name> & classes) {
    class_state const & s = class_ext::get_state(env);
    s.m_instances.for_each([&](name const & c, list<name> const &) {
            classes.push_back(c);
        });
}

bool is_class(environment const & env, name const & c) {
    class_state const & s = class_ext::get_state(env);
    return s.m_instances.contains(c);
}

old_type_checker_ptr mk_class_type_checker(environment const & env, bool conservative) {
    auto pred = conservative ? mk_not_reducible_pred(env) : mk_irreducible_pred(env);
    class_state s = class_ext::get_state(env);
    return mk_type_checker(env, [=](name const & n) {
            return s.m_instances.contains(n) || pred(n);
        });
}

static environment set_reducible_if_def(environment const & env, name const & n, bool persistent) {
    declaration const & d = env.get(n);
    if (d.is_definition() && !d.is_theorem())
        return set_reducible(env, n, reducible_status::Reducible, persistent);
    else
        return env;
}

environment add_instance(environment const & env, name const & n, unsigned priority, bool persistent) {
    declaration d = env.get(n);
    expr type = d.get_type();
    auto tc = mk_class_type_checker(env, false);
    while (true) {
        type = tc->whnf(type).first;
        if (!is_pi(type))
            break;
        type = instantiate(binding_body(type), mk_local(mk_fresh_name(), binding_domain(type)));
    }
    name c = get_class_name(env, get_app_fn(type));
    check_is_class(env, c);
    environment new_env = class_ext::add_entry(env, get_dummy_ios(), class_entry(class_entry_kind::Instance, c, n, priority),
                                               persistent);
    return set_reducible_if_def(new_env, n, persistent);
}

static name * g_source = nullptr;

static pair<name, name> get_source_target(environment const & env, old_type_checker & tc, name const & n) {
    buffer<expr> domain;
    declaration const & d = env.get(n);
    expr codomain      = to_telescope(tc, d.get_type(), domain);
    optional<name> tgt = is_ext_class(tc, codomain);
    if (!tgt)
        throw exception(sstream() << "invalid transitive instance, resulting type of '" << n << "' is not a class");
    optional<name> src;
    unsigned i = domain.size();
    while (i > 0) {
        --i;
        expr const & d = domain[i];
        if (auto it = is_ext_class(tc, mlocal_type(d))) {
            src = it;
            break;
        }
    }
    if (!src)
        src = *g_source;
    return mk_pair(*src, *tgt);
}

environment add_trans_instance(environment const & env, name const & n, unsigned priority, bool persistent) {
    old_type_checker_ptr  tc     = mk_type_checker(env);
    pair<name, name> src_tgt = get_source_target(env, *tc, n);
    class_state const & s = class_ext::get_state(env);
    tc_multigraph g    = s.m_mgraph;
    pair<environment, list<tc_edge>> new_env_insts = g.add(env, src_tgt.first, n, src_tgt.second);
    environment new_env = new_env_insts.first;
    new_env = class_ext::add_entry(new_env, get_dummy_ios(),
                                   class_entry::mk_trans_inst(src_tgt.first, src_tgt.second, n, priority), persistent);
    new_env = set_reducible_if_def(new_env, n, persistent);
    for (tc_edge const & edge : new_env_insts.second) {
        new_env = class_ext::add_entry(new_env, get_dummy_ios(),
                                       class_entry::mk_derived_trans_inst(edge.m_from, edge.m_to, edge.m_cnst), persistent);
        new_env = set_reducible(new_env, edge.m_cnst, reducible_status::Reducible, persistent);
        new_env = add_protected(new_env, edge.m_cnst);
    }
    return new_env;
}

name_predicate mk_class_pred(environment const & env) {
    class_state const & s = class_ext::get_state(env);
    class_state::class_instances cs = s.m_instances;
    return [=](name const & n) { return cs.contains(n); }; // NOLINT
}

name_predicate mk_instance_pred(environment const & env) {
    class_state const & s = class_ext::get_state(env);
    class_state::instance_priorities insts = s.m_priorities;
    name_set der_insts = s.m_derived_trans_instance_set;
    return [=](name const & n) { return insts.contains(n) || der_insts.contains(n); }; // NOLINT
}

bool is_derived_trans_instance(environment const & env, name const & i) {
    class_state const & s = class_ext::get_state(env);
    return s.is_derived_trans_instance(i);
}

list<name> get_class_instances(environment const & env, name const & c) {
    class_state const & s = class_ext::get_state(env);
    return ptr_to_list(s.m_instances.find(c));
}

list<name> get_class_derived_trans_instances(environment const & env, name const & c) {
    class_state const & s = class_ext::get_state(env);
    return ptr_to_list(s.m_derived_trans_instances.find(c));
}

/** \brief If the constant \c e is a class, return its name */
static optional<name> constant_is_ext_class(environment const & env, expr const & e) {
    name const & cls_name = const_name(e);
    if (is_class(env, cls_name)) {
        return optional<name>(cls_name);
    } else {
        return optional<name>();
    }
}

/** \brief Partial/Quick test for is_ext_class. Result
    l_true:   \c type is a class, and the name of the class is stored in \c result.
    l_false:  \c type is not a class.
    l_undef:  procedure did not establish whether \c type is a class or not.
*/
static lbool is_quick_ext_class(old_type_checker const & tc, expr const & type, name & result) {
    environment const & env = tc.env();
    expr const * it         = &type;
    while (true) {
        switch (it->kind()) {
        case expr_kind::Var:  case expr_kind::Sort:   case expr_kind::Local:
        case expr_kind::Meta: case expr_kind::Lambda: case expr_kind::Let:
            return l_false;
        case expr_kind::Macro:
            return l_undef;
        case expr_kind::Constant:
            if (auto r = constant_is_ext_class(env, *it)) {
                result = *r;
                return l_true;
            } else if (tc.is_opaque(*it)) {
                return l_false;
            } else {
                return l_undef;
            }
        case expr_kind::App: {
            expr const & f = get_app_fn(*it);
            if (is_constant(f)) {
                if (auto r = constant_is_ext_class(env, f)) {
                    result = *r;
                    return l_true;
                } else if (tc.is_opaque(f)) {
                    return l_false;
                } else {
                    return l_undef;
                }
            } else if (is_lambda(f) || is_macro(f)) {
                return l_undef;
            } else {
                return l_false;
            }
        }
        case expr_kind::Pi:
            it = &binding_body(*it);
            break;
        }
    }
}

/** \brief Full/Expensive test for \c is_ext_class */
static optional<name> is_full_ext_class(old_type_checker & tc, expr type) {
    type = tc.whnf(type).first;
    if (is_pi(type)) {
        return is_full_ext_class(tc, instantiate(binding_body(type), mk_local(mk_fresh_name(), binding_domain(type))));
    } else {
        expr f = get_app_fn(type);
        if (!is_constant(f))
            return optional<name>();
        return constant_is_ext_class(tc.env(), f);
    }
}

/** \brief Return true iff \c type is a class or Pi that produces a class. */
optional<name> is_ext_class(old_type_checker & tc, expr const & type) {
    name result;
    switch (is_quick_ext_class(tc, type, result)) {
    case l_true:  return optional<name>(result);
    case l_false: return optional<name>();
    case l_undef: break;
    }
    return is_full_ext_class(tc, type);
}

void initialize_class() {
    g_source     = new name("_source");
    g_key = new std::string("class");
    class_ext::initialize();

    register_no_params_attribute("class", "type class",
                                 [](environment const & env, io_state const &, name const & d, bool persistent) {
                                     return add_class(env, d, persistent);
                                 });

    register_prio_attribute("instance", "type class instance",
                            [](environment const & env, io_state const &, name const & d, unsigned prio, bool persistent) {
                                return add_instance(env, d, prio, persistent);
                            });

    register_prio_attribute("trans_instance", "transitive type class instance",
                            [](environment const & env, io_state const &, name const & d, unsigned prio, bool persistent) {
                                return add_trans_instance(env, d, prio, persistent);
                            });
}

void finalize_class() {
    class_ext::finalize();
    delete g_key;
    delete g_source;
}
}
