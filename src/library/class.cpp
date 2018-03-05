/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/lbool.h"
#include "util/sstream.h"
#include "util/fresh_name.h"
#include "util/name_set.h"
#include "kernel/type_checker.h"
#include "kernel/instantiate.h"
#include "kernel/for_each_fn.h"
#include "library/scoped_ext.h"
#include "library/constants.h"
#include "library/kernel_serializer.h"
#include "library/aliases.h"
#include "library/protected.h"
#include "library/type_context.h"
#include "library/class.h"
#include "library/attribute_manager.h"
#include "library/trace.h"

namespace lean {
enum class class_entry_kind { Class, Instance, Tracker };
struct class_entry {
    class_entry_kind m_kind;
    name             m_class;
    name             m_instance;    // only relevant if m_kind == Instance
    unsigned         m_priority{0}; // only relevant if m_kind == Instance
    name             m_track_attr;  // only relevant if m_kind == Tracker
    class_entry():m_kind(class_entry_kind::Class) {}
    explicit class_entry(name const & c):m_kind(class_entry_kind::Class), m_class(c) {}
    class_entry(class_entry_kind k, name const & c, name const & i, unsigned p):
        m_kind(k), m_class(c), m_instance(i), m_priority(p) {}
    class_entry(name const & c, name const & track_attr):
        m_kind(class_entry_kind::Tracker), m_class(c), m_track_attr(track_attr) {}
};

struct class_state {
    typedef name_map<list<name>> class_instances;
    typedef name_map<unsigned>   instance_priorities;
    typedef name_map<list<name>> class_track_attrs;
    typedef name_map<name_set>   attr_symbols;

    class_instances       m_instances;
    instance_priorities   m_priorities;
    class_track_attrs     m_class_track_attrs;
    attr_symbols          m_attr_symbols;
    name_set              m_has_out_params;

    unsigned get_priority(name const & i) const {
        if (auto it = m_priorities.find(i))
            return *it;
        else
            return LEAN_DEFAULT_PRIORITY;
    }

    bool is_instance(name const & i) const {
        return m_priorities.contains(i);
    }

    list<name> insert(name const & inst, unsigned priority, list<name> const & insts) const {
        if (!insts)
            return to_list(inst);
        else if (priority >= get_priority(head(insts)))
            return list<name>(inst, insts);
        else
            return list<name>(head(insts), insert(inst, priority, tail(insts)));
    }

    void add_class(environment const & env, name const & c) {
        auto it = m_instances.find(c);
        if (!it)
            m_instances.insert(c, list<name>());
        expr type = env.get(c).get_type();
        bool has_out_param = false;
        while (is_pi(type)) {
            if (is_class_out_param(binding_domain(type))) {
                has_out_param = true;
                break;
            }
            type = binding_body(type);
        }
        if (has_out_param)
            m_has_out_params.insert(c);
    }

    void collect_symbols(type_checker & tc, name const & inst, name const & attr) {
        environment const & env = tc.env();
        name_set S;
        if (auto curr_S = m_attr_symbols.find(attr))
            S = *curr_S;
        buffer<expr> params;
        expr type = to_telescope(tc, env.get(inst).get_type(), params);
        buffer<expr> args;
        get_app_args(type, args);
        for (expr const & arg : args) {
            expr arg_type = tc.whnf(tc.infer(arg));
            if (!is_sort(arg_type)) {
                /* We only track symbols that are not occurring in types */
                for_each(arg, [&](expr const & e, unsigned) {
                        if (is_constant(e))
                            S.insert(const_name(e));
                        return true;
                    });
            }
        }
        if (!S.empty())
            m_attr_symbols.insert(attr, S);
    }

    void add_instance(environment const & env, name const & c, name const & i, unsigned p) {
        auto it = m_instances.find(c);
        if (!it) {
            m_instances.insert(c, to_list(i));
        } else {
            auto lst = filter(*it, [&](name const & i1) { return i1 != i; });
            m_instances.insert(c, insert(i, p, lst));
        }
        m_priorities.insert(i, p);
        if (auto attrs = m_class_track_attrs.find(c)) {
            type_checker tc(env);
            for (name const & attr : *attrs) {
                collect_symbols(tc, i, attr);
            }
        }
    }

    void track_symbols(name const & c, name const & attr_name) {
        if (auto s = m_class_track_attrs.find(c)) {
            m_class_track_attrs.insert(c, cons(attr_name, *s));
        } else {
            m_class_track_attrs.insert(c, to_list(attr_name));
        }
    }
};

static name * g_class_name = nullptr;

struct class_config {
    typedef class_state state;
    typedef class_entry entry;
    static void add_entry(environment const & env, io_state const &, state & s, entry const & e) {
        switch (e.m_kind) {
        case class_entry_kind::Class:
            s.add_class(env, e.m_class);
            break;
        case class_entry_kind::Instance:
            s.add_instance(env, e.m_class, e.m_instance, e.m_priority);
            break;
        case class_entry_kind::Tracker:
            s.track_symbols(e.m_class, e.m_track_attr);
            break;
        }
    }

    static name const & get_class_name() {
        return *g_class_name;
    }

    static const char * get_serialization_key() { return "class"; }

    static void  write_entry(serializer & s, entry const & e) {
        s << static_cast<char>(e.m_kind);
        switch (e.m_kind) {
        case class_entry_kind::Class:
            s << e.m_class;
            break;
        case class_entry_kind::Instance:
            s << e.m_class << e.m_instance << e.m_priority;
            break;
        case class_entry_kind::Tracker:
            s << e.m_class << e.m_track_attr;
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
        case class_entry_kind::Tracker:
            d >> e.m_class >> e.m_track_attr;
            break;
        }
        return e;
    }

    static optional<unsigned> get_fingerprint(entry const & e) {
        switch (e.m_kind) {
        case class_entry_kind::Class:
            return some(e.m_class.hash());
        case class_entry_kind::Instance:
            return some(hash(hash(e.m_class.hash(), e.m_instance.hash()), e.m_priority));
        case class_entry_kind::Tracker:
            return some(hash(e.m_class.hash(), e.m_track_attr.hash()));
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

environment add_class_core(environment const & env, name const &n, bool persistent) {
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

bool has_class_out_params(environment const & env, name const & c) {
    class_state const & s = class_ext::get_state(env);
    return s.m_has_out_params.contains(c);
}

environment add_instance_core(environment const & env, name const & n, unsigned priority, bool persistent) {
    declaration d = env.get(n);
    expr type = d.get_type();
    type_context_old ctx(env, transparency_mode::All);
    class_state S = class_ext::get_state(env);
    type_context_old::tmp_locals locals(ctx);
    while (true) {
        type = ctx.whnf_head_pred(type, [&](expr const & e) {
                expr const & fn = get_app_fn(e);
                return !is_constant(fn) || !S.m_instances.contains(const_name(fn)); });
        if (!is_pi(type))
            break;
        expr x = locals.push_local_from_binding(type);
        type = instantiate(binding_body(type), x);
    }
    name c = get_class_name(env, get_app_fn(type));
    check_is_class(env, c);
    environment new_env = class_ext::add_entry(env, get_dummy_ios(), class_entry(class_entry_kind::Instance, c, n, priority),
                                               persistent);
    return new_env;
}

bool is_instance(environment const & env, name const & i) {
    class_state const & s = class_ext::get_state(env);
    return s.is_instance(i);
}

unsigned get_instance_priority(environment const & env, name const & n) {
    class_state const & s                  = class_ext::get_state(env);
    class_state::instance_priorities insts = s.m_priorities;
    if (auto r = insts.find(n))
        return *r;
    return LEAN_DEFAULT_PRIORITY;
}

name_predicate mk_class_pred(environment const & env) {
    class_state const & s = class_ext::get_state(env);
    class_state::class_instances cs = s.m_instances;
    return [=](name const & n) { return cs.contains(n); }; // NOLINT
}

name_predicate mk_instance_pred(environment const & env) {
    class_state const & s = class_ext::get_state(env);
    class_state::instance_priorities insts = s.m_priorities;
    return [=](name const & n) { return insts.contains(n); }; // NOLINT
}

list<name> get_class_instances(environment const & env, name const & c) {
    class_state const & s = class_ext::get_state(env);
    return ptr_to_list(s.m_instances.find(c));
}

static name * g_class_attr_name    = nullptr;
static name * g_instance_attr_name = nullptr;

environment add_class(environment const &env, name const &n, bool persistent) {
    return static_cast<basic_attribute const &>(get_system_attribute(*g_class_attr_name)).set(env, get_global_ios(), n, LEAN_DEFAULT_PRIORITY, persistent);
}

environment add_instance(environment const & env, name const & n, unsigned priority, bool persistent) {
    return static_cast<basic_attribute const &>(get_system_attribute(*g_instance_attr_name)).set(env, get_global_ios(), n, priority, persistent);
}

name const & get_instance_attr_name() {
    return *g_instance_attr_name;
}

unsigned get_instance_fingerprint(environment const & env) {
    return get_attribute_fingerprint(env, get_instance_attr_name());
}

static name * g_anonymous_inst_name_prefix = nullptr;

name const & get_anonymous_instance_prefix() {
    return *g_anonymous_inst_name_prefix;
}

name mk_anonymous_inst_name(unsigned idx) {
    return g_anonymous_inst_name_prefix->append_after(idx);
}

bool is_anonymous_inst_name(name const & n) {
    if (!n.is_atomic() || !n.is_string()) return false;
    return strncmp(n.get_string(),
                   g_anonymous_inst_name_prefix->get_string(),
                   strlen(g_anonymous_inst_name_prefix->get_string())) == 0;
}

bool is_class_out_param(expr const & e) {
    return is_app_of(e, get_out_param_name(), 1);
}

static name_set * g_tracking_attributes = nullptr;

void register_class_symbol_tracking_attribute(name const & n, char const * descr) {
    if (g_tracking_attributes->contains(n))
        throw exception(sstream() << "invalid type class tracking attribute '" << n << "', attribute has already been defined");
    g_tracking_attributes->insert(n);
    register_system_attribute(basic_attribute(n, descr,
                                              [=](environment const & env, io_state const &, name const & d, unsigned, bool persistent) {
                                                  if (!persistent) {
                                                      throw exception(sstream() << "invalid attribute [" << n << "] at '" << d << "', "
                                                                      << "it must not be 'local'");
                                                  }
                                                  if (!is_class(env, d)) {
                                                      throw exception(sstream() << "invalid attribute [" << n << "] at '" << d << "', "
                                                                      << "declaration is not a class");
                                                  }
                                                  return class_ext::add_entry(env, get_dummy_ios(), class_entry(d, n), persistent);
                                              }));
}

bool is_class_symbol_tracking_attribute(name const & n) {
    return g_tracking_attributes->contains(n);
}

name_set get_class_attribute_symbols(environment const & env, name const & attr_name) {
    class_state const & s = class_ext::get_state(env);
    if (name_set const * S = s.m_attr_symbols.find(attr_name))
        return *S;
    else
        return name_set();
}

void initialize_class() {
    g_class_attr_name = new name("class");
    g_instance_attr_name = new name("instance");
    g_class_name = new name("class");
    g_tracking_attributes = new name_set();
    class_ext::initialize();

    register_system_attribute(basic_attribute(*g_class_attr_name, "type class",
                                              [](environment const & env, io_state const &, name const & d, unsigned,
                                                 bool persistent) {
                                                  return add_class_core(env, d, persistent);
                                             }));

    register_system_attribute(basic_attribute(*g_instance_attr_name, "type class instance",
                                              [](environment const & env, io_state const &, name const & d,
                                                 unsigned prio, bool persistent) {
                                                  return add_instance_core(env, d, prio, persistent);
                                              }));

    g_anonymous_inst_name_prefix = new name("_inst");
}

void finalize_class() {
    class_ext::finalize();
    delete g_class_name;
    delete g_class_attr_name;
    delete g_instance_attr_name;
    delete g_anonymous_inst_name_prefix;
    delete g_tracking_attributes;
}
}
