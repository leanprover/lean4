/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/lbool.h"
#include "util/sstream.h"
#include "kernel/instantiate.h"
#include "library/scoped_ext.h"
#include "library/kernel_serializer.h"
#include "library/reducible.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/util.h"
#include "frontends/lean/tactic_hint.h"

namespace lean {
struct class_entry {
    bool  m_class_cmd;
    name  m_class;
    name  m_instance; // only relevant if m_class_cmd == false
    class_entry():m_class_cmd(false) {}
    explicit class_entry(name const & c):m_class_cmd(true), m_class(c) {}
    class_entry(name const & c, name const & i):m_class_cmd(false), m_class(c), m_instance(i) {}
};

struct class_state {
    typedef rb_map<name, list<name>, name_quick_cmp> class_instances;
    class_instances m_instances;
    void add_class(name const & c) {
        auto it = m_instances.find(c);
        if (!it)
            m_instances.insert(c, list<name>());
    }
    void add_instance(name const & c, name const & i) {
        auto it = m_instances.find(c);
        if (!it)
            m_instances.insert(c, to_list(i));
        else
            m_instances.insert(c, cons(i, filter(*it, [&](name const & i1) { return i1 != i; })));
    }
};

static name * g_class_name = nullptr;
static std::string * g_key = nullptr;

struct class_config {
    typedef class_state state;
    typedef class_entry entry;
    static void add_entry(environment const &, io_state const &, state & s, entry const & e) {
        if (e.m_class_cmd)
            s.add_class(e.m_class);
        else
            s.add_instance(e.m_class, e.m_instance);
    }
    static name const & get_class_name() {
        return *g_class_name;
    }
    static std::string const & get_serialization_key() {
        return *g_key;
    }
    static void  write_entry(serializer & s, entry const & e) {
        if (e.m_class_cmd)
            s << true << e.m_class;
        else
            s << false << e.m_class << e.m_instance;
    }
    static entry read_entry(deserializer & d) {
        entry e;
        d >> e.m_class_cmd;
        if (e.m_class_cmd)
            d >> e.m_class;
        else
            d >> e.m_class >> e.m_instance;
        return e;
    }
};

template class scoped_ext<class_config>;
typedef scoped_ext<class_config> class_ext;

static void check_class(environment const & env, name const & c_name) {
    declaration c_d = env.get(c_name);
    if (c_d.is_definition() && !c_d.is_opaque())
        throw exception(sstream() << "invalid class, '" << c_name << "' is a transparent definition");
}

name get_class_name(environment const & env, expr const & e) {
    if (!is_constant(e))
        throw exception("class expected, expression is not a constant");
    name const & c_name = const_name(e);
    check_class(env, c_name);
    return c_name;
}

environment add_class(environment const & env, name const & n, bool persistent) {
    check_class(env, n);
    return class_ext::add_entry(env, get_dummy_ios(), class_entry(n), persistent);
}

static name * g_tmp_prefix = nullptr;
environment add_instance(environment const & env, name const & n, bool persistent) {
    declaration d = env.get(n);
    expr type = d.get_type();
    name_generator ngen(*g_tmp_prefix);
    auto tc = mk_type_checker(env, ngen, false);
    while (true) {
        type = tc->whnf(type).first;
        if (!is_pi(type))
            break;
        type = instantiate(binding_body(type), mk_local(ngen.next(), binding_domain(type)));
    }
    name c = get_class_name(env, get_app_fn(type));
    return class_ext::add_entry(env, get_dummy_ios(), class_entry(c, n), persistent);
}

bool is_class(environment const & env, name const & c) {
    class_state const & s = class_ext::get_state(env);
    return s.m_instances.contains(c);
}

list<name> get_class_instances(environment const & env, name const & c) {
    class_state const & s = class_ext::get_state(env);
    return ptr_to_list(s.m_instances.find(c));
}

environment add_instance_cmd(parser & p) {
    bool found = false;
    bool persistent = false;
    parse_persistent(p, persistent);
    environment env = p.env();
    while (p.curr_is_identifier()) {
        found    = true;
        name c   = p.check_constant_next("invalid 'class instance' declaration, constant expected");
        env = add_instance(env, c, persistent);
    }
    if (!found)
        throw parser_error("invalid 'class instance' declaration, at least one identifier expected", p.pos());
    return env;
}


environment add_class_cmd(parser & p) {
    bool found = false;
    environment env = p.env();
    bool persistent = false;
    parse_persistent(p, persistent);
    while (p.curr_is_identifier()) {
        found    = true;
        name c   = p.check_constant_next("invalid 'class' declaration, constant expected");
        env = add_class(env, c, persistent);
    }
    if (!found)
        throw parser_error("invalid 'class' declaration, at least one identifier expected", p.pos());
    return env;
}

void register_class_cmds(cmd_table & r) {
    add_cmd(r, cmd_info("instance", "add a new instance", add_instance_cmd));
    add_cmd(r, cmd_info("class",    "add a new class", add_class_cmd));
}

/** \brief If the constant \c e is a class, return its name */
optional<name> constant_is_ext_class(environment const & env, expr const & e) {
    name const & cls_name = const_name(e);
    if (is_class(env, cls_name) || !empty(get_tactic_hints(env, cls_name))) {
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
lbool is_quick_ext_class(type_checker const & tc, expr const & type, name & result) {
    environment const & env = tc.env();
    expr const * it         = &type;
    while (true) {
        switch (it->kind()) {
        case expr_kind::Var:  case expr_kind::Sort:   case expr_kind::Local:
        case expr_kind::Meta: case expr_kind::Lambda:
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
optional<name> is_full_ext_class(type_checker & tc, expr type) {
    type = tc.whnf(type).first;
    if (is_pi(type)) {
        return is_full_ext_class(tc, instantiate(binding_body(type), mk_local(tc.mk_fresh_name(), binding_domain(type))));
    } else {
        expr f = get_app_fn(type);
        if (!is_constant(f))
            return optional<name>();
        return constant_is_ext_class(tc.env(), f);
    }
}

/** \brief Return true iff \c type is a class or Pi that produces a class. */
optional<name> is_ext_class(type_checker & tc, expr const & type) {
    name result;
    switch (is_quick_ext_class(tc, type, result)) {
    case l_true:  return optional<name>(result);
    case l_false: return optional<name>();
    case l_undef: break;
    }
    return is_full_ext_class(tc, type);
}

/** \brief Return a list of instances of the class \c cls_name that occur in \c ctx */
list<expr> get_local_instances(type_checker & tc, list<expr> const & ctx, name const & cls_name) {
    buffer<expr> buffer;
    for (auto const & l : ctx) {
        if (!is_local(l))
            continue;
        expr inst_type    = mlocal_type(l);
        if (auto it = is_ext_class(tc, inst_type))
            if (*it == cls_name)
                buffer.push_back(l);
    }
    return to_list(buffer.begin(), buffer.end());
}
void initialize_class() {
    g_tmp_prefix = new name(name::mk_internal_unique_name());
    g_class_name = new name("class");
    g_key = new std::string("class");
    class_ext::initialize();
}

void finalize_class() {
    class_ext::finalize();
    delete g_key;
    delete g_class_name;
    delete g_tmp_prefix;
}
}
