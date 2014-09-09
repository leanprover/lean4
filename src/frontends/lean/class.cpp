/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/sstream.h"
#include "kernel/instantiate.h"
#include "library/scoped_ext.h"
#include "library/kernel_serializer.h"
#include "library/opaque_hints.h"
#include "frontends/lean/parser.h"

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
        static name g_class_name("class");
        return g_class_name;
    }
    static std::string const & get_serialization_key() {
        static std::string g_key("class");
        return g_key;
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

environment add_class(environment const & env, name const & n) {
    check_class(env, n);
    return class_ext::add_entry(env, get_dummy_ios(), class_entry(n));
}

static name g_tmp_prefix = name::mk_internal_unique_name();
environment add_instance(environment const & env, name const & n) {
    declaration d = env.get(n);
    expr type = d.get_type();
    name_generator ngen(g_tmp_prefix);
    auto tc = mk_type_checker_with_hints(env, ngen, false);
    while (true) {
        type = tc->whnf(type).first;
        if (!is_pi(type))
            break;
        type = instantiate(binding_body(type), mk_local(ngen.next(), binding_domain(type)));
    }
    name c = get_class_name(env, get_app_fn(type));
    return class_ext::add_entry(env, get_dummy_ios(), class_entry(c, n));
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
    environment env = p.env();
    while (p.curr_is_identifier()) {
        found    = true;
        name c   = p.check_constant_next("invalid 'class instance' declaration, constant expected");
        env = add_instance(env, c);
    }
    if (!found)
        throw parser_error("invalid 'class instance' declaration, at least one identifier expected", p.pos());
    return env;
}

environment add_class_cmd(parser & p) {
    bool found = false;
    environment env = p.env();
    while (p.curr_is_identifier()) {
        found    = true;
        name c   = p.check_constant_next("invalid 'class' declaration, constant expected");
        env = add_class(env, c);
    }
    if (!found)
        throw parser_error("invalid 'class' declaration, at least one identifier expected", p.pos());
    return env;
}

void register_class_cmds(cmd_table & r) {
    add_cmd(r, cmd_info("instance", "add a new instance", add_instance_cmd));
    add_cmd(r, cmd_info("class",    "add a new class", add_class_cmd));
}
}
