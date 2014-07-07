/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/sstream.h"
#include "library/scoped_ext.h"
#include "library/kernel_serializer.h"
#include "frontends/lean/parser.h"

namespace lean {
struct class_entry {
    enum class kind { NewClass, NewInstance };
    kind  m_kind;
    name  m_class;
    name  m_instance;
    class_entry() {}
    class_entry(name const & c):m_kind(kind::NewClass), m_class(c) {}
    class_entry(name const & c, name const & i):m_kind(kind::NewInstance), m_class(c), m_instance(i) {}
    bool is_new_class() const { return m_kind == kind::NewClass; }
};

struct class_state {
    typedef rb_map<name, list<name>, name_quick_cmp> class_instances;
    class_instances m_instances;
    void add_class(name const & c) {
        m_instances.insert(c, list<name>());
    }
    void add_instance(name const & c, name const & i) {
        auto it = m_instances.find(c);
        if (!it)
            m_instances.insert(c, list<name>(i));
        else
            m_instances.insert(c, cons(i, filter(*it, [&](name const & i1) { return i1 != i; })));
    }
};

struct class_config {
    typedef class_state state;
    typedef class_entry entry;
    static void add_entry(environment const &, io_state const &, state & s, entry const & e) {
        if (e.m_kind == class_entry::kind::NewClass) {
            s.add_class(e.m_class);
        } else {
            s.add_instance(e.m_class, e.m_instance);
        }
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
        s.write_char(static_cast<char>(e.m_kind)); // NOLINT
        if (e.is_new_class())
            s << e.m_class;
        else
            s << e.m_class << e.m_instance;
    }
    static entry read_entry(deserializer & d) {
        entry e;
        e.m_kind = static_cast<class_entry::kind>(d.read_char());
        if (e.is_new_class())
            d >> e.m_class;
        else
            d >> e.m_class >> e.m_instance;
        return e;
    }
};

template class scoped_ext<class_config>;
typedef scoped_ext<class_config> class_ext;

environment add_class(environment const & env, name const & n) {
    declaration d = env.get(n);
    if (d.is_definition() && !d.is_opaque())
        throw exception(sstream() << "invalid class declaration, '" << n << "' is not an opaque definition");
    class_state const & s = class_ext::get_state(env);
    if (s.m_instances.contains(n))
        throw exception(sstream() << "class '" << n << "' has already been declared");
    return class_ext::add_entry(env, get_dummy_ios(), class_entry(n));
}

environment add_instance(environment const & env, name const & n) {
    declaration d = env.get(n);
    expr type = d.get_type();
    while (is_pi(type))
        type = binding_body(type);
    if (!is_constant(get_app_fn(type)))
        throw exception(sstream() << "invalid class instance declaration '" << n << "' resultant type must be a class");
    name const & c = const_name(get_app_fn(type));
    return class_ext::add_entry(env, get_dummy_ios(), class_entry(c, n));
}

bool is_class(environment const & env, name const & c) {
    class_state const & s = class_ext::get_state(env);
    return s.m_instances.contains(c);
}

list<name> get_class_instances(environment const & env, name const & c) {
    class_state const & s = class_ext::get_state(env);
    if (auto it = s.m_instances.find(c))
        return *it;
    else
        return list<name>();
}

environment add_class_cmd(parser & p) {
    auto pos = p.pos();
    name c   = p.check_id_next("invalid 'class' declaration, identifier expected");
    expr e   = p.id_to_expr(c, pos);
    if (!is_constant(e)) throw parser_error(sstream() << "invalid 'class' declaration, '" << c << "' is not a constant", pos);
    return add_class(p.env(), const_name(e));
}

environment add_instance_cmd(parser & p) {
    auto pos = p.pos();
    name c   = p.check_id_next("invalid 'class instance' declaration, identifier expected");
    expr e   = p.id_to_expr(c, pos);
    if (!is_constant(e)) throw parser_error(sstream() << "invalid 'class instance' declaration, '" << c << "' is not a constant", pos);
    return add_instance(p.env(), const_name(e));
}

void register_class_cmds(cmd_table & r) {
    add_cmd(r, cmd_info("class", "add a new class", add_class_cmd));
    add_cmd(r, cmd_info("instance", "add a new instance", add_instance_cmd));
}
}
