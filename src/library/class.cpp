/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "runtime/sstream.h"
#include "util/lbool.h"
#include "util/fresh_name.h"
#include "util/name_set.h"
#include "kernel/instantiate.h"
#include "kernel/for_each_fn.h"
#include "library/scoped_ext.h"
#include "library/constants.h"
#include "library/protected.h"
#include "library/type_context.h"
#include "library/class.h"
#include "library/attribute_manager.h"
#include "library/trace.h"

namespace lean {
enum class class_entry_kind { Class, Instance };
struct class_entry {
    class_entry_kind m_kind;
    name             m_class;
    name             m_instance;    // only relevant if m_kind == Instance
    class_entry():m_kind(class_entry_kind::Class) {}
    explicit class_entry(name const & c):m_kind(class_entry_kind::Class), m_class(c) {}
    class_entry(class_entry_kind k, name const & c, name const & i):
        m_kind(k), m_class(c), m_instance(i) {}
};

struct class_state {
    typedef name_map<names> class_instances;
    typedef name_set        instance_set;

    class_instances       m_instances;
    instance_set          m_instance_set;
    name_set              m_has_out_params;

    bool is_instance(name const & i) const {
        return m_instance_set.contains(i);
    }

    names insert(name const & inst, names const & insts) const {
        if (!insts)
            return names(inst);
        else
            return names(inst, insts);
    }

    void add_class(environment const & env, name const & c) {
        auto it = m_instances.find(c);
        if (!it)
            m_instances.insert(c, names());
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

    void add_instance(name const & c, name const & i) {
        auto it = m_instances.find(c);
        if (!it) {
            m_instances.insert(c, names(i));
        } else {
            auto lst = filter(*it, [&](name const & i1) { return i1 != i; });
            m_instances.insert(c, names(i, lst));
        }
        m_instance_set.insert(i);
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
            s.add_instance(e.m_class, e.m_instance);
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
            s << e.m_class << e.m_instance;
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
            d >> e.m_class >> e.m_instance;
            break;
        }
        return e;
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

bool is_class(environment const & env, name const & c) {
    class_state const & s = class_ext::get_state(env);
    return s.m_instances.contains(c);
}

bool has_class_out_params(environment const & env, name const & c) {
    class_state const & s = class_ext::get_state(env);
    return s.m_has_out_params.contains(c);
}

environment add_instance_core(environment const & env, name const & n, bool persistent) {
    constant_info info = env.get(n);
    expr type = info.get_type();
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
    environment new_env = class_ext::add_entry(env, get_dummy_ios(), class_entry(class_entry_kind::Instance, c, n),
                                               persistent);
    return new_env;
}

bool is_instance(environment const & env, name const & i) {
    class_state const & s = class_ext::get_state(env);
    return s.is_instance(i);
}

names get_class_instances(environment const & env, name const & c) {
    class_state const & s = class_ext::get_state(env);
    return names(s.m_instances.find(c));
}

static name * g_class_attr_name    = nullptr;
static name * g_instance_attr_name = nullptr;

environment add_class(environment const &env, name const &n, bool persistent) {
    return static_cast<basic_attribute const &>(get_system_attribute(*g_class_attr_name)).set(env, get_global_ios(), n, LEAN_DEFAULT_PRIORITY, persistent);
}

environment add_instance(environment const & env, name const & n, bool persistent) {
    return static_cast<basic_attribute const &>(get_system_attribute(*g_instance_attr_name)).set(env, get_global_ios(), n, LEAN_DEFAULT_PRIORITY, persistent);
}

static name * g_anonymous_inst_name_prefix = nullptr;

name const & get_anonymous_instance_prefix() {
    return *g_anonymous_inst_name_prefix;
}

name mk_anonymous_inst_name(unsigned idx) {
    return g_anonymous_inst_name_prefix->append_after(idx);
}

bool is_anonymous_inst_name(name const & n) {
    // remove mangled macro scopes
    auto n2 = n.get_root();
    if (!n2.is_string()) return false;
    return strncmp(n2.get_string().data(),
                   g_anonymous_inst_name_prefix->get_string().data(),
                   strlen(g_anonymous_inst_name_prefix->get_string().data())) == 0;
}

bool is_class_out_param(expr const & e) {
    return is_app_of(e, get_out_param_name(), 1);
}

void initialize_class() {
    g_class_attr_name = new name("class");
    g_instance_attr_name = new name("instance");
    g_class_name = new name("class");
    class_ext::initialize();

    register_system_attribute(basic_attribute(*g_class_attr_name, "type class",
                                              [](environment const & env, io_state const &, name const & d, unsigned,
                                                 bool persistent) {
                                                  return add_class_core(env, d, persistent);
                                             }));

    register_system_attribute(basic_attribute(*g_instance_attr_name, "type class instance",
                                              [](environment const & env, io_state const &, name const & d,
                                                 unsigned, bool persistent) {
                                                  return add_instance_core(env, d, persistent);
                                              }));

    g_anonymous_inst_name_prefix = new name("_inst");
}

void finalize_class() {
    class_ext::finalize();
    delete g_class_name;
    delete g_class_attr_name;
    delete g_anonymous_inst_name_prefix;
}
}
