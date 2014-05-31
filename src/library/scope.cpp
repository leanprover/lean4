/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <memory>
#include "util/list.h"
#include "library/scope.h"
#include "library/kernel_bindings.h"

namespace lean {
struct scope_ext : public environment_extension {
    enum class scope_kind { Namespace, Section };
    struct section {
        environment m_prev_env;
    };
    list<name>       m_namespaces;
    list<section>    m_sections;
    list<scope_kind> m_scope_kinds;
    scope_ext() {}
};

struct scope_ext_reg {
    unsigned m_ext_id;
    scope_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<scope_ext>()); }
};

static scope_ext_reg g_ext;
static scope_ext const & get_extension(environment const & env) {
    return static_cast<scope_ext const &>(env.get_extension(g_ext.m_ext_id));
}
static environment update(environment const & env, scope_ext const & ext) {
    return env.update(g_ext.m_ext_id, std::make_shared<scope_ext>(ext));
}

environment begin_section_scope(environment const & env) {
    // TODO(Leo)
    return env;
}

environment begin_namespace_scope(environment const & env, char const * n) {
    scope_ext ext = get_extension(env);
    ext.m_scope_kinds = list<scope_ext::scope_kind>(scope_ext::scope_kind::Namespace, ext.m_scope_kinds);
    ext.m_namespaces  = list<name>(name(get_namespace(env), n), ext.m_namespaces);
    return update(env, ext);
}

environment end_scope(environment const & env) {
    scope_ext ext = get_extension(env);
    if (is_nil(ext.m_scope_kinds))
        throw exception("environment does not have open scopes");
    switch (head(ext.m_scope_kinds)) {
    case scope_ext::scope_kind::Namespace:
        ext.m_namespaces = tail(ext.m_namespaces);
        break;
    case scope_ext::scope_kind::Section:
        // TODO(Leo)
        break;
    }
    ext.m_scope_kinds = tail(ext.m_scope_kinds);
    return update(env, ext);
}

name const & get_namespace(environment const & env) {
    scope_ext const & ext = get_extension(env);
    if (is_nil(ext.m_namespaces))
        return name::anonymous();
    else
        return head(ext.m_namespaces);
}

optional<declaration> find(environment const & env, name const & n) {
    scope_ext const & ext = get_extension(env);
    for (auto const & p : ext.m_namespaces) {
        name full_name = p + n;
        if (auto d = env.find(full_name)) {
            return d;
        }
    }
    return env.find(n);
}

name get_name_in_namespace(environment const & env, name const & n) {
    if (auto d = env.find(n)) {
        scope_ext const & ext = get_extension(env);
        for (auto const & p : ext.m_namespaces) {
            if (is_prefix_of(p, n)) {
                name r = n.replace_prefix(p, name());
                if (auto d2 = find(env, r)) {
                    if (is_eqp(*d, *d2))
                        return r;
                }
                return n;
            }
        }
    }
    return n;
}

static int begin_section_scope(lua_State * L) { return push_environment(L, begin_section_scope(to_environment(L, 1))); }
static int begin_namespace_scope(lua_State * L) { return push_environment(L, begin_namespace_scope(to_environment(L, 1), lua_tostring(L, 2))); }
static int end_scope(lua_State * L) { return push_environment(L, end_scope(to_environment(L, 1))); }
static int get_namespace(lua_State * L) { return push_name(L, get_namespace(to_environment(L, 1))); }
static int get_name_in_namespace(lua_State * L) {
    return push_name(L, get_name_in_namespace(to_environment(L, 1), to_name_ext(L, 2)));
}
static int find_decl(lua_State * L) { return push_optional_declaration(L, find(to_environment(L, 1), to_name_ext(L, 2))); }

void open_scope(lua_State * L) {
    SET_GLOBAL_FUN(begin_section_scope,   "begin_section_scope");
    SET_GLOBAL_FUN(begin_namespace_scope, "begin_namespace_scope");
    SET_GLOBAL_FUN(end_scope,             "end_scope");
    SET_GLOBAL_FUN(get_namespace,         "get_namespace");
    SET_GLOBAL_FUN(get_name_in_namespace, "get_name_in_namespace");
    SET_GLOBAL_FUN(find_decl,             "find_decl");
}
}
