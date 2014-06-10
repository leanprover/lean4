/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include "util/rb_map.h"
#include "util/name_generator.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "library/expr_lt.h"
#include "library/kernel_bindings.h"
#include "library/aliases.h"
#include "library/placeholder.h"

namespace lean {
struct aliases_ext : public environment_extension {
    rb_map<name, list<expr>, name_quick_cmp> m_aliases;
    rb_map<expr, name,       expr_quick_cmp> m_inv_aliases;
    void add_alias(name const & a, expr const & e) {
        auto it = m_aliases.find(a);
        if (it)
            m_aliases.insert(a, list<expr>(e, *it));
        else
            m_aliases.insert(a, list<expr>(e));
        m_inv_aliases.insert(e, a);
    }
};

struct aliases_ext_reg {
    unsigned m_ext_id;
    aliases_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<aliases_ext>()); }
};
static aliases_ext_reg g_ext;
static aliases_ext const & get_extension(environment const & env) {
    return static_cast<aliases_ext const &>(env.get_extension(g_ext.m_ext_id));
}
static environment update(environment const & env, aliases_ext const & ext) {
    return env.update(g_ext.m_ext_id, std::make_shared<aliases_ext>(ext));
}

environment add_alias(environment const & env, name const & a, expr const & e) {
    aliases_ext ext = get_extension(env);
    ext.add_alias(a, e);
    return update(env, ext);
}

environment add_aliases(environment const & env, name const & prefix, name const & new_prefix) {
    aliases_ext ext = get_extension(env);
    env.for_each([&](declaration const & d) {
            if (is_prefix_of(prefix, d.get_name())) {
                name a        = d.get_name().replace_prefix(prefix, new_prefix);
                levels ls     = map2<level>(d.get_univ_params(), [](name const &) { return mk_level_placeholder(); });
                expr c        = mk_constant(d.get_name(), ls);
                ext.add_alias(a, c);
            }
        });
    return update(env, ext);
}

optional<name> is_aliased(environment const & env, expr const & t) {
    auto it = get_extension(env).m_inv_aliases.find(t);
    return it ? optional<name>(*it) : optional<name>();
}

list<expr> get_aliases(environment const & env, name const & n) {
    auto it = get_extension(env).m_aliases.find(n);
    return it ? *it : list<expr>();
}

static int add_alias(lua_State * L) {
    return push_environment(L, add_alias(to_environment(L, 1), to_name_ext(L, 2), to_expr(L, 3)));
}

static int add_aliases(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 2) {
        return push_environment(L, add_aliases(to_environment(L, 1), to_name_ext(L, 2), name()));
    } else {
        return push_environment(L, add_aliases(to_environment(L, 1), to_name_ext(L, 2), to_name_ext(L, 3)));
    }
}

static int is_aliased(lua_State * L) {
    return push_optional_name(L, is_aliased(to_environment(L, 1), to_expr(L, 2)));
}

static int get_aliases(lua_State * L) {
    return push_list_expr(L, get_aliases(to_environment(L, 1), to_name_ext(L, 2)));
}

void open_aliases(lua_State * L) {
    SET_GLOBAL_FUN(add_alias,   "add_alias");
    SET_GLOBAL_FUN(add_aliases, "add_aliases");
    SET_GLOBAL_FUN(is_aliased,  "is_aliased");
    SET_GLOBAL_FUN(get_aliases, "get_aliases");
}
}
