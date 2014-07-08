/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <algorithm>
#include "util/rb_map.h"
#include "util/name_generator.h"
#include "util/sstream.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "library/expr_lt.h"
#include "library/kernel_bindings.h"
#include "library/aliases.h"
#include "library/placeholder.h"
#include "library/scoped_ext.h"

namespace lean {
struct aliases_ext;
static aliases_ext const & get_extension(environment const & env);
static environment update(environment const & env, aliases_ext const & ext);

struct aliases_ext : public environment_extension {
    struct state {
        bool                                      m_in_section;
        rb_map<name, list<expr>, name_quick_cmp>  m_aliases;
        rb_map<expr, name,       expr_quick_cmp>  m_inv_aliases;
        rb_map<name, level,      name_quick_cmp>  m_level_aliases;
        rb_map<level, name,      level_quick_cmp> m_inv_level_aliases;
        state():m_in_section(false) {}

        void add_alias(name const & a, expr const & e) {
            auto it = m_aliases.find(a);
            if (it)
                m_aliases.insert(a, list<expr>(e, filter(*it, [&](expr const & t) { return t != e; })));
            else
                m_aliases.insert(a, list<expr>(e));
            m_inv_aliases.insert(e, a);
        }
    };

    state       m_state;
    list<state> m_scopes;

    void add_alias(name const & a, expr const & e) {
        m_state.add_alias(a, e);
    }

    void add_alias(name const & a, level const & l) {
        auto it = m_state.m_level_aliases.find(a);
        if (it)
            throw exception(sstream() << "universe level alias '" << a << "' shadows existing alias");
        m_state.m_level_aliases.insert(a, l);
        m_state.m_inv_level_aliases.insert(l, a);
    }

    list<state> add_decl_alias_core(list<state> const & scopes, name const & a, expr const & e) {
        if (empty(scopes)) {
            return scopes;
        } else {
            state s = head(scopes);
            s.add_alias(a, e);
            if (s.m_in_section) {
                return cons(s, add_decl_alias_core(tail(scopes), a, e));
            } else {
                return cons(s, tail(scopes));
            }
        }
    }

    void add_decl_alias(name const & a, expr const & e) {
        if (m_state.m_in_section) {
            m_scopes = add_decl_alias_core(m_scopes, a, e);
        } else {
            add_alias(a, e);
        }
    }

    void push(bool in_section) {
        m_scopes = list<state>(m_state, m_scopes);
        m_state.m_in_section = in_section;
    }

    void pop() {
        m_state  = head(m_scopes);
        m_scopes = tail(m_scopes);
    }

    static environment using_namespace(environment const & env, io_state const &, name const &) {
        // do nothing, aliases are treated in a special way in the frontend.
        return env;
    }

    static environment push_scope(environment const & env, bool in_section) {
        aliases_ext ext = get_extension(env);
        ext.push(in_section);
        environment new_env = update(env, ext);
        if (!::lean::in_section(new_env))
            new_env = add_aliases(new_env, get_namespace(new_env), name());
        return new_env;
    }

    static environment pop_scope(environment const & env, bool) {
        aliases_ext ext = get_extension(env);
        ext.pop();
        return update(env, ext);
    }
};

static name g_aliases("aliases");

struct aliases_ext_reg {
    unsigned m_ext_id;
    aliases_ext_reg() {
        register_scoped_ext(g_aliases, aliases_ext::using_namespace, aliases_ext::push_scope, aliases_ext::pop_scope);
        m_ext_id = environment::register_extension(std::make_shared<aliases_ext>());
    }
};
static aliases_ext_reg g_ext;
static aliases_ext const & get_extension(environment const & env) {
    return static_cast<aliases_ext const &>(env.get_extension(g_ext.m_ext_id));
}
static environment update(environment const & env, aliases_ext const & ext) {
    return env.update(g_ext.m_ext_id, std::make_shared<aliases_ext>(ext));
}

static void check_atomic(name const & a) {
    if (!a.is_atomic())
        throw exception(sstream() << "invalid alias '" << a << "', aliases must be atomic names");
}

environment add_alias(environment const & env, name const & a, expr const & e) {
    check_atomic(a);
    aliases_ext ext = get_extension(env);
    ext.add_alias(a, e);
    return update(env, ext);
}

environment add_decl_alias(environment const & env, name const & a, expr const & e) {
    check_atomic(a);
    aliases_ext ext = get_extension(env);
    ext.add_decl_alias(a, e);
    return update(env, ext);
}

optional<name> is_aliased(environment const & env, expr const & t) {
    auto it = get_extension(env).m_state.m_inv_aliases.find(t);
    return it ? optional<name>(*it) : optional<name>();
}

list<expr> get_alias_exprs(environment const & env, name const & n) {
    auto it = get_extension(env).m_state.m_aliases.find(n);
    return it ? *it : list<expr>();
}

static void check_no_shadow(environment const & env, name const & a) {
    if (env.is_universe(a))
        throw exception(sstream() << "universe level alias '" << a << "' shadows existing global universe level");
}

environment add_alias(environment const & env, name const & a, level const & l) {
    check_atomic(a);
    check_no_shadow(env, a);
    aliases_ext ext = get_extension(env);
    ext.add_alias(a, l);
    return update(env, ext);
}

optional<name> is_aliased(environment const & env, level const & l) {
    auto it = get_extension(env).m_state.m_inv_level_aliases.find(l);
    return it ? optional<name>(*it) : optional<name>();
}

optional<level> get_alias_level(environment const & env, name const & n) {
    auto it = get_extension(env).m_state.m_level_aliases.find(n);
    return it ? some_level(*it) : optional<level>();
}

// Return true iff \c n is (prefix + ex) for some ex in exceptions
static bool is_exception(name const & n, name const & prefix, unsigned num_exceptions, name const * exceptions) {
    return std::any_of(exceptions, exceptions + num_exceptions, [&](name const & ex) { return (prefix + ex) == n; });
}

environment add_aliases(environment const & env, name const & prefix, name const & new_prefix,
                        unsigned num_exceptions, name const * exceptions) {
    aliases_ext ext = get_extension(env);
    env.for_each_declaration([&](declaration const & d) {
            if (is_prefix_of(prefix, d.get_name()) && !is_exception(d.get_name(), prefix, num_exceptions, exceptions)) {
                name a        = d.get_name().replace_prefix(prefix, new_prefix);
                levels ls     = map2<level>(d.get_univ_params(), [](name const &) { return mk_level_placeholder(); });
                expr c        = mk_constant(d.get_name(), ls);
                ext.add_alias(a, c);
            }
        });
    env.for_each_universe([&](name const & u) {
            if (is_prefix_of(prefix, u) && !is_exception(u, prefix, num_exceptions, exceptions)) {
                name a = u.replace_prefix(prefix, new_prefix);
                if (env.is_universe(a))
                    throw exception(sstream() << "universe level alias '" << a << "' shadows existing global universe level");
                ext.add_alias(a, mk_global_univ(u));
            }
        });
    return update(env, ext);
}

static int add_alias(lua_State * L) {
    if (is_expr(L, 3))
        return push_environment(L, add_alias(to_environment(L, 1), to_name_ext(L, 2), to_expr(L, 3)));
    else
        return push_environment(L, add_alias(to_environment(L, 1), to_name_ext(L, 2), to_level(L, 3)));
}

static int is_aliased(lua_State * L) {
    if (is_expr(L, 2))
        return push_optional_name(L, is_aliased(to_environment(L, 1), to_expr(L, 2)));
    else
        return push_optional_name(L, is_aliased(to_environment(L, 1), to_level(L, 2)));
}

static int get_alias_exprs(lua_State * L) {
    return push_list_expr(L, get_alias_exprs(to_environment(L, 1), to_name_ext(L, 2)));
}

static int get_alias_level(lua_State * L) {
    return push_optional_level(L, get_alias_level(to_environment(L, 1), to_name_ext(L, 2)));
}

static int add_aliases(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 2) {
        return push_environment(L, add_aliases(to_environment(L, 1), to_name_ext(L, 2), name()));
    } else if (nargs == 3) {
        return push_environment(L, add_aliases(to_environment(L, 1), to_name_ext(L, 2), to_name_ext(L, 3)));
    } else {
        buffer<name> exs;
        luaL_checktype(L, 4, LUA_TTABLE);
        int n = objlen(L, 4);
        for (int i = 1; i <= n; i++) {
            lua_rawgeti(L, 4, i);
            exs.push_back(to_name_ext(L, -1));
            lua_pop(L, 1);
        }
        return push_environment(L, add_aliases(to_environment(L, 1), to_name_ext(L, 2), to_name_ext(L, 3),
                                               exs.size(), exs.data()));
    }
}

void open_aliases(lua_State * L) {
    SET_GLOBAL_FUN(add_alias,       "add_alias");
    SET_GLOBAL_FUN(add_aliases,     "add_aliases");
    SET_GLOBAL_FUN(is_aliased,      "is_aliased");
    SET_GLOBAL_FUN(get_alias_exprs, "get_alias_exprs");
    SET_GLOBAL_FUN(get_alias_level, "get_alias_level");
}
}
