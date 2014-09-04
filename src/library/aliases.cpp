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
#include "library/protected.h"

namespace lean {
struct aliases_ext;
static aliases_ext const & get_extension(environment const & env);
static environment update(environment const & env, aliases_ext const & ext);

struct aliases_ext : public environment_extension {
    struct state {
        bool                                      m_in_section_or_context;
        rb_map<name, list<name>, name_quick_cmp>  m_aliases;
        rb_map<name, name,       name_quick_cmp>  m_inv_aliases;
        rb_map<name, name,       name_quick_cmp>  m_level_aliases;
        rb_map<name, name,       name_quick_cmp>  m_inv_level_aliases;
        state():m_in_section_or_context(false) {}

        void add_expr_alias(name const & a, name const & e) {
            auto it = m_aliases.find(a);
            if (it)
                m_aliases.insert(a, cons(e, filter(*it, [&](name const & t) { return t != e; })));
            else
                m_aliases.insert(a, to_list(e));
            m_inv_aliases.insert(e, a);
        }
    };

    state       m_state;
    list<state> m_scopes;

    void add_expr_alias(name const & a, name const & e) {
        m_state.add_expr_alias(a, e);
    }

    void add_level_alias(name const & a, name const & l) {
        auto it = m_state.m_level_aliases.find(a);
        if (it)
            throw exception(sstream() << "universe level alias '" << a << "' shadows existing alias");
        m_state.m_level_aliases.insert(a, l);
        m_state.m_inv_level_aliases.insert(l, a);
    }

    list<state> add_expr_alias_rec_core(list<state> const & scopes, name const & a, name const & e) {
        if (empty(scopes)) {
            return scopes;
        } else {
            state s = head(scopes);
            s.add_expr_alias(a, e);
            if (s.m_in_section_or_context) {
                return cons(s, add_expr_alias_rec_core(tail(scopes), a, e));
            } else {
                return cons(s, tail(scopes));
            }
        }
    }

    void add_expr_alias_rec(name const & a, name const & e) {
        if (m_state.m_in_section_or_context) {
            m_scopes = add_expr_alias_rec_core(m_scopes, a, e);
        } else {
            add_expr_alias(a, e);
        }
    }

    void push(bool in_section_or_context) {
        m_scopes = cons(m_state, m_scopes);
        m_state.m_in_section_or_context = in_section_or_context;
    }

    void pop() {
        m_state  = head(m_scopes);
        m_scopes = tail(m_scopes);
    }

    void for_each_expr_alias(std::function<void(name const &, list<name> const &)> const & fn) {
        m_state.m_aliases.for_each(fn);
    }

    static environment using_namespace(environment const & env, io_state const &, name const &) {
        // do nothing, aliases are treated in a special way in the frontend.
        return env;
    }

    static environment push_scope(environment const & env, scope_kind k) {
        aliases_ext ext = get_extension(env);
        ext.push(k != scope_kind::Namespace);
        environment new_env = update(env, ext);
        if (!::lean::in_section_or_context(new_env))
            new_env = add_aliases(new_env, get_namespace(new_env), name());
        return new_env;
    }

    static environment pop_scope(environment const & env, scope_kind) {
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

environment add_expr_alias(environment const & env, name const & a, name const & e) {
    aliases_ext ext = get_extension(env);
    ext.add_expr_alias(a, e);
    return update(env, ext);
}

environment add_expr_alias_rec(environment const & env, name const & a, name const & e) {
    aliases_ext ext = get_extension(env);
    ext.add_expr_alias_rec(a, e);
    return update(env, ext);
}

optional<name> is_expr_aliased(environment const & env, name const & t) {
    auto it = get_extension(env).m_state.m_inv_aliases.find(t);
    return it ? optional<name>(*it) : optional<name>();
}

list<name> get_expr_aliases(environment const & env, name const & n) {
    return ptr_to_list(get_extension(env).m_state.m_aliases.find(n));
}

static void check_no_shadow(environment const & env, name const & a) {
    if (env.is_universe(a))
        throw exception(sstream() << "universe level alias '" << a << "' shadows existing global universe level");
}

environment add_level_alias(environment const & env, name const & a, name const & l) {
    check_no_shadow(env, a);
    aliases_ext ext = get_extension(env);
    ext.add_level_alias(a, l);
    return update(env, ext);
}

optional<name> is_level_aliased(environment const & env, name const & l) {
    auto it = get_extension(env).m_state.m_inv_level_aliases.find(l);
    return it ? optional<name>(*it) : optional<name>();
}

optional<name> get_level_alias(environment const & env, name const & n) {
    auto it = get_extension(env).m_state.m_level_aliases.find(n);
    return it ? optional<name>(*it) : optional<name>();
}

// Return true iff \c n is (prefix + ex) for some ex in exceptions
static bool is_exception(name const & n, name const & prefix, unsigned num_exceptions, name const * exceptions) {
    return std::any_of(exceptions, exceptions + num_exceptions, [&](name const & ex) { return (prefix + ex) == n; });
}

environment add_aliases(environment const & env, name const & prefix, name const & new_prefix,
                        unsigned num_exceptions, name const * exceptions) {
    aliases_ext ext = get_extension(env);
    env.for_each_declaration([&](declaration const & d) {
            if (!is_protected(env, d.get_name()) &&
                is_prefix_of(prefix, d.get_name()) && !is_exception(d.get_name(), prefix, num_exceptions, exceptions)) {
                name a        = d.get_name().replace_prefix(prefix, new_prefix);
                if (!a.is_anonymous())
                    ext.add_expr_alias(a, d.get_name());
            }
        });
    env.for_each_universe([&](name const & u) {
            if (!is_protected(env, u) &&
                is_prefix_of(prefix, u) && !is_exception(u, prefix, num_exceptions, exceptions)) {
                name a = u.replace_prefix(prefix, new_prefix);
                if (env.is_universe(a))
                    throw exception(sstream() << "universe level alias '" << a << "' shadows existing global universe level");
                if (!a.is_anonymous())
                    ext.add_level_alias(a, u);
            }
        });
    return update(env, ext);
}

void for_each_expr_alias(environment const & env, std::function<void(name const &, list<name> const &)> const & fn) {
    aliases_ext ext = get_extension(env);
    ext.for_each_expr_alias(fn);
}

static int add_expr_alias(lua_State * L) {
    return push_environment(L, add_expr_alias(to_environment(L, 1), to_name_ext(L, 2), to_name_ext(L, 3)));
}
static int add_level_alias(lua_State * L) {
    return push_environment(L, add_level_alias(to_environment(L, 1), to_name_ext(L, 2), to_name_ext(L, 3)));
}

static int is_expr_aliased(lua_State * L) {
    return push_optional_name(L, is_expr_aliased(to_environment(L, 1), to_name_ext(L, 2)));
}
static int is_level_aliased(lua_State * L) {
    return push_optional_name(L, is_level_aliased(to_environment(L, 1), to_name_ext(L, 2)));
}

static int get_expr_aliases(lua_State * L) {
    return push_list_name(L, get_expr_aliases(to_environment(L, 1), to_name_ext(L, 2)));
}
static int get_level_alias(lua_State * L) {
    return push_optional_name(L, get_level_alias(to_environment(L, 1), to_name_ext(L, 2)));
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
    SET_GLOBAL_FUN(add_expr_alias,   "add_expr_alias");
    SET_GLOBAL_FUN(add_level_alias,  "add_level_alias");
    SET_GLOBAL_FUN(is_expr_aliased,  "is_expr_aliased");
    SET_GLOBAL_FUN(is_level_aliased, "is_level_aliased");
    SET_GLOBAL_FUN(get_expr_aliases, "get_expr_aliases");
    SET_GLOBAL_FUN(get_level_alias,  "get_level_alias");
    SET_GLOBAL_FUN(add_aliases,      "add_aliases");
}
}
