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
#include "library/io_state_stream.h"
#include "library/placeholder.h"

namespace lean {
struct aliases_ext : public environment_extension {
    rb_map<name, expr, name_quick_cmp> m_aliases;
    rb_map<expr, name, expr_quick_cmp> m_inv_aliases;
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

static void check_name(environment const & env, name const & a, io_state const & ios) {
    if (get_extension(env).m_aliases.contains(a))
        diagnostic(env, ios) << "alias '" << a << "' shadows existing alias\n";
    if (env.find(a))
        diagnostic(env, ios) << "alias '" << a << "' shadows existing declaration\n";
}

environment add_alias(environment const & env, name const & a, expr const & e, io_state const & ios) {
    check_name(env, a, ios);
    aliases_ext ext = get_extension(env);
    ext.m_aliases.insert(a, e);
    ext.m_inv_aliases.insert(e, a);
    return update(env, ext);
}

environment add_aliases(environment const & env, name const & prefix, name const & new_prefix, io_state const & ios) {
    return add_aliases(env, prefix, new_prefix, 0, nullptr, ios);
}

static optional<expr> get_fix_param(unsigned num_fix_params, std::pair<name, expr> const * fix_params, name const & n) {
    for (unsigned i = 0; i < num_fix_params; i++) {
        if (fix_params[i].first == n)
            return some_expr(fix_params[i].second);
    }
    return none_expr();
}

static name g_local_name = name::mk_internal_unique_name();

environment add_aliases(environment const & env, name const & prefix, name const & new_prefix,
                        unsigned num_fix_params, std::pair<name, expr> const * fix_params, io_state const & ios) {
    aliases_ext ext = get_extension(env);
    env.for_each([&](declaration const & d) {
            if (is_prefix_of(prefix, d.get_name())) {
                name a        = d.get_name().replace_prefix(prefix, new_prefix);
                check_name(env, a, ios);
                levels ls     = map2<level>(d.get_univ_params(), [](name const &) { return mk_level_placeholder(); });
                expr c        = mk_constant(d.get_name(), ls);
                if (num_fix_params > 0) {
                    expr t = d.get_type();
                    buffer<expr>        locals;
                    buffer<binder_info> infos;
                    buffer<expr>        args;
                    name_generator      ngen(g_local_name);
                    bool found_free = false;
                    bool found_fix  = false;
                    bool easy       = true;
                    while (is_pi(t)) {
                        if (auto p = get_fix_param(num_fix_params, fix_params, binding_name(t))) {
                            args.push_back(*p);
                            if (found_free)
                                easy = false;
                            found_fix = true;
                            t = instantiate(binding_body(t), *p);
                        } else {
                            found_free = true;
                            expr l = mk_local(ngen.next(), binding_name(t), binding_domain(t));
                            infos.push_back(binding_info(t));
                            locals.push_back(l);
                            args.push_back(l);
                            t = instantiate(binding_body(t), l);
                        }
                    }
                    if (found_fix) {
                        if (easy) {
                            args.shrink(args.size() - locals.size());
                            c = mk_app(c, args);
                        } else {
                            c = mk_app(c, args);
                            unsigned i = locals.size();
                            while (i > 0) {
                                --i;
                                c = Fun(locals[i], c, infos[i]);
                            }
                        }
                    }
                }
                ext.m_aliases.insert(a, c);
                ext.m_inv_aliases.insert(c, a);
            }
        });
    return update(env, ext);
}

optional<name> is_aliased(environment const & env, expr const & t) {
    auto it = get_extension(env).m_inv_aliases.find(t);
    return it ? optional<name>(*it) : optional<name>();
}

optional<expr> get_alias(environment const & env, name const & n) {
    auto it = get_extension(env).m_aliases.find(n);
    return it ? optional<expr>(*it) : optional<expr>();
}

static int add_alias(lua_State * L) {
    return push_environment(L, add_alias(to_environment(L, 1), to_name_ext(L, 2), to_expr(L, 3), to_io_state_ext(L, 4)));
}

static int add_aliases(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 2) {
        return push_environment(L, add_aliases(to_environment(L, 1), to_name_ext(L, 2), name(), get_io_state(L)));
    } else if (nargs == 3) {
        return push_environment(L, add_aliases(to_environment(L, 1), to_name_ext(L, 2), to_name_ext(L, 3), get_io_state(L)));
    } else if (nargs == 4 && is_io_state(L, 4)) {
        return push_environment(L, add_aliases(to_environment(L, 1), to_name_ext(L, 2), to_name_ext(L, 3), to_io_state(L, 4)));
    } else {
        buffer<std::pair<name, expr>> fix_params;
        luaL_checktype(L, 4, LUA_TTABLE);
        int sz = objlen(L, 4);
        for (int i = 1; i <= sz; i++) {
            lua_rawgeti(L, 4, i);
            luaL_checktype(L, -1, LUA_TTABLE);
            lua_rawgeti(L, -1, 1);
            name n = to_name_ext(L, -1);
            lua_pop(L, 1);
            lua_rawgeti(L, -1, 2);
            expr e = to_expr(L, -1);
            lua_pop(L, 2);
            fix_params.emplace_back(n, e);
        }
        return push_environment(L, add_aliases(to_environment(L, 1), to_name_ext(L, 2), to_name_ext(L, 3),
                                               fix_params.size(), fix_params.data(), to_io_state_ext(L, 5)));
    }
}

static int is_aliased(lua_State * L) {
    return push_optional_name(L, is_aliased(to_environment(L, 1), to_expr(L, 2)));
}

static int get_alias(lua_State * L) {
    return push_optional_expr(L, get_alias(to_environment(L, 1), to_name_ext(L, 2)));
}

void open_aliases(lua_State * L) {
    SET_GLOBAL_FUN(add_alias,   "add_alias");
    SET_GLOBAL_FUN(add_aliases, "add_aliases");
    SET_GLOBAL_FUN(is_aliased,  "is_aliased");
    SET_GLOBAL_FUN(get_alias,   "get_alias");
}
}
