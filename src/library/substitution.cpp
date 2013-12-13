/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/replace_fn.h"
#include "kernel/metavar.h"
#include "library/substitution.h"
#include "library/kernel_bindings.h"

namespace lean {
expr find(substitution & s, expr e) {
    while (true) {
        if (is_metavar(e)) {
            expr * it = s.find(metavar_name(e));
            if (it == nullptr)
                return e;
            e = *it;
        } else {
            return e;
        }
    }
}

expr apply(substitution & s, expr const & e, optional<metavar_env> const & menv) {
    auto f = [&](expr const & e, unsigned) -> expr {
        if (is_metavar(e)) {
            expr r = find(s, e);
            if (r != e) {
                if (has_metavar(r)) {
                    r = apply(s, r);
                    s.insert(metavar_name(e), r);
                }
                return apply_local_context(r, metavar_lctx(e), menv);
            } else {
                return e;
            }
        } else {
            return e;
        }
    };
    return replace_fn<decltype(f)>(f)(e);
}

DECL_UDATA(substitution)

static int substitution_size(lua_State * L) {
    lua_pushinteger(L, to_substitution(L, 1).size());
    return 1;
}

static int substitution_empty(lua_State * L) {
    lua_pushboolean(L, to_substitution(L, 1).empty());
    return 1;
}

static int substitution_find(lua_State * L) {
    substitution & s = to_substitution(L, 1);
    expr * it;
    if (is_expr(L, 2)) {
        expr const & e = to_expr(L, 2);
        if (is_metavar(e))
            it = s.find(metavar_name(e));
        else
            throw exception("arg #2 must be a metavariable");
    } else {
        it = s.find(to_name_ext(L, 2));
    }
    if (it)
        push_expr(L, find(s, *it));
    else
        lua_pushnil(L);
    return 1;
}

static int substitution_apply(lua_State * L) {
    return push_expr(L, apply(to_substitution(L, 1), to_expr(L, 2)));
}

static const struct luaL_Reg substitution_m[] = {
    {"__gc",              substitution_gc}, // never throws
    {"__len",             safe_function<substitution_size>},
    {"find",              safe_function<substitution_find>},
    {"empty",             safe_function<substitution_empty>},
    {"size",              safe_function<substitution_size>},
    {"apply",             safe_function<substitution_apply>},
    {0, 0}
};

void open_substitution(lua_State * L) {
    luaL_newmetatable(L, substitution_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, substitution_m, 0);

    SET_GLOBAL_FUN(substitution_pred, "is_substitution");
}
}
