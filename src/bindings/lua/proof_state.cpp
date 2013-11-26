/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <sstream>
#include <lua.hpp>
#include "library/tactic/proof_state.h"
#include "bindings/lua/util.h"
#include "bindings/lua/name.h"
#include "bindings/lua/options.h"
#include "bindings/lua/formatter.h"
#include "bindings/lua/format.h"
#include "bindings/lua/expr.h"
#include "bindings/lua/context.h"
#include "bindings/lua/environment.h"
#include "bindings/lua/metavar_env.h"
#include "bindings/lua/goal.h"
#include "bindings/lua/proof_builder.h"
#include "bindings/lua/cex_builder.h"

namespace lean {
DECL_UDATA(goals)

static int mk_goals(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 0) {
        return push_goals(L, goals());
    } else if (nargs == 2) {
        return push_goals(L, goals(mk_pair(to_name_ext(L, 1), to_goal(L, 2)), goals()));
    } else if (nargs == 3) {
        return push_goals(L, goals(mk_pair(to_name_ext(L, 1), to_goal(L, 2)), to_goals(L, 3)));
    } else {
        throw exception("goals functions expects 0 (empty list), 2 (name & goal for singleton goal list), or 3 (name & goal & goal list) arguments");
    }
}

static int goals_is_nil(lua_State * L) {
    lua_pushboolean(L, !to_goals(L, 1));
    return 1;
}

static int goals_head(lua_State * L) {
    goals const & hs = to_goals(L, 1);
    if (!hs)
        throw exception("head method expects a non-empty goal list");
    push_name(L, head(hs).first);
    push_goal(L, head(hs).second);
    return 2;
}

static int goals_tail(lua_State * L) {
    goals const & hs = to_goals(L, 1);
    if (!hs)
        throw exception("tail method expects a non-empty goal list");
    push_goals(L, tail(hs));
    return 1;
}

static int goals_next(lua_State * L) {
    goals & hs   = to_goals(L, lua_upvalueindex(1));
    if (hs) {
        push_goals(L, tail(hs));
        lua_replace(L, lua_upvalueindex(1));
        push_name(L, head(hs).first);
        push_goal(L, head(hs).second);
        return 2;
    } else {
        lua_pushnil(L);
        return 1;
    }
}

static int goals_items(lua_State * L) {
    goals & hs = to_goals(L, 1);
    push_goals(L, hs);  // upvalue(1): goals
    lua_pushcclosure(L, &safe_function<goals_next>, 1); // create closure with 1 upvalue
    return 1;
}

static int goals_len(lua_State * L) {
    lua_pushinteger(L, length(to_goals(L, 1)));
    return 1;
}

static const struct luaL_Reg goals_m[] = {
    {"__gc",            goals_gc}, // never throws
    {"__len",           safe_function<goals_len>},
    {"size",            safe_function<goals_len>},
    {"pairs",           safe_function<goals_items>},
    {"is_nil",          safe_function<goals_is_nil>},
    {"empty",           safe_function<goals_is_nil>},
    {"head",            safe_function<goals_head>},
    {"tail",            safe_function<goals_tail>},
    {0, 0}
};

DECL_UDATA(proof_state)

static int mk_proof_state(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 0) {
        return push_proof_state(L, proof_state());
    } else if (nargs == 4) {
        return push_proof_state(L, proof_state(to_goals(L, 1), to_metavar_env(L, 2), to_proof_builder(L, 3), to_cex_builder(L, 4)));
    } else if (nargs == 3) {
        return push_proof_state(L, proof_state(to_proof_state(L, 1), to_goals(L, 2), to_proof_builder(L, 3)));
    } else {
        throw exception("proof_state expectes 0, 3, or 4 arguments");
    }
}

static int to_proof_state(lua_State * L) {
    return push_proof_state(L, to_proof_state(to_environment(L, 1), to_context(L, 2), to_expr(L, 3)));
}

static int proof_state_tostring(lua_State * L) {
    std::ostringstream out;
    proof_state & s = to_proof_state(L, 1);
    formatter fmt = get_global_formatter(L);
    options opts  = get_global_options(L);
    out << mk_pair(s.pp(fmt, opts), opts);
    lua_pushstring(L, out.str().c_str());
    return 1;
}

static int proof_state_get_precision(lua_State * L) {
    lua_pushinteger(L, static_cast<int>(to_proof_state(L, 1).get_precision()));
    return 1;
}

static int proof_state_get_goals(lua_State * L) {
    return push_goals(L, to_proof_state(L, 1).get_goals());
}

static int proof_state_get_menv(lua_State * L) {
    return push_metavar_env(L, to_proof_state(L, 1).get_menv());
}

static int proof_state_get_proof_builder(lua_State * L) {
    return push_proof_builder(L, to_proof_state(L, 1).get_proof_builder());
}

static int proof_state_get_cex_builder(lua_State * L) {
    return push_cex_builder(L, to_proof_state(L, 1).get_cex_builder());
}

static int proof_state_is_proof_final_state(lua_State * L) {
    lua_pushboolean(L, to_proof_state(L, 1).is_proof_final_state());
    return 1;
}

static int proof_state_is_cex_final_state(lua_State * L) {
    lua_pushboolean(L, to_proof_state(L, 1).is_cex_final_state());
    return 1;
}

static int proof_state_pp(lua_State * L) {
    int nargs = lua_gettop(L);
    proof_state & s = to_proof_state(L, 1);
    if (nargs == 1) {
        return push_format(L, s.pp(get_global_formatter(L), get_global_options(L)));
    } else if (nargs == 2) {
        if (is_formatter(L, 2))
            return push_format(L, s.pp(to_formatter(L, 2), get_global_options(L)));
        else
            return push_format(L, s.pp(get_global_formatter(L), to_options(L, 2)));
    } else {
        return push_format(L, s.pp(to_formatter(L, 2), to_options(L, 3)));
    }
}

static const struct luaL_Reg proof_state_m[] = {
    {"__gc",                 proof_state_gc}, // never throws
    {"__tostring",           safe_function<proof_state_tostring>},
    {"pp",                   safe_function<proof_state_pp>},
    {"get_precision",        safe_function<proof_state_get_precision>},
    {"get_goals",            safe_function<proof_state_get_goals>},
    {"get_menv",             safe_function<proof_state_get_menv>},
    {"get_proof_builder",    safe_function<proof_state_get_proof_builder>},
    {"get_cex_builder",      safe_function<proof_state_get_cex_builder>},
    {"precision",            safe_function<proof_state_get_precision>},
    {"goals",                safe_function<proof_state_get_goals>},
    {"menv",                 safe_function<proof_state_get_menv>},
    {"proof_builder",        safe_function<proof_state_get_proof_builder>},
    {"cex_builder",          safe_function<proof_state_get_cex_builder>},
    {"is_proof_final_state", safe_function<proof_state_is_proof_final_state>},
    {"is_cex_final_state",   safe_function<proof_state_is_cex_final_state>},
    {0, 0}
};

void open_proof_state(lua_State * L) {
    luaL_newmetatable(L, goals_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, goals_m, 0);

    SET_GLOBAL_FUN(goals_pred, "is_goals");
    SET_GLOBAL_FUN(mk_goals, "goals");

    luaL_newmetatable(L, proof_state_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, proof_state_m, 0);

    SET_GLOBAL_FUN(proof_state_pred, "is_proof_state");
    SET_GLOBAL_FUN(mk_proof_state, "proof_state");
    SET_GLOBAL_FUN(to_proof_state, "to_proof_state");

    lua_newtable(L);
    SET_ENUM("Precise",   precision::Precise);
    SET_ENUM("Over",      precision::Over);
    SET_ENUM("Under",     precision::Under);
    SET_ENUM("UnderOver", precision::UnderOver);
    lua_setglobal(L, "precision");
}
}
