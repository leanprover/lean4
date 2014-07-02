/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include "util/sstream.h"
#include "util/interrupt.h"
#include "kernel/type_checker.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "library/io_state_stream.h"
#include "library/kernel_bindings.h"
#include "library/tactic/proof_state.h"

#ifndef LEAN_PROOF_STATE_GOAL_NAMES
#define LEAN_PROOF_STATE_GOAL_NAMES false
#endif

#ifndef LEAN_PROOF_STATE_MINIMIZE_CONTEXTUAL
#define LEAN_PROOF_STATE_MINIMIZE_CONTEXTUAL true
#endif

namespace lean {
static name g_proof_state_goal_names          {"tactic", "goal_names"};
RegisterBoolOption(g_proof_state_goal_names, LEAN_PROOF_STATE_GOAL_NAMES, "(tactic) display goal names when pretty printing proof state");
bool get_proof_state_goal_names(options const & opts) { return opts.get_bool(g_proof_state_goal_names, LEAN_PROOF_STATE_GOAL_NAMES); }

format proof_state::pp(environment const & env, formatter const & fmt, options const & opts) const {
    bool show_goal_names = get_proof_state_goal_names(opts);
    unsigned indent      = get_pp_indent(opts);
    format r;
    bool first = true;
    for (auto const & g : get_goals()) {
        if (first) first = false; else r += line();
        if (show_goal_names) {
            r += group(format{format(g.get_name()), colon(), nest(indent, compose(line(), g.pp(env, fmt, opts)))});
        } else {
            r += g.pp(env, fmt, opts);
        }
    }
    if (first) r = format("no goals");
    return r;
}

goals map_goals(proof_state const & s, std::function<optional<goal>(goal const & g)> f) {
    return map_filter(s.get_goals(), [=](goal const & in, goal & out) -> bool {
            check_interrupted();
            optional<goal> new_goal = f(in);
            if (new_goal) {
                out = *new_goal;
                return true;
            } else {
                return false;
            }
        });
}

io_state_stream const & operator<<(io_state_stream const & out, proof_state const & s) {
    options const & opts = out.get_options();
    out.get_stream() << mk_pair(s.pp(out.get_environment(), out.get_formatter(), opts), opts);
    return out;
}

proof_state to_proof_state(expr const & meta, expr const & type, name_generator ngen) {
    return proof_state(goals(goal(meta, type)), substitution(), ngen);
}

DECL_UDATA(goals)

static int mk_goals(lua_State * L) {
    int i = lua_gettop(L);
    goals r;
    if (i > 0 && is_goals(L, i)) {
        r = to_goals(L, i);
        i--;
    }
    while (i > 0) {
        r = goals(to_goal(L, i), r);
        i--;
    }
    return push_goals(L, r);
}

static int goals_is_nil(lua_State * L) {
    lua_pushboolean(L, !to_goals(L, 1));
    return 1;
}

static int goals_head(lua_State * L) {
    goals const & hs = to_goals(L, 1);
    if (!hs)
        throw exception("head method expects a non-empty goal list");
    return push_goal(L, head(hs));
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
        return push_goal(L, head(hs));
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
    return push_integer(L, length(to_goals(L, 1)));
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
    if (nargs == 2) {
        return push_proof_state(L, proof_state(to_proof_state(L, 1), to_goals(L, 2)));
    } else if (nargs == 3) {
        return push_proof_state(L, proof_state(to_proof_state(L, 1), to_goals(L, 2), to_substitution(L, 3)));
    } else if (nargs == 4) {
        return push_proof_state(L, proof_state(to_goals(L, 1), to_substitution(L, 2), to_name_generator(L, 3)));
    } else {
        throw exception("proof_state invalid number of arguments");
    }
}

static name g_tmp_prefix = name::mk_internal_unique_name();
static int to_proof_state(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 2)
        return push_proof_state(L, to_proof_state(to_expr(L, 1), to_expr(L, 2), name_generator(g_tmp_prefix)));
    else
        return push_proof_state(L, to_proof_state(to_expr(L, 1), to_expr(L, 2), to_name_generator(L, 3)));
}

static int proof_state_tostring(lua_State * L) {
    std::ostringstream out;
    proof_state & s = to_proof_state(L, 1);
    environment env = get_global_environment(L);
    formatter fmt   = get_global_formatter(L);
    options opts    = get_global_options(L);
    out << mk_pair(s.pp(env, fmt, opts), opts);
    lua_pushstring(L, out.str().c_str());
    return 1;
}

static int proof_state_get_goals(lua_State * L) { return push_goals(L, to_proof_state(L, 1).get_goals()); }
static int proof_state_get_ngen(lua_State * L) { return push_name_generator(L, to_proof_state(L, 1).get_ngen()); }
static int proof_state_get_subst(lua_State * L) { return push_substitution(L, to_proof_state(L, 1).get_subst()); }
static int proof_state_is_final_state(lua_State * L) { return push_boolean(L, to_proof_state(L, 1).is_final_state()); }
static int proof_state_pp(lua_State * L) {
    int nargs = lua_gettop(L);
    proof_state & s = to_proof_state(L, 1);
    if (nargs == 1)
        return push_format(L, s.pp(get_global_environment(L), get_global_formatter(L), get_global_options(L)));
    else if (nargs == 2)
        return push_format(L, s.pp(to_environment(L, 2), get_global_formatter(L), get_global_options(L)));
    else if (nargs == 3)
        return push_format(L, s.pp(to_environment(L, 2), to_formatter(L, 3), get_global_options(L)));
    else
        return push_format(L, s.pp(to_environment(L, 2), to_formatter(L, 3), to_options(L, 4)));
}

static const struct luaL_Reg proof_state_m[] = {
    {"__gc",                 proof_state_gc}, // never throws
    {"__tostring",           safe_function<proof_state_tostring>},
    {"pp",                   safe_function<proof_state_pp>},
    {"goals",                safe_function<proof_state_get_goals>},
    {"subst",                safe_function<proof_state_get_subst>},
    {"ngen",                 safe_function<proof_state_get_ngen>},
    {"is_final_state",       safe_function<proof_state_is_final_state>},
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
    SET_GLOBAL_FUN(mk_proof_state,   "proof_state");
    SET_GLOBAL_FUN(to_proof_state,   "to_proof_state");
}
}
