/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include "util/sstream.h"
#include "util/interrupt.h"
#include "util/sexpr/option_declarations.h"
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
static name * g_proof_state_goal_names = nullptr;

bool get_proof_state_goal_names(options const & opts) {
    return opts.get_bool(*g_proof_state_goal_names, LEAN_PROOF_STATE_GOAL_NAMES);
}

proof_state::proof_state(goals const & gs, substitution const & s, name_generator const & ngen,
                         constraints const & postponed, bool report_failure):
    m_goals(gs), m_subst(s), m_ngen(ngen), m_postponed(postponed),
    m_report_failure(report_failure) {
    if (std::any_of(gs.begin(), gs.end(),
                    [&](goal const & g) { return s.is_assigned(g.get_mvar()); })) {
        m_goals = filter(gs, [&](goal const & g) { return !s.is_assigned(g.get_mvar()); });
    }
}

format proof_state::pp_core(std::function<formatter()> const & mk_fmt, options const & opts) const {
    bool show_goal_names = get_proof_state_goal_names(opts);
    unsigned indent      = get_pp_indent(opts);
    format r;
    bool first = true;

    for (auto const & g : get_goals()) {
        formatter fmt = mk_fmt();
        if (first) first = false; else r += line() + line();
        if (show_goal_names) {
            r += group(format(g.get_name()) + colon() + nest(indent, line() + g.pp(fmt, m_subst)));
        } else {
            r += g.pp(fmt, m_subst);
        }
    }
    if (first) r = format("no goals");
    return r;
}

format proof_state::pp(formatter const & fmt) const {
    return pp_core([&]() { return fmt; }, fmt.get_options());
}

format proof_state::pp(environment const & env, io_state const & ios) const {
    return pp_core([&]() { return ios.get_formatter_factory()(env, ios.get_options()); },
                   ios.get_options());
}

goals map_goals(proof_state const & s, std::function<optional<goal>(goal const & g)> f) {
    return map_filter<goal>(s.get_goals(), [=](goal const & in, goal & out) -> bool {
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

proof_state to_proof_state(expr const & meta, expr const & type, substitution const & subst, name_generator ngen) {
    return proof_state(goals(goal(meta, type)), subst, ngen, constraints());
}

proof_state to_proof_state(expr const & meta, expr const & type, name_generator ngen) {
    return to_proof_state(meta, type, substitution(), ngen);
}

proof_state apply_substitution(proof_state const & s) {
    if (!s.get_goals())
        return s;
    substitution subst = s.get_subst();
    goal  g  = head(s.get_goals());
    goals gs = tail(s.get_goals());
    goal new_g(subst.instantiate_all(g.get_meta()), subst.instantiate_all(g.get_type()));
    return proof_state(s, goals(new_g, gs), subst);
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
    } else if (nargs == 3 && is_proof_state(L, 1)) {
        return push_proof_state(L, proof_state(to_proof_state(L, 1), to_goals(L, 2), to_substitution(L, 3)));
    } else if (nargs == 3) {
        return push_proof_state(L, proof_state(to_goals(L, 1), to_substitution(L, 2), to_name_generator(L, 3),
                                               constraints()));
    } else {
        throw exception("proof_state invalid number of arguments");
    }
}

static name * g_tmp_prefix = nullptr;
static int to_proof_state(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 2)
        return push_proof_state(L, to_proof_state(to_expr(L, 1), to_expr(L, 2), name_generator(*g_tmp_prefix)));
    else
        return push_proof_state(L, to_proof_state(to_expr(L, 1), to_expr(L, 2), to_name_generator(L, 3)));
}

static int proof_state_tostring(lua_State * L) {
    std::ostringstream out;
    proof_state & s = to_proof_state(L, 1);
    options opts    = get_global_options(L);
    out << mk_pair(s.pp(get_global_environment(L), get_io_state(L)), opts);
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
        return push_format(L, s.pp(get_global_environment(L), get_io_state(L)));
    else
        return push_format(L, s.pp(to_environment(L, 1), to_io_state(L, 2)));
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

void initialize_proof_state() {
    g_tmp_prefix = new name(name::mk_internal_unique_name());
    g_proof_state_goal_names = new name{"tactic", "goal_names"};
    register_bool_option(*g_proof_state_goal_names, LEAN_PROOF_STATE_GOAL_NAMES,
                         "(tactic) display goal names when pretty printing proof state");
}

void finalize_proof_state() {
    delete g_tmp_prefix;
    delete g_proof_state_goal_names;
}
}
