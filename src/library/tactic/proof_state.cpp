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
static name g_proof_state_minimize_contextual {"tactic", "mimimize_contextual"};
RegisterBoolOption(g_proof_state_goal_names, LEAN_PROOF_STATE_GOAL_NAMES, "(tactic) display goal names when pretty printing proof state");
RegisterBoolOption(g_proof_state_minimize_contextual, LEAN_PROOF_STATE_MINIMIZE_CONTEXTUAL,
                   "(tactic) only hypotheses, that are not propositions, are marked as 'contextual'");
bool get_proof_state_goal_names(options const & opts) { return opts.get_bool(g_proof_state_goal_names, LEAN_PROOF_STATE_GOAL_NAMES); }
bool get_proof_state_minimize_contextual(options const & opts) {
    return opts.get_bool(g_proof_state_minimize_contextual, LEAN_PROOF_STATE_MINIMIZE_CONTEXTUAL);
}

optional<name> get_ith_goal_name(goals const & gs, unsigned i) {
    unsigned j = 1;
    for (auto const & p : gs) {
        if (i == j) return some(p.first);
        j++;
    }
    return optional<name>();
}

precision mk_union(precision p1, precision p2) {
    if (p1 == p2) return p1;
    else if (p1 == precision::Precise) return p2;
    else if (p2 == precision::Precise) return p1;
    else return precision::UnderOver;
}

bool trust_proof(precision p) { return p == precision::Precise || p == precision::Over; }
bool trust_cex(precision p) { return p == precision::Precise || p == precision::Under; }

format proof_state::pp(environment const & env, formatter const & fmt, options const & opts) const {
    bool show_goal_names = get_proof_state_goal_names(opts);
    unsigned indent      = get_pp_indent(opts);
    format r;
    bool first = true;
    for (auto const & p : get_goals()) {
        if (first) first = false; else r += line();
        if (show_goal_names) {
            r += group(format{format(p.first), colon(), nest(indent, compose(line(), p.second.pp(env, fmt, opts)))});
        } else {
            r += p.second.pp(env, fmt, opts);
        }
    }
    if (first) r = format("no goals");
    return r;
}

goals map_goals(proof_state const & s, std::function<optional<goal>(name const & gn, goal const & g)> f) {
    return map_filter(s.get_goals(), [=](std::pair<name, goal> const & in, std::pair<name, goal> & out) -> bool {
            check_interrupted();
            optional<goal> new_goal = f(in.first, in.second);
            if (new_goal) {
                out.first  = in.first;
                out.second = *new_goal;
                return true;
            } else {
                return false;
            }
        });
}

bool proof_state::is_proof_final_state() const {
    return empty(get_goals()) && trust_proof(get_precision());
}

void proof_state::get_goal_names(name_set & r) const {
    for (auto const & p : get_goals())
        r.insert(p.first);
}

static name g_main("main");
proof_builder mk_init_proof_builder(list<expr> const & locals) {
    return proof_builder([=](proof_map const & m, substitution const &) -> expr {
            expr r = find(m, g_main);
            for (expr const & l : locals)
                r = Fun(l, r);
            return r;
        });
}

static proof_state to_proof_state(environment const * env, expr const & mvar, name_generator ngen) {
    if (!is_metavar(mvar))
        throw exception("invalid 'to_proof_state', argument is not a metavariable");
    optional<type_checker> tc;
    if (env)
        tc.emplace(*env, ngen.mk_child());
    expr t = mlocal_type(mvar);
    list<expr> init_ls;
    hypotheses hs;
    while (is_pi(t)) {
        expr l  = mk_local(ngen.next(), binding_name(t), binding_domain(t));
        bool c  = true;
        if (tc)
            c   = !tc->is_prop(binding_domain(t));
        hs      = hypotheses(hypothesis(l, c), hs);
        t       = instantiate(binding_body(t), l);
        init_ls = list<expr>(l, init_ls);
    }
    goals gs(mk_pair(g_main, goal(hs, t)));
    return proof_state(gs, mk_init_proof_builder(init_ls), mk_cex_builder_for(g_main), ngen, init_ls);
}

static name g_tmp_prefix = name::mk_internal_unique_name();
proof_state to_proof_state(expr const & mvar, name_generator const & ngen) { return to_proof_state(nullptr, mvar, ngen); }
proof_state to_proof_state(expr const & mvar) { return to_proof_state(mvar, name_generator(g_tmp_prefix)); }
proof_state to_proof_state(environment const & env, expr const & mvar, name_generator const & ngen, options const & opts) {
    bool min_ctx = get_proof_state_minimize_contextual(opts) && env.impredicative();
    if (!min_ctx)
        return to_proof_state(mvar, ngen);
    else
        return to_proof_state(&env, mvar, ngen);
}
proof_state to_proof_state(environment const & env, expr const & meta, options const & opts) {
    return to_proof_state(env, meta, name_generator(g_tmp_prefix), opts);
}

io_state_stream const & operator<<(io_state_stream const & out, proof_state const & s) {
    options const & opts = out.get_options();
    out.get_stream() << mk_pair(s.pp(out.get_environment(), out.get_formatter(), opts), opts);
    return out;
}

optional<expr> to_proof(proof_state const & s) {
    if (s.is_proof_final_state()) {
        try {
            substitution a;
            proof_map  m;
            return some_expr(s.get_pb()(m, a));
        } catch (...) {}
    }
    return none_expr();
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
        lua_rawgeti(L, i, 1);
        lua_rawgeti(L, i, 2);
        if (!(lua_isstring(L, -2) || is_name(L, -2)) || !is_goal(L, -1))
            throw exception(sstream() << "arg #" << i << " must be a pair: name, goal");
        r = goals(mk_pair(to_name_ext(L, -2), to_goal(L, -1)), r);
        lua_pop(L, 2);
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
    if (nargs == 2) {
        return push_proof_state(L, proof_state(to_proof_state(L, 1), to_goals(L, 2)));
    } else if (nargs == 3) {
        return push_proof_state(L, proof_state(to_proof_state(L, 1), to_goals(L, 2), to_proof_builder(L, 3)));
    } else if (nargs == 4) {
        return push_proof_state(L, proof_state(to_proof_state(L, 1), to_goals(L, 2), to_proof_builder(L, 3), to_name_generator(L, 4)));
    } else {
        throw exception("proof_state invalid number of arguments");
    }
}

static int to_proof_state(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 1)
        return push_proof_state(L, to_proof_state(to_expr(L, 1)));
    else if (nargs == 2 && is_expr(L, 1))
        return push_proof_state(L, to_proof_state(to_expr(L, 1), to_name_generator(L, 2)));
    else if (nargs == 2)
        return push_proof_state(L, to_proof_state(to_environment(L, 1), to_expr(L, 2)));
    else if (nargs == 3)
        return push_proof_state(L, to_proof_state(to_environment(L, 1), to_expr(L, 2), to_options(L, 3)));
    else
        return push_proof_state(L, to_proof_state(to_environment(L, 1), to_expr(L, 2), to_name_generator(L, 3), to_options(L, 4)));
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

static int proof_state_get_precision(lua_State * L) { return push_integer(L, static_cast<int>(to_proof_state(L, 1).get_precision())); }
static int proof_state_get_goals(lua_State * L) { return push_goals(L, to_proof_state(L, 1).get_goals()); }
static int proof_state_apply_proof_builder(lua_State * L) {
    return push_expr(L, to_proof_state(L, 1).get_pb()(to_proof_map(L, 2), to_substitution(L, 3)));
}
static int proof_state_apply_cex_builder(lua_State * L) {
    optional<counterexample> cex;
    if (!lua_isnil(L, 3))
        cex = to_environment(L, 3);
    return push_environment(L, to_proof_state(L, 1).get_cb()(to_name_ext(L, 2), cex, to_substitution(L, 4)));
}
static int proof_state_is_proof_final_state(lua_State * L) { return push_boolean(L, to_proof_state(L, 1).is_proof_final_state()); }
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

static int to_proof(lua_State * L) { return push_optional_expr(L, to_proof(to_proof_state(L, 1))); }

static const struct luaL_Reg proof_state_m[] = {
    {"__gc",                 proof_state_gc}, // never throws
    {"__tostring",           safe_function<proof_state_tostring>},
    {"pp",                   safe_function<proof_state_pp>},
    {"get_precision",        safe_function<proof_state_get_precision>},
    {"get_goals",            safe_function<proof_state_get_goals>},
    {"pb",                   safe_function<proof_state_apply_proof_builder>},
    {"cb",                   safe_function<proof_state_apply_cex_builder>},
    {"precision",            safe_function<proof_state_get_precision>},
    {"goals",                safe_function<proof_state_get_goals>},
    {"is_proof_final_state", safe_function<proof_state_is_proof_final_state>},
    {"to_proof",             safe_function<to_proof>},
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
