/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include "util/buffer.h"
#include "library/kernel_bindings.h"
#include "library/tactic/goal.h"

namespace lean {
goal::goal(hypotheses const & hs, expr const & c):m_hypotheses(hs), m_conclusion(c) {}

format goal::pp(environment const & env, formatter const & fmt, options const & opts) const {
    unsigned indent  = get_pp_indent(opts);
    bool unicode     = get_pp_unicode(opts);
    format turnstile = unicode ? format("\u22A2") /* ⊢ */ : format("|-");
    buffer<hypothesis> tmp;
    to_buffer(m_hypotheses, tmp);
    bool first = true;
    format r;
    for (auto const & p : tmp) {
        if (first) {
            first = false;
        } else {
            r += compose(comma(), line());
        }
        r += format{format(p.first), space(), colon(), nest(indent, compose(line(), fmt(env, p.second, opts)))};
    }

    r = group(r);
    r += format{line(), turnstile, space(), nest(indent, fmt(env, m_conclusion, opts))};
    return group(r);
}

DECL_UDATA(hypotheses)

static int mk_hypotheses(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 0) {
        return push_hypotheses(L, hypotheses());
    } else if (nargs == 2) {
        return push_hypotheses(L, hypotheses(mk_pair(to_name_ext(L, 1), to_expr(L, 2)), hypotheses()));
    } else if (nargs == 3) {
        return push_hypotheses(L, hypotheses(mk_pair(to_name_ext(L, 1), to_expr(L, 2)), to_hypotheses(L, 3)));
    } else {
        throw exception("hypotheses functions expects 0 (empty list), 2 (name & expr for singleton hypotheses list), or 3 (name & expr & hypotheses list) arguments");
    }
}

static int hypotheses_is_nil(lua_State * L) {
    lua_pushboolean(L, !to_hypotheses(L, 1));
    return 1;
}

static int hypotheses_head(lua_State * L) {
    hypotheses const & hs = to_hypotheses(L, 1);
    if (!hs)
        throw exception("head method expects a non-empty hypotheses list");
    push_name(L, head(hs).first);
    push_expr(L, head(hs).second);
    return 2;
}

static int hypotheses_tail(lua_State * L) {
    hypotheses const & hs = to_hypotheses(L, 1);
    if (!hs)
        throw exception("tail method expects a non-empty hypotheses list");
    push_hypotheses(L, tail(hs));
    return 1;
}

static int hypotheses_next(lua_State * L) {
    hypotheses & hs   = to_hypotheses(L, lua_upvalueindex(1));
    if (hs) {
        push_hypotheses(L, tail(hs));
        lua_replace(L, lua_upvalueindex(1));
        push_name(L, head(hs).first);
        push_expr(L, head(hs).second);
        return 2;
    } else {
        lua_pushnil(L);
        return 1;
    }
}

static int hypotheses_items(lua_State * L) {
    hypotheses & hs = to_hypotheses(L, 1);
    push_hypotheses(L, hs);  // upvalue(1): hypotheses
    lua_pushcclosure(L, &safe_function<hypotheses_next>, 1); // create closure with 1 upvalue
    return 1;
}

static int hypotheses_len(lua_State * L) {
    lua_pushinteger(L, length(to_hypotheses(L, 1)));
    return 1;
}

static const struct luaL_Reg hypotheses_m[] = {
    {"__gc",            hypotheses_gc}, // never throws
    {"__len",           safe_function<hypotheses_len>},
    {"size",            safe_function<hypotheses_len>},
    {"pairs",           safe_function<hypotheses_items>},
    {"is_nil",          safe_function<hypotheses_is_nil>},
    {"empty",           safe_function<hypotheses_is_nil>},
    {"head",            safe_function<hypotheses_head>},
    {"tail",            safe_function<hypotheses_tail>},
    {0, 0}
};

DECL_UDATA(goal)

static int mk_goal(lua_State * L) { return push_goal(L, goal(to_hypotheses(L, 1), to_expr(L, 2))); }
static int goal_hypotheses(lua_State * L) { return push_hypotheses(L, to_goal(L, 1).get_hypotheses()); }
static int goal_conclusion(lua_State * L) { return push_expr(L, to_goal(L, 1).get_conclusion()); }
static int goal_tostring(lua_State * L) {
    std::ostringstream out;
    goal & g = to_goal(L, 1);
    environment env = get_global_environment(L);
    formatter fmt   = get_global_formatter(L);
    options opts    = get_global_options(L);
    out << mk_pair(g.pp(env, fmt, opts), opts);
    lua_pushstring(L, out.str().c_str());
    return 1;
}

static int goal_pp(lua_State * L) {
    int nargs = lua_gettop(L);
    goal & g = to_goal(L, 1);
    if (nargs == 1) {
        return push_format(L, g.pp(get_global_environment(L), get_global_formatter(L), get_global_options(L)));
    } else if (nargs == 2) {
        return push_format(L, g.pp(to_environment(L, 2), get_global_formatter(L), get_global_options(L)));
    } else if (nargs == 3) {
        return push_format(L, g.pp(to_environment(L, 2), to_formatter(L, 3), get_global_options(L)));
    } else {
        return push_format(L, g.pp(to_environment(L, 2), to_formatter(L, 3), to_options(L, 4)));
    }
}

static const struct luaL_Reg goal_m[] = {
    {"__gc",            goal_gc}, // never throws
    {"__tostring",      safe_function<goal_tostring>},
    {"hypotheses",      safe_function<goal_hypotheses>},
    {"hyps",            safe_function<goal_hypotheses>},
    {"conclusion",      safe_function<goal_conclusion>},
    {"pp",              safe_function<goal_pp>},
    {0, 0}
};

void open_goal(lua_State * L) {
    luaL_newmetatable(L, hypotheses_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, hypotheses_m, 0);

    SET_GLOBAL_FUN(hypotheses_pred, "is_hypotheses");
    SET_GLOBAL_FUN(mk_hypotheses, "hypotheses");

    luaL_newmetatable(L, goal_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, goal_m, 0);

    SET_GLOBAL_FUN(goal_pred, "is_goal");
    SET_GLOBAL_FUN(mk_goal, "goal");
}
}
