/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include "util/buffer.h"
#include "util/sstream.h"
#include "kernel/replace_fn.h"
#include "kernel/for_each_fn.h"
#include "kernel/abstract.h"
#include "library/kernel_bindings.h"
#include "library/tactic/goal.h"

namespace lean {
goal::goal(hypotheses const & hs, expr const & c):m_hypotheses(hs), m_conclusion(c) {}

static bool is_used_pp_name(hypothesis const * begin, hypothesis const * end, name const & n) {
    return std::any_of(begin, end, [&](hypothesis const & h) { return local_pp_name(h.first) == n; });
}

static expr pick_unused_pp_name(hypothesis const * begin, hypothesis const * end, expr const & l) {
    expr r = l;
    unsigned i = 1;
    while (is_used_pp_name(begin, end, local_pp_name(r))) {
        name new_pp_name = local_pp_name(l);
        new_pp_name = new_pp_name.append_after(i);
        r = mk_local(new_pp_name, mlocal_type(l));
        i++;
    }
    return r;
}

static void update_local(expr & t, expr const & old_local, expr const & new_local) {
    t = replace(t, [&](expr const & e, unsigned) {
            if (!has_local(e))
                return some_expr(e);
            if (e == old_local)
                return some_expr(new_local);
            return none_expr();
        });
}

static void update_local(hypothesis * begin, hypothesis * end, expr & conclusion,
                         expr const & old_local, expr const & new_local) {
    for (auto it = begin; it != end; ++it)
        update_local(it->first, old_local, new_local);
    update_local(conclusion, old_local, new_local);
}

format goal::pp(environment const & env, formatter const & fmt, options const & opts) const {
    unsigned indent  = get_pp_indent(opts);
    bool unicode     = get_pp_unicode(opts);
    format turnstile = unicode ? format("\u22A2") /* ⊢ */ : format("|-");
    expr conclusion  = m_conclusion;
    buffer<hypothesis> tmp;
    to_buffer(m_hypotheses, tmp);
    std::reverse(tmp.begin(), tmp.end());
    bool first = true;
    format r;
    auto end = tmp.end();
    for (auto it = tmp.begin(); it != end; ++it) {
        if (first) first = false; else r += compose(comma(), line());
        expr l     = it->first;
        expr new_l = pick_unused_pp_name(tmp.begin(), it, l);
        if (!is_eqp(l, new_l))
            update_local(it+1, end, conclusion, l, new_l);
        r += format{format(local_pp_name(new_l)), space(), colon(), nest(indent, compose(line(), fmt(env, mlocal_type(new_l), opts)))};
    }
    r = group(r);
    r += format{line(), turnstile, space(), nest(indent, fmt(env, conclusion, opts))};
    return group(r);
}

expr goal::mk_meta(name const & n, expr const & type) const {
    if (has_local(type)) {
        bool failed = false;
        name missing;
        for_each(type, [&](expr const & e, unsigned) {
                if (!has_local(e) || failed) return false;
                if (is_local(e)) {
                    bool found = false;
                    for (hypothesis const & h : m_hypotheses) {
                        if (mlocal_name(h.first) == mlocal_name(e)) {
                            found = true;
                            break;
                        }
                    }
                    if (!found) {
                        failed  = true;
                        missing = local_pp_name(e);
                        return false;
                    }
                }
                return true;
            });
        if (failed) {
            throw exception(sstream() << "invalid metavariable for goal, metavariable type contains local constant '"
                            << missing << "' which is not a hypothesis for this goal");
        }
    }
    expr t = type;
    buffer<expr> args;
    for (hypothesis const & h : m_hypotheses) {
        if (h.second) {
            t = Pi(h.first, t);
            args.push_back(h.first);
        }
    }
    std::reverse(args.begin(), args.end());
    return mk_app(mk_metavar(n, t), args);
}

goal goal::instantiate_metavars(substitution const & s) const {
    hypotheses hs = map(m_hypotheses, [&](hypothesis const & h) {
            return mk_pair(s.instantiate_metavars_wo_jst(h.first), h.second);
        });
    expr c = s.instantiate_metavars_wo_jst(m_conclusion);
    return goal(hs, c);
}

static bool validate(expr const & r, hypotheses const & hs) {
    bool failed = false;
    for_each(r, [&](expr const & e, unsigned) {
            if (!has_local(e) || failed) return false;
            if (is_local(e) &&
                !std::any_of(hs.begin(), hs.end(), [&](hypothesis const & h) { return h.first == e; })) {
                failed = true;
                return false;
            }
            return true;
        });
    return !failed;
}

bool goal::validate() const {
    if (!::lean::validate(m_conclusion, m_hypotheses))
        return false;
    hypotheses const * h = &m_hypotheses;
    while (!is_nil(*h)) {
        if (!::lean::validate(mlocal_type(head(*h).first), tail(*h)))
            return false;
        h = &tail(*h);
    }
    return true;
}

DECL_UDATA(hypotheses)

static int mk_hypotheses(lua_State * L) {
    int i = lua_gettop(L);
    hypotheses r;
    if (i > 0 && is_hypotheses(L, i)) {
        r = to_hypotheses(L, i);
        i--;
    }
    while (i > 0) {
        if (is_expr(L, i)) {
            expr const & l = to_expr(L, i);
            if (!is_local(l))
                throw exception(sstream() << "arg #" << i << " must be a local constant or a pair");
            r = hypotheses(hypothesis(l, true), r);
        } else {
            lua_rawgeti(L, i, 1);
            lua_rawgeti(L, i, 2);
            if (!is_expr(L, -2) || !is_local(to_expr(L, -2)) || !lua_isboolean(L, -1))
                throw exception(sstream() << "arg #" << i << " must be a pair: local constant, Boolean");
            r = hypotheses(hypothesis(to_expr(L, -2), lua_toboolean(L, -1)), r);
            lua_pop(L, 2);
        }
        i--;
    }
    return push_hypotheses(L, r);
}

static int hypotheses_is_nil(lua_State * L) {
    lua_pushboolean(L, !to_hypotheses(L, 1));
    return 1;
}

static int hypotheses_head(lua_State * L) {
    hypotheses const & hs = to_hypotheses(L, 1);
    if (!hs)
        throw exception("head method expects a non-empty hypotheses list");
    push_expr(L, head(hs).first);
    push_boolean(L, head(hs).second);
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
        push_expr(L, head(hs).first);
        push_boolean(L, head(hs).second);
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
static int goal_mk_meta(lua_State * L) { return push_expr(L, to_goal(L, 1).mk_meta(to_name_ext(L, 2), to_expr(L, 3))); }
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
static int goal_validate(lua_State * L) { return push_boolean(L, to_goal(L, 1).validate()); }

static const struct luaL_Reg goal_m[] = {
    {"__gc",            goal_gc}, // never throws
    {"__tostring",      safe_function<goal_tostring>},
    {"hypotheses",      safe_function<goal_hypotheses>},
    {"hyps",            safe_function<goal_hypotheses>},
    {"conclusion",      safe_function<goal_conclusion>},
    {"mk_meta",         safe_function<goal_mk_meta>},
    {"pp",              safe_function<goal_pp>},
    {"validate",        safe_function<goal_validate>},
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
