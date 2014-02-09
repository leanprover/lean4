/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <vector>
#include <algorithm>
#include "util/name_set.h"
#include "util/buffer.h"
#include "kernel/for_each_fn.h"
#include "kernel/replace_fn.h"
#include "kernel/abstract.h"
#include "kernel/type_checker.h"
#include "library/kernel_bindings.h"
#include "library/tactic/goal.h"

namespace lean {

name mk_unique_hypothesis_name(hypotheses const & hs, name const & suggestion) {
    name n = suggestion;
    unsigned i = 0;
    // TODO(Leo): investigate if this method is a performance bottleneck
    while (true) {
        bool ok = true;
        for (auto const & p : hs) {
            if (is_prefix_of(n, p.first)) {
                ok = false;
                break;
            }
        }
        if (ok) {
            return n;
        } else {
            i++;
            n = name(suggestion, i);
        }
    }
}

name update_hypotheses_fn::operator()(name const & suggestion, expr const & t) {
    name n = mk_unique_hypothesis_name(m_hypotheses, suggestion);
    m_hypotheses.emplace_front(n, t);
    return n;
}

goal::goal(hypotheses const & hs, expr const & c):m_hypotheses(hs), m_conclusion(c) {}

format goal::pp(formatter const & fmt, options const & opts) const {
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
        r += format{format(p.first), space(), colon(), nest(indent, compose(line(), fmt(p.second, opts)))};
    }

    r = group(r);
    r += format{line(), turnstile, space(), nest(indent, fmt(m_conclusion, opts))};
    return group(r);
}

name goal::mk_unique_hypothesis_name(name const & suggestion) const {
    return ::lean::mk_unique_hypothesis_name(m_hypotheses, suggestion);
}

goal_proof_fn::goal_proof_fn(std::vector<expr> && consts):
    m_constants(consts) {
}

expr goal_proof_fn::operator()(expr const & pr) const {
    return abstract(pr, m_constants.size(), m_constants.data());
}

static name_set collect_used_names(context const & ctx, expr const & t) {
    name_set r;
    auto f = [&r](expr const & e, unsigned) { if (is_constant(e)) r.insert(const_name(e)); return true; };
    for_each_fn<decltype(f)> visitor(f);
    for (auto const & e : ctx) {
        if (optional<expr> const & d = e.get_domain())
            visitor(*d);
        if (optional<expr> const & b = e.get_body())
            visitor(*b);
    }
    visitor(t);
    return r;
}

static name mk_unique_name(name_set & s, name const & suggestion) {
    unsigned i = 1;
    name n = suggestion;
    while (true) {
        if (s.find(n) == s.end()) {
            s.insert(n);
            return n;
        } else {
            n = name(suggestion, i);
            i++;
        }
    }
}

static name g_unused       = name::mk_internal_unique_name();
static expr g_unused_const = mk_constant(g_unused);

std::pair<goal, goal_proof_fn> to_goal(ro_environment const & env, context const & ctx, expr const & t) {
    type_inferer inferer(env);
    if (!inferer.is_proposition(t, ctx))
        throw type_is_not_proposition_exception();
    name_set used_names = collect_used_names(ctx, t);
    buffer<context_entry> entries;
    for (auto const & e : ctx)
        entries.push_back(e);
    std::reverse(entries.begin(), entries.end());
    buffer<hypothesis> hypotheses;   // normalized names and types of the entries processed so far
    buffer<optional<expr>> bodies;   // normalized bodies of the entries processed so far
    std::vector<expr> consts;        // cached consts[i] == mk_constant(names[i], hypotheses[i])
    auto replace_vars = [&](expr const & e, unsigned offset) -> expr {
        if (is_var(e)) {
            unsigned vidx = var_idx(e);
            if (vidx >= offset) {
                unsigned nvidx = vidx - offset;
                unsigned nfv   = consts.size();
                if (nvidx >= nfv)
                    throw exception("failed to create goal, unknown free variable");
                unsigned lvl   = nfv - nvidx - 1;
                if (bodies[lvl])
                    return *(bodies[lvl]);
                else
                    return consts[lvl];
            }
        }
        return e;
    };
    replace_fn<decltype(replace_vars)> replacer(replace_vars);
    auto it  = entries.begin();
    auto end = entries.end();
    for (; it != end; ++it) {
        auto const & e = *it;
        name n = mk_unique_name(used_names, e.get_name());
        optional<expr> d = e.get_domain();
        optional<expr> b = e.get_body();
        if (d) d = some_expr(replacer(*d));
        if (b) b = some_expr(replacer(*b));
        if (b && !d) {
            d = some_expr(inferer(*b));
        }
        replacer.clear();
        if (b && !inferer.is_proposition(*d)) {
            bodies.push_back(b);
            // Insert a dummy just to make sure consts has the right size.
            // The dummy must be a closed term, and should not be used anywhere else.
            consts.push_back(g_unused_const);
        } else {
            lean_assert(d);
            hypotheses.emplace_back(n, *d);
            bodies.push_back(none_expr());
            expr c = mk_constant(n, *d);
            consts.push_back(c);
        }
    }
    expr conclusion = replacer(t);
    return mk_pair(goal(to_list(hypotheses.begin(), hypotheses.end()), conclusion),
                   goal_proof_fn(std::move(consts)));
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

static int mk_goal(lua_State * L) {
    return push_goal(L, goal(to_hypotheses(L, 1), to_expr(L, 2)));
}

static int goal_hypotheses(lua_State * L) {
    return push_hypotheses(L, to_goal(L, 1).get_hypotheses());
}

static int goal_conclusion(lua_State * L) {
    return push_expr(L, to_goal(L, 1).get_conclusion());
}

static int goal_unique_name(lua_State * L) {
    return push_name(L, to_goal(L, 1).mk_unique_hypothesis_name(to_name_ext(L, 2)));
}

static int goal_tostring(lua_State * L) {
    std::ostringstream out;
    goal & g = to_goal(L, 1);
    formatter fmt = get_global_formatter(L);
    options opts  = get_global_options(L);
    out << mk_pair(g.pp(fmt, opts), opts);
    lua_pushstring(L, out.str().c_str());
    return 1;
}

static int goal_pp(lua_State * L) {
    int nargs = lua_gettop(L);
    goal & g = to_goal(L, 1);
    if (nargs == 1) {
        return push_format(L, g.pp(get_global_formatter(L), get_global_options(L)));
    } else if (nargs == 2) {
        if (is_formatter(L, 2))
            return push_format(L, g.pp(to_formatter(L, 2), get_global_options(L)));
        else
            return push_format(L, g.pp(get_global_formatter(L), to_options(L, 2)));
    } else {
        return push_format(L, g.pp(to_formatter(L, 2), to_options(L, 3)));
    }
}

static const struct luaL_Reg goal_m[] = {
    {"__gc",            goal_gc}, // never throws
    {"__tostring",      safe_function<goal_tostring>},
    {"hypotheses",      safe_function<goal_hypotheses>},
    {"hyps",            safe_function<goal_hypotheses>},
    {"conclusion",      safe_function<goal_conclusion>},
    {"unique_name",     safe_function<goal_unique_name>},
    {"pp",              safe_function<goal_pp>},
    {0, 0}
};

static void hypotheses_migrate(lua_State * src, int i, lua_State * tgt) {
    push_hypotheses(tgt, to_hypotheses(src, i));
}

static void goal_migrate(lua_State * src, int i, lua_State * tgt) {
    push_goal(tgt, to_goal(src, i));
}

void open_goal(lua_State * L) {
    luaL_newmetatable(L, hypotheses_mt);
    set_migrate_fn_field(L, -1, hypotheses_migrate);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, hypotheses_m, 0);

    SET_GLOBAL_FUN(hypotheses_pred, "is_hypotheses");
    SET_GLOBAL_FUN(mk_hypotheses, "hypotheses");

    luaL_newmetatable(L, goal_mt);
    set_migrate_fn_field(L, -1, goal_migrate);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, goal_m, 0);

    SET_GLOBAL_FUN(goal_pred, "is_goal");
    SET_GLOBAL_FUN(mk_goal, "goal");
}
}
