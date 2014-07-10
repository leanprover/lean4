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
#include "kernel/type_checker.h"
#include "library/kernel_bindings.h"
#include "library/tactic/goal.h"

namespace lean {
static bool is_used_pp_name(expr const * begin, expr const * end, name const & n) {
    return std::any_of(begin, end, [&](expr const & h) {
            return local_pp_name(h) == n;
        });
}

static expr pick_unused_pp_name(expr const * begin, expr const * end, expr const & l) {
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

static void update_local(expr * begin, expr * end, expr & conclusion,
                         expr const & old_local, expr const & new_local) {
    for (auto it = begin; it != end; ++it)
        update_local(*it, old_local, new_local);
    update_local(conclusion, old_local, new_local);
}

format goal::pp(formatter const & fmt) const {
    options const & opts = fmt.get_options();
    unsigned indent  = get_pp_indent(opts);
    bool unicode     = get_pp_unicode(opts);
    format turnstile = unicode ? format("\u22A2") /* ⊢ */ : format("|-");
    expr conclusion  = m_type;
    buffer<expr> tmp;
    get_app_args(m_meta, tmp);
    bool first = true;
    format r;
    auto end = tmp.end();
    for (auto it = tmp.begin(); it != end; ++it) {
        if (first) first = false; else r += compose(comma(), line());
        expr l     = *it;
        expr new_l = pick_unused_pp_name(tmp.begin(), it, l);
        if (!is_eqp(l, new_l))
            update_local(it+1, end, conclusion, l, new_l);
        r += format{format(local_pp_name(new_l)), space(), colon(), nest(indent, compose(line(), fmt(mlocal_type(new_l))))};
    }
    r = group(r);
    r += format{line(), turnstile, space(), nest(indent, fmt(conclusion))};
    return group(r);
}

expr goal::abstract(expr const & v) const {
    buffer<expr> locals;
    get_app_args(m_meta, locals);
    return Fun(locals, v);
}

expr goal::mk_meta(name const & n, expr const & type, bool only_contextual) const {
    buffer<expr> locals;
    expr this_mvar = get_app_args(m_meta, locals);
    if (only_contextual) {
        auto new_end = std::remove_if(locals.begin(), locals.end(),
                                      [](expr const & l) { return !local_info(l).is_contextual(); });
        locals.shrink(locals.size() - (locals.end() - new_end));
    }
    expr mvar = copy_tag(this_mvar, mk_metavar(n, Pi(locals, type)));
    return copy_tag(m_meta, mk_app(mvar, locals));
}

static bool validate_locals(expr const & r, unsigned num_locals, expr const * locals) {
    bool failed = false;
    for_each(r, [&](expr const & e, unsigned) {
            if (!has_local(e) || failed) return false;
            if (is_local(e) &&
                !std::any_of(locals, locals + num_locals,
                             [&](expr const & l) { return mlocal_name(l) == mlocal_name(e); })) {
                failed = true;
                return false;
            }
            return true;
        });
    return !failed;
}

bool goal::validate_locals() const {
    buffer<expr> locals;
    get_app_args(m_meta, locals);
    if (!::lean::validate_locals(m_type, locals.size(), locals.data()))
        return false;
    unsigned i = locals.size();
    while (i > 0) {
        --i;
        if (!::lean::validate_locals(mlocal_type(locals[i]), i, locals.data()))
            return false;
    }
    return true;
}

bool goal::validate(environment const & env) const {
    if (validate_locals()) {
        type_checker tc(env);
        return tc.is_def_eq(tc.check(m_meta), m_type);
    } else {
        return false;
    }
}

DECL_UDATA(goal)

static int mk_goal(lua_State * L) { return push_goal(L, goal(to_expr(L, 1), to_expr(L, 2))); }
static int goal_meta(lua_State * L) { return push_expr(L, to_goal(L, 1).get_meta()); }
static int goal_type(lua_State * L) { return push_expr(L, to_goal(L, 1).get_type()); }
static int goal_tostring(lua_State * L) {
    std::ostringstream out;
    goal & g = to_goal(L, 1);
    formatter fmt   = mk_formatter(L);
    options opts    = get_global_options(L);
    out << mk_pair(g.pp(fmt), opts);
    lua_pushstring(L, out.str().c_str());
    return 1;
}
static int goal_mk_meta(lua_State * L) {
    int nargs = lua_gettop(L);
    return push_expr(L, to_goal(L, 1).mk_meta(to_name_ext(L, 2), to_expr(L, 3), nargs == 4 ? lua_toboolean(L, 4) : true));
}

static int goal_pp(lua_State * L) {
    int nargs = lua_gettop(L);
    goal & g = to_goal(L, 1);
    if (nargs == 1) {
        return push_format(L, g.pp(mk_formatter(L)));
    } else {
        return push_format(L, g.pp(to_formatter(L, 2)));
    }
}
static int goal_validate_locals(lua_State * L) { return push_boolean(L, to_goal(L, 1).validate_locals()); }
static int goal_validate(lua_State * L) { return push_boolean(L, to_goal(L, 1).validate(to_environment(L, 2))); }
static int goal_abstract(lua_State * L) { return push_expr(L, to_goal(L, 1).abstract(to_expr(L, 2))); }
static int goal_name(lua_State * L) { return push_name(L, to_goal(L, 1).get_name()); }

static const struct luaL_Reg goal_m[] = {
    {"__gc",            goal_gc}, // never throws
    {"__tostring",      safe_function<goal_tostring>},
    {"abstract",        safe_function<goal_abstract>},
    {"mk_meta",         safe_function<goal_mk_meta>},
    {"pp",              safe_function<goal_pp>},
    {"validate",        safe_function<goal_validate>},
    {"validate_locals", safe_function<goal_validate_locals>},
    {"meta",            safe_function<goal_meta>},
    {"type",            safe_function<goal_type>},
    {"name",            safe_function<goal_name>},
    {0, 0}
};

void open_goal(lua_State * L) {
    luaL_newmetatable(L, goal_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, goal_m, 0);

    SET_GLOBAL_FUN(goal_pred, "is_goal");
    SET_GLOBAL_FUN(mk_goal, "goal");
}
}
