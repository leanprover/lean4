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
#include "kernel/metavar.h"
#include "library/kernel_bindings.h"
#include "library/tactic/goal.h"

namespace lean {
format goal::pp(formatter const & fmt) const {
    return pp(fmt, substitution());
}

format goal::pp(formatter const & fmt, substitution const & s) const {
    substitution tmp_subst(s);
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
        expr t     = tmp_subst.instantiate(mlocal_type(l));
        r += fmt(l) + space() + colon() + nest(indent, line() + fmt(t));
    }
    r = group(r);
    r += line() + turnstile + space() + nest(indent, fmt(tmp_subst.instantiate(conclusion)));
    return group(r);
}

expr goal::abstract(expr const & v) const {
    buffer<expr> locals;
    get_app_args(m_meta, locals);
    return Fun(locals, v);
}

expr goal::mk_meta(name const & n, expr const & type) const {
    buffer<expr> locals;
    expr this_mvar = get_app_args(m_meta, locals);
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
        return tc.is_def_eq(tc.check(m_meta).first, m_type).first;
    } else {
        return false;
    }
}

list<expr> goal::to_context() const {
    buffer<expr> locals;
    get_app_rev_args(m_meta, locals);
    return to_list(locals.begin(), locals.end());
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
    return push_expr(L, to_goal(L, 1).mk_meta(to_name_ext(L, 2), to_expr(L, 3)));
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
