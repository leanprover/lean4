/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include "util/luaref.h"
#include "util/lazy_list_fn.h"
#include "kernel/for_each_fn.h"
#include "kernel/abstract.h"
#include "kernel/type_checker.h"
#include "library/unifier.h"
#include "library/kernel_bindings.h"

namespace lean {
static std::pair<unify_status, substitution> unify_simple_core(substitution const & s, expr const & lhs, expr const & rhs,
                                                               justification const & j) {
    lean_assert(is_meta(lhs));
    buffer<expr> args;
    expr const & m = get_app_args(lhs, args);
    lean_assert(is_metavar(m));
    for (auto it = args.begin(); it != args.end(); it++) {
        if (!is_local(*it) || std::find(args.begin(), it, *it) != it)
            return mk_pair(unify_status::Unsupported, s);
    }
    if (is_meta(rhs) && get_app_fn(rhs) == m)
        return mk_pair(unify_status::Unsupported, s);
    bool failed = false;
    for_each(rhs, [&](expr const & e, unsigned) {
            if (failed)
                return false;
            if (is_local(e) && std::find(args.begin(), args.end(), e) == args.end()) {
                // right-hand-side contains variable that is not in the scope
                // of metavariable.
                failed = true;
                return false;
            }
            if (is_metavar(e) && e == m) {
                // occurs-check failed
                failed = true;
                return false;
            }
            // we only need to continue exploring e if it contains
            // metavariables and/or local constants.
            return has_metavar(e) || has_local(e);
        });
    if (failed)
        return mk_pair(unify_status::Failed, s);
    expr v = abstract_locals(rhs, args.size(), args.data());
    unsigned i = args.size();
    while (i > 0) {
        --i;
        v = mk_lambda(local_pp_name(args[i]), mlocal_type(args[i]), v);
    }
    return mk_pair(unify_status::Solved, s.assign(mlocal_name(m), v, j));
}

std::pair<unify_status, substitution> unify_simple(substitution const & s, expr const & lhs, expr const & rhs, justification const & j) {
    if (lhs == rhs)
        return mk_pair(unify_status::Solved, s);
    else if (!has_metavar(lhs) && !has_metavar(rhs))
        return mk_pair(unify_status::Failed, s);
    else if (is_meta(lhs))
        return unify_simple_core(s, lhs, rhs, j);
    else if (is_meta(rhs))
        return unify_simple_core(s, rhs, lhs, j);
    else
        return mk_pair(unify_status::Unsupported, s);
}

std::pair<unify_status, substitution> unify_simple_core(substitution const & s, level const & lhs, level const & rhs, justification const & j) {
    lean_assert(is_meta(lhs));
    bool contains = false;
    for_each(rhs, [&](level const & l) {
            if (contains)
                return false;
            if (l == lhs) {
                // occurs-check failed
                contains = true;
                return false;
            }
            return true;
        });
    if (contains) {
        if (is_succ(rhs))
            return mk_pair(unify_status::Failed, s);
        else
            return mk_pair(unify_status::Unsupported, s);
    }
    return mk_pair(unify_status::Solved, s.assign(meta_id(lhs), rhs, j));
}

std::pair<unify_status, substitution> unify_simple(substitution const & s, level const & lhs, level const & rhs, justification const & j) {
    if (lhs == rhs)
        return mk_pair(unify_status::Solved, s);
    else if (!has_meta(lhs) && !has_meta(rhs))
        return mk_pair(unify_status::Failed, s);
    else if (is_meta(lhs))
        return unify_simple_core(s, lhs, rhs, j);
    else if (is_meta(rhs))
        return unify_simple_core(s, rhs, lhs, j);
    else if (is_succ(lhs) && is_succ(rhs))
        return unify_simple(s, succ_of(lhs), succ_of(rhs), j);
    else
        return mk_pair(unify_status::Unsupported, s);
}

std::pair<unify_status, substitution> unify_simple(substitution const & s, constraint const & c) {
    if (is_eq_cnstr(c))
        return unify_simple(s, cnstr_lhs_expr(c), cnstr_rhs_expr(c), c.get_justification());
    else if (is_level_cnstr(c))
        return unify_simple(s, cnstr_lhs_level(c), cnstr_rhs_level(c), c.get_justification());
    else
        return mk_pair(unify_status::Unsupported, s);
}

struct unifier_fn {
    environment    m_env;
    name_generator m_ngen;
    substitution   m_subst;
    unifier_plugin m_plugin;
    bool           m_use_exception;

    unifier_fn(environment const & env, unsigned /* num_cs */, constraint const * /* cs */,
               name_generator const & ngen, substitution const & s, unifier_plugin const & p,
               bool use_exception):
        m_env(env), m_ngen(ngen), m_subst(s), m_plugin(p), m_use_exception(use_exception) {
    }

    optional<substitution> next() {
        // TODO(Leo)
        return optional<substitution>();
    }
};

lazy_list<substitution> unify(std::shared_ptr<unifier_fn> const & u) {
    return mk_lazy_list<substitution>([=]() {
            auto s = u->next();
            if (s)
                return some(mk_pair(*s, unify(u)));
            else
                return lazy_list<substitution>::maybe_pair();
        });
}

lazy_list<substitution> unify(environment const & env,  unsigned num_cs, constraint const * cs, name_generator const & ngen,
                              unifier_plugin const & p, bool use_exception) {
    return unify(std::make_shared<unifier_fn>(env, num_cs, cs, ngen, substitution(), p, use_exception));
}

lazy_list<substitution> unify(environment const & env, unsigned num_cs, constraint const * cs, name_generator const & ngen,
                              bool use_exception) {
    return unify(env, num_cs, cs, ngen, [](constraint const &, name_generator const &) { return lazy_list<constraints>(); }, use_exception);
}

lazy_list<substitution> unify(environment const & env, expr const & lhs, expr const & rhs, name_generator const & ngen, unifier_plugin const & p) {
    substitution s;
    buffer<constraint> cs;
    name_generator new_ngen(ngen);
    bool failed = false;
    type_checker tc(env, new_ngen.mk_child(), [&](constraint const & c) {
            if (!failed) {
                auto r = unify_simple(s, c);
                switch (r.first) {
                case unify_status::Solved:
                    s = r.second; break;
                case unify_status::Failed:
                    failed = true; break;
                case unify_status::Unsupported:
                    cs.push_back(c); break;
                }
            }
        });
    if (!tc.is_def_eq(lhs, rhs) || failed) {
        return lazy_list<substitution>();
    } else if (cs.empty()) {
        return lazy_list<substitution>(s);
    } else {
        return unify(std::make_shared<unifier_fn>(env, cs.size(), cs.data(), ngen, s, p, false));
    }
}

lazy_list<substitution> unify(environment const & env, expr const & lhs, expr const & rhs, name_generator const & ngen) {
    return unify(env, lhs, rhs, ngen, [](constraint const &, name_generator const &) { return lazy_list<constraints>(); });
}

static int unify_simple(lua_State * L) {
    int nargs = lua_gettop(L);
    std::pair<unify_status, substitution> r;
    if (nargs == 2)
        r = unify_simple(to_substitution(L, 1), to_constraint(L, 2));
    else if (nargs == 3 && is_expr(L, 2))
        r = unify_simple(to_substitution(L, 1), to_expr(L, 2), to_expr(L, 3), justification());
    else if (nargs == 3 && is_level(L, 2))
        r = unify_simple(to_substitution(L, 1), to_level(L, 2), to_level(L, 3), justification());
    else if (is_expr(L, 2))
        r = unify_simple(to_substitution(L, 1), to_expr(L, 2), to_expr(L, 3), to_justification(L, 4));
    else
        r = unify_simple(to_substitution(L, 1), to_level(L, 2), to_level(L, 3), to_justification(L, 4));
    push_integer(L, static_cast<unsigned>(r.first));
    push_substitution(L, r.second);
    return 2;
}

typedef lazy_list<substitution> substitution_seq;
DECL_UDATA(substitution_seq)

static const struct luaL_Reg substitution_seq_m[] = {
    {"__gc", substitution_seq_gc},
    {0, 0}
};

static int substitution_seq_next(lua_State * L) {
    substitution_seq seq = to_substitution_seq(L, lua_upvalueindex(1));
    substitution_seq::maybe_pair p;
    p = seq.pull();
    if (p) {
        push_substitution_seq(L, p->second);
        lua_replace(L, lua_upvalueindex(1));
        push_substitution(L, p->first);
    } else {
        lua_pushnil(L);
    }
    return 1;
}

static int push_substitution_seq_it(lua_State * L, substitution_seq const & seq) {
    push_substitution_seq(L, seq);
    lua_pushcclosure(L, &safe_function<substitution_seq_next>, 1); // create closure with 1 upvalue
    return 1;
}

static void to_constraint_buffer(lua_State * L, int idx, buffer<constraint> & cs) {
    luaL_checktype(L, idx, LUA_TTABLE);
    lua_pushvalue(L, idx); // put table on top of the stack
    int n = objlen(L, idx);
    for (int i = 1; i <= n; i++) {
        lua_rawgeti(L, -1, i);
        cs.push_back(to_constraint(L, -1));
        lua_pop(L, 1);
    }
    lua_pop(L, 1);
}

static constraints to_constraints(lua_State * L, int idx) {
    buffer<constraint> cs;
    to_constraint_buffer(L, idx, cs);
    return to_list(cs.begin(), cs.end());
}

static unifier_plugin to_unifier_plugin(lua_State * L, int idx) {
    luaL_checktype(L, idx, LUA_TFUNCTION); // user-fun
    luaref f(L, idx);
    return unifier_plugin([=](constraint const & c, name_generator const & ngen) {
            lua_State * L = f.get_state();
            f.push();
            push_constraint(L, c);
            push_name_generator(L, ngen);
            pcall(L, 2, 1, 0);
            lazy_list<constraints> r;
            if (is_constraint(L, -1)) {
                // single constraint
                r = lazy_list<constraints>(constraints(to_constraint(L, -1)));
            } else if (lua_istable(L, -1)) {
                int num = objlen(L, -1);
                if (num == 0) {
                    // empty table
                    r = lazy_list<constraints>();
                } else {
                    lua_rawgeti(L, -1, 1);
                    if (is_constraint(L, -1)) {
                        // array of constraints case
                        lua_pop(L, 1);
                        r = lazy_list<constraints>(to_constraints(L, -1));
                    } else {
                        lua_pop(L, 1);
                        buffer<constraints> css;
                        // array of array of constraints
                        for (int i = 1; i <= num; i++) {
                            lua_rawgeti(L, -1, i);
                            css.push_back(to_constraints(L, -1));
                            lua_pop(L, 1);
                        }
                        r = to_lazy(to_list(css.begin(), css.end()));
                    }
                }
            } else if (lua_isnil(L, -1)) {
                // nil case
                r = lazy_list<constraints>();
            } else {
                throw exception("invalid unifier plugin, the result value must be a constrant, "
                                "nil, an array of constraints, or an array of arrays of constraints");
            }
            lua_pop(L, 1);
            return r;
        });
}

static name g_tmp_prefix = name::mk_internal_unique_name();

static int unify(lua_State * L) {
    int nargs = lua_gettop(L);
    lazy_list<substitution> r;
    environment const & env = to_environment(L, 1);
    if (is_expr(L, 2)) {
        if (nargs == 3)
            r = unify(env, to_expr(L, 2), to_expr(L, 3), name_generator(g_tmp_prefix));
        else if (nargs == 4 && is_name_generator(L, 4))
            r = unify(env, to_expr(L, 2), to_expr(L, 3), to_name_generator(L, 4));
        else if (nargs == 4)
            r = unify(env, to_expr(L, 2), to_expr(L, 3), name_generator(g_tmp_prefix), to_unifier_plugin(L, 4));
        else
            r = unify(env, to_expr(L, 2), to_expr(L, 3), to_name_generator(L, 4), to_unifier_plugin(L, 5));
    } else {
        buffer<constraint> cs;
        to_constraint_buffer(L, 2, cs);
        if (nargs == 2)
            r = unify(env, cs.size(), cs.data(), name_generator(g_tmp_prefix));
        else if (nargs == 3 && is_name_generator(L, 3))
            r = unify(env, cs.size(), cs.data(), to_name_generator(L, 3));
        else if (nargs == 3)
            r = unify(env, cs.size(), cs.data(), name_generator(g_tmp_prefix), to_unifier_plugin(L, 3));
        else
            r = unify(env, cs.size(), cs.data(), to_name_generator(L, 3), to_unifier_plugin(L, 4));
    }
    return push_substitution_seq_it(L, r);
}

void open_unifier(lua_State * L) {
    luaL_newmetatable(L, substitution_seq_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, substitution_seq_m, 0);
    SET_GLOBAL_FUN(substitution_seq_pred, "is_substitution_seq");

    SET_GLOBAL_FUN(unify_simple,  "unify_simple");
    SET_GLOBAL_FUN(unify,         "unify");

    lua_newtable(L);
    SET_ENUM("Solved",       unify_status::Solved);
    SET_ENUM("Failed",       unify_status::Failed);
    SET_ENUM("Unsupported",  unify_status::Unsupported);
    lua_setglobal(L, "unify_status");
}
}
