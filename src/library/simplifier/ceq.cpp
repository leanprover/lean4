/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/list_fn.h"
#include "kernel/kernel.h"
#include "kernel/free_vars.h"
#include "kernel/for_each_fn.h"
#include "kernel/type_checker.h"
#include "kernel/instantiate.h"
#include "kernel/occurs.h"
#include "library/expr_pair.h"
#include "library/kernel_bindings.h"
#include "library/equality.h"

namespace lean {
static name g_Hc("Hc"); // auxiliary name for if-then-else

bool is_ceq(ro_environment const & env, optional<ro_metavar_env> const & menv, expr e);

/**
   \brief Auxiliary functional object for creating "conditional equations"
*/
class to_ceqs_fn {
    ro_environment const &           m_env;
    optional<ro_metavar_env> const & m_menv;
    unsigned                         m_idx;

    static list<expr_pair> mk_singleton(expr const & e, expr const & H) {
        return to_list(mk_pair(e, H));
    }

    expr lift_free_vars(expr const & e, unsigned d) {
        return ::lean::lift_free_vars(e, d, m_menv);
    }

    name mk_aux_name() {
        if (m_idx == 0) {
            m_idx = 1;
            return g_Hc;
        } else {
            name r = name(g_Hc, m_idx);
            m_idx++;
            return r;
        }
    }

    list<expr_pair> apply(expr const & e, expr const & H) {
        if (is_equality(e)) {
            return mk_singleton(e, H);
        } else if (is_neq(e)) {
            expr T   = arg(e, 1);
            expr lhs = arg(e, 2);
            expr rhs = arg(e, 3);
            expr new_e = mk_iff(mk_eq(T, lhs, rhs), False);
            expr new_H = mk_neq_elim_th(T, lhs, rhs, H);
            return mk_singleton(new_e, new_H);
        } else if (is_not(e)) {
            expr a     = arg(e, 1);
            if (is_not(a)) {
                return apply(arg(a, 1), mk_not_not_elim_th(arg(a, 1), H));
            } else if (is_neq(a)) {
                return mk_singleton(update_app(a, 0, mk_eq_fn()),
                                    mk_not_neq_elim_th(arg(a, 1), arg(a, 2), arg(a, 3), H));
            } else if (is_or(a)) {
                return apply(mk_and(mk_not(arg(a, 1)), mk_not(arg(a, 2))),
                             mk_not_or_elim_th(arg(a, 1), arg(a, 2), H));
            } else {
                expr new_e = mk_iff(a, False);
                expr new_H = mk_eqf_intro_th(a, H);
                return mk_singleton(new_e, new_H);
            }
        } else if (is_and(e)) {
            expr a1     = arg(e, 1);
            expr a2     = arg(e, 2);
            expr new_H1 = mk_and_eliml_th(a1, a2, H);
            expr new_H2 = mk_and_elimr_th(a1, a2, H);
            return append(apply(a1, new_H1), apply(a2, new_H2));
        } else if (is_pi(e)) {
            expr new_e  = abst_body(e);
            expr new_H  = mk_app(lift_free_vars(H, 1), mk_var(0));
            auto ceqs   = apply(new_e, new_H);
            if (length(ceqs) == 1 && new_e == car(ceqs).first) {
                return mk_singleton(e, H);
            } else {
                return map(ceqs, [&](expr_pair const & e_H) -> expr_pair {
                        expr new_e = mk_pi(abst_name(e), abst_domain(e), e_H.first);
                        expr new_H = mk_lambda(abst_name(e),  abst_domain(e), e_H.second);
                        return mk_pair(new_e, new_H);
                    });
            }
        } else if (is_ite(e)) {
            expr c     = arg(e, 2);
            expr not_c = mk_not(c);
            expr c1    = lift_free_vars(c, 1);
            expr a1    = lift_free_vars(arg(e, 3), 1);
            expr b1    = lift_free_vars(arg(e, 4), 1);
            expr H1    = lift_free_vars(H, 1);
            auto then_ceqs = apply(a1, mk_if_imp_then_th(c1, a1, b1, H1, mk_var(0)));
            auto else_ceqs = apply(b1, mk_if_imp_else_th(c1, a1, b1, H1, mk_var(0)));
            name Hc = mk_aux_name();
            auto new_then_ceqs = map(then_ceqs, [&](expr_pair const & e_H) {
                    expr new_e = mk_pi(Hc, c, e_H.first);
                    expr new_H = mk_lambda(Hc, c, e_H.second);
                    return mk_pair(new_e, new_H);
                });
            auto new_else_ceqs = map(else_ceqs, [&](expr_pair const & e_H) {
                    expr new_e = mk_pi(Hc, not_c, e_H.first);
                    expr new_H = mk_lambda(Hc, not_c, e_H.second);
                    return mk_pair(new_e, new_H);
                });
            return append(new_then_ceqs, new_else_ceqs);
        } else {
            return mk_singleton(mk_iff(e, True), mk_eqt_intro_th(e, H));
        }
    }
public:
    to_ceqs_fn(ro_environment const & env, optional<ro_metavar_env> const & menv):m_env(env), m_menv(menv), m_idx(0) {}

    list<expr_pair> operator()(expr const & e, expr const & H) {
        return filter(apply(e, H), [&](expr_pair const & p) { return is_ceq(m_env, m_menv, p.first); });
    }
};

list<expr_pair> to_ceqs(ro_environment const & env, optional<ro_metavar_env> const & menv, expr const & e, expr const & H) {
    return to_ceqs_fn(env, menv)(e, H);
}

static name g_unique = name::mk_internal_unique_name();

bool is_ceq(ro_environment const & env, optional<ro_metavar_env> const & menv, expr e) {
    buffer<bool> found_args;
    // Define a procedure for marking arguments found.
    auto visitor_fn = [&](expr const & e, unsigned offset) {
        if (is_var(e)) {
            unsigned vidx = var_idx(e);
            if (vidx >= offset) {
                vidx -= offset;
                if (vidx >= found_args.size()) {
                    // it is a free variable
                } else {
                    found_args[found_args.size() - vidx - 1] = true;
                }
            }
        }
        return true;
    };
    type_checker tc(env);
    context ctx;
    buffer<expr> hypothesis; // arguments that are propositions
    expr e_prime = e;        // in e_prime we replace local variables with fresh constants
    unsigned next_idx = 0;
    while (is_pi(e)) {
        if (!found_args.empty()) {
            // Support for dependent types.
            // We may find the instantiation for the previous variables
            // by matching the type.
            for_each(abst_domain(e), visitor_fn);
        }
        // If a variable is a proposition, than if doesn't need to occurr in the lhs.
        // So, we mark it as true.
        if (tc.is_proposition(abst_domain(e), ctx, menv)) {
            found_args.push_back(true);
            hypothesis.push_back(abst_domain(e_prime));
        } else {
            found_args.push_back(false);
        }
        ctx = extend(ctx, abst_name(e), abst_domain(e));
        next_idx++;
        e_prime = instantiate(abst_body(e_prime), mk_constant(name(g_unique, next_idx)), menv);
        e = abst_body(e);
    }
    expr lhs, rhs;
    if (is_equality(e, lhs, rhs)) {
        // traverse lhs, and mark all variables that occur there in is_lhs.
        for_each(lhs, visitor_fn);
        if (std::find(found_args.begin(), found_args.end(), false) != found_args.end())
            return false;
        // basic looping ceq detection: the left-hand-side should not occur in the right-hand-side,
        // nor it should occur in any of the hypothesis
        expr lhs_prime, rhs_prime;
        lean_verify(is_equality(e_prime, lhs_prime, rhs_prime));
        return
            !occurs(lhs_prime, rhs_prime) &&
            std::all_of(hypothesis.begin(), hypothesis.end(), [&](expr const & h) { return !occurs(lhs_prime, h); });
    } else {
        return false;
    }
}

static bool is_permutation(expr const & lhs, expr const & rhs, unsigned offset, buffer<optional<unsigned>> & p) {
    if (lhs.kind() != rhs.kind())
        return false;
    switch (lhs.kind()) {
    case expr_kind::Constant: case expr_kind::Type: case expr_kind::Value: case expr_kind::MetaVar:
        return lhs == rhs;
    case expr_kind::Var:
        if (var_idx(lhs) < offset) {
            return lhs == rhs; // locally bound variable
        } else if (var_idx(lhs) - offset < p.size()) {
            if (p[var_idx(lhs) - offset]) {
                return *(p[var_idx(lhs) - offset]) == var_idx(rhs);
            } else {
                p[var_idx(lhs) - offset] = var_idx(rhs);
                return true;
            }
        } else {
            return lhs == rhs; // free variable
        }
    case expr_kind::HEq:
        return
            is_permutation(heq_lhs(lhs),  heq_lhs(rhs), offset, p) &&
            is_permutation(heq_rhs(lhs),  heq_rhs(rhs), offset, p);
    case expr_kind::Proj:
        return proj_first(lhs) == proj_first(rhs) && is_permutation(proj_arg(lhs), proj_arg(rhs), offset, p);
    case expr_kind::Pair:
        return
            is_permutation(pair_first(lhs),  pair_first(rhs), offset, p) &&
            is_permutation(pair_second(lhs), pair_second(rhs), offset, p) &&
            is_permutation(pair_type(lhs),   pair_type(rhs), offset, p);
    case expr_kind::Lambda: case expr_kind::Pi: case expr_kind::Sigma:
        return
            is_permutation(abst_domain(lhs), abst_domain(rhs), offset, p) &&
            is_permutation(abst_body(lhs), abst_body(rhs), offset+1, p);
    case expr_kind::App:
        if (num_args(lhs) == num_args(rhs)) {
            for (unsigned i = 0; i < num_args(lhs); i++) {
                if (!is_permutation(arg(lhs, i), arg(rhs, i), offset, p))
                    return false;
            }
            return true;
        } else {
            return false;
        }
    case expr_kind::Let:
        if (static_cast<bool>(let_type(lhs)) != static_cast<bool>(let_type(rhs)))
            return false;
        if (static_cast<bool>(let_type(lhs)) && !is_permutation(*let_type(lhs), *let_type(rhs), offset, p))
            return false;
        return
            is_permutation(let_value(lhs), let_value(rhs), offset, p) &&
            is_permutation(let_body(lhs), let_value(rhs), offset+1, p);
    }
    lean_unreachable();
}

bool is_permutation_ceq(expr e) {
    unsigned num_args = 0;
    while (is_pi(e)) {
        e = abst_body(e);
        num_args++;
    }
    expr lhs, rhs;
    if (is_equality(e, lhs, rhs)) {
        buffer<optional<unsigned>> permutation;
        permutation.resize(num_args);
        return is_permutation(lhs, rhs, 0, permutation);
    } else {
        return false;
    }
}

// Quick approximate test for e == (Type U).
// If the result is true, then \c e is definitionally equal to TypeU.
// If the result is false, then it may or may not be.
static bool is_TypeU(ro_environment const & env, expr const & e) {
    if (is_type(e)) {
        return e == TypeU;
    } else if (is_constant(e)) {
        auto obj = env->find_object(const_name(e));
        return obj && obj->is_definition() && is_TypeU(obj->get_value());
    } else {
        return false;
    }
}

bool is_safe_to_skip_check_ceq_types(ro_environment const & env, optional<ro_metavar_env> const & menv, expr ceq) {
    lean_assert(is_ceq(env, menv, ceq));
    type_checker tc(env);
    buffer<expr> args;
    buffer<bool> skip;
    unsigned next_idx = 0;
    bool to_check = false;
    while (is_pi(ceq)) {
        expr d = abst_domain(ceq);
        expr a = mk_constant(name(g_unique, next_idx), d);
        args.push_back(a);
        if (tc.is_proposition(d, context(), menv) ||
            is_TypeU(env, d)) {
            // See comment at ceq.h
            // 1- The argument has type (Type U). In Lean, (Type U) is the maximal universe.
            // 2- The argument is a proposition.
            skip.push_back(true);
        } else {
            skip.push_back(false);
            to_check = true;
        }
        ceq = instantiate(abst_body(ceq), a);
        next_idx++;
    }
    if (!to_check)
        return true;

    expr lhs, rhs;
    lean_verify(is_equality(ceq, lhs, rhs));

    auto arg_idx_core_fn = [&](expr const & e) -> optional<unsigned> {
        if (is_constant(e)) {
            name const & n = const_name(e);
            if (!n.is_atomic() && n.get_prefix() == g_unique) {
                return some(n.get_numeral());
            }
        }
        return optional<unsigned>();
    };

    auto arg_idx_fn = [&](expr const & e) -> optional<unsigned> {
        if (is_app(e))
            return arg_idx_core_fn(arg(e, 0));
        else if (is_lambda(e))
            return arg_idx_core_fn(abst_body(e));
        else
            return arg_idx_core_fn(e);
    };

    // Return true if the application \c e has an argument or an
    // application (f ...) where f is an argument.
    auto has_target_fn = [&](expr const & e) -> bool {
        lean_assert(is_app(e));
        for (unsigned i = 1; i < num_args(e); i++) {
            expr const & a = arg(e, i);
            if (arg_idx_fn(a))
                return true;
        }
        return false;
    };

    // 3- There is an application (f x) in the left-hand-side, and
    //    the type expected by f is definitionally equal to the argument type.
    // 4- There is an application (f (x ...)) in the left-hand-side, and
    //    the type expected by f is definitionally equal to the type of (x ...)
    // 5- There is an application (f (fun y, x)) in the left-hand-side,
    //    and the type expected by f is definitionally equal to the type of (fun y, x)
    std::function<void(expr const &, context const & ctx)> visit_fn =
        [&](expr const & e, context const & ctx) {
        if (is_app(e)) {
            expr const & f = arg(e, 0);
            if (has_target_fn(e)) {
                expr f_type = tc.infer_type(f, ctx, menv);
                for (unsigned i = 1; i < num_args(e); i++) {
                    f_type         = tc.ensure_pi(f_type, ctx, menv);
                    expr const & a = arg(e, i);
                    auto arg_idx = arg_idx_fn(a);
                    if (arg_idx && !skip[*arg_idx]) {
                        expr const & expected_type = abst_domain(f_type);
                        expr const & given_type    = tc.infer_type(a, ctx, menv);
                        if (tc.is_definitionally_equal(given_type, expected_type)) {
                            skip[*arg_idx] = true;
                        }
                    }
                    f_type = instantiate(abst_body(f_type), a);
                }
            }
            for (expr const & a : ::lean::args(e))
                visit_fn(a, ctx);
        } else if (is_abstraction(e)) {
            visit_fn(abst_domain(e), ctx);
            visit_fn(abst_body(e), extend(ctx, abst_name(e), abst_body(e)));
        }
    };

    visit_fn(lhs, context());
    return std::all_of(skip.begin(), skip.end(), [](bool b) { return b; });
}

static int to_ceqs(lua_State * L) {
    ro_shared_environment env(L, 1);
    optional<ro_metavar_env> menv;
    if (!lua_isnil(L, 2))
        menv = to_metavar_env(L, 2);
    auto r = to_ceqs(env, menv, to_expr(L, 3), to_expr(L, 4));
    lua_newtable(L);
    int i = 1;
    for (auto p : r) {
        lua_newtable(L);
        push_expr(L, p.first);
        lua_rawseti(L, -2, 1);
        push_expr(L, p.second);
        lua_rawseti(L, -2, 2);
        lua_rawseti(L, -2, i);
        i = i + 1;
    }
    return 1;
}

static int is_ceq(lua_State * L) {
    ro_shared_environment env(L, 1);
    optional<ro_metavar_env> menv;
    if (!lua_isnil(L, 2))
        menv = to_metavar_env(L, 2);
    lua_pushboolean(L, is_ceq(env, menv, to_expr(L, 3)));
    return 1;
}

static int is_permutation_ceq(lua_State * L) {
    lua_pushboolean(L, is_permutation_ceq(to_expr(L, 1)));
    return 1;
}

void open_ceq(lua_State * L) {
    SET_GLOBAL_FUN(to_ceqs, "to_ceqs");
    SET_GLOBAL_FUN(is_ceq,  "is_ceq");
    SET_GLOBAL_FUN(is_permutation_ceq, "is_permutation_ceq");
}
}
