/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/list_fn.h"
#include "kernel/kernel.h"
#include "kernel/free_vars.h"
#include "kernel/for_each_fn.h"
#include "library/expr_pair.h"
#include "library/ite.h"
#include "library/kernel_bindings.h"
#include "library/equality.h"

namespace lean {
static name g_Hc("Hc"); // auxiliary name for if-then-else

bool is_ceq(ro_environment const & env, expr e);

/**
   \brief Auxiliary functional object for creating "conditional equations"
*/
class to_ceqs_fn {
    ro_environment const & m_env;
    unsigned               m_idx;

    static list<expr_pair> mk_singleton(expr const & e, expr const & H) {
        return list<expr_pair>(mk_pair(e, H));
    }

    bool imported_ite() {
        return m_env->imported("if_then_else");
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
            expr new_e = mk_iff(a, False);
            expr new_H = mk_eqf_intro_th(a, H);
            return mk_singleton(new_e, new_H);
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
        } else if (is_ite(e) && imported_ite()) {
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
    to_ceqs_fn(ro_environment const & env):m_env(env), m_idx(0) {}

    list<expr_pair> operator()(expr const & e, expr const & H) {
        return filter(apply(e, H), [&](expr_pair const & p) { return is_ceq(m_env, p.first); });
    }
};

list<expr_pair> to_ceqs(ro_environment const & env, expr const & e, expr const & H) {
    return to_ceqs_fn(env)(e, H);
}

bool is_ceq(ro_environment const & env, expr e) {
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

    context ctx;
    while (is_pi(e)) {
        if (!found_args.empty()) {
            // Support for dependent types.
            // We may find the instantiation for the previous variables
            // by matching the type.
            for_each(abst_domain(e), visitor_fn);
        }
        // If a variable is a proposition, than if doesn't need to occurr in the lhs.
        // So, we mark it as true.
        found_args.push_back(env->is_proposition(abst_domain(e), ctx));
        ctx = extend(ctx, abst_name(e), abst_domain(e));
        e = abst_body(e);
    }
    expr lhs, rhs;
    if (is_equality(e, lhs, rhs)) {
        // traverse lhs, and mark all variables that occur there in is_lhs.
        for_each(lhs, visitor_fn);
        return std::find(found_args.begin(), found_args.end(), false) == found_args.end();
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
    case expr_kind::Lambda: case expr_kind::Pi:
        return
            is_permutation(abst_domain(lhs), abst_domain(rhs), offset, p) &&
            is_permutation(abst_body(lhs), abst_body(rhs), offset+1, p);
    case expr_kind::HEq:
        return
            is_permutation(heq_lhs(lhs), heq_lhs(rhs), offset, p) &&
            is_permutation(heq_rhs(lhs), heq_rhs(rhs), offset, p);
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

static int to_ceqs(lua_State * L) {
    ro_shared_environment env(L, 1);
    auto r = to_ceqs(env, to_expr(L, 2), to_expr(L, 3));
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
    lua_pushboolean(L, is_ceq(env, to_expr(L, 2)));
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
