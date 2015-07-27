/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/type_checker.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/for_each_fn.h"
#include "library/constants.h"
#include "library/util.h"
#include "library/relation_manager.h"
#include "library/occurs.h"
#include "library/simplifier/ceqv.h"

namespace lean {
bool is_ceqv(type_checker & tc, expr e);

bool is_simp_relation(environment const & env, name const & n) {
    return is_trans_relation(env, n) && is_refl_relation(env, n);
}

/** \brief Auxiliary functional object for creating "conditional equations" */
class to_ceqvs_fn {
    environment const &   m_env;
    type_checker &        m_tc;

    static list<expr_pair> mk_singleton(expr const & e, expr const & H) {
        return list<expr_pair>(mk_pair(e, H));
    }

    bool is_type(expr const & e) {
        return is_sort(m_tc.whnf(m_tc.infer(e).first).first);
    }

    bool is_relation(expr const & e) {
        if (!is_app(e)) return false;
        expr const & fn = get_app_fn(e);
        return is_constant(fn) && is_simp_relation(m_env, const_name(fn));
    }

    list<expr_pair> lift(expr const & local, list<expr_pair> const & l) {
        lean_assert(is_local(local));
        return map(l, [&](expr_pair const & e_H) {
                return mk_pair(Pi(local, e_H.first), Fun(local, e_H.second));
            });
    }

    bool is_prop(expr const & e) {
        constraint_seq cs;
        return m_tc.is_prop(e, cs) && !cs;
    }

    // If restricted is true, we don't use (e <-> true) rewrite
    list<expr_pair> apply(expr const & e, expr const & H, bool restrited) {
        expr c, Hdec, A, arg1, arg2;
        if (is_relation(e)) {
            return mk_singleton(e, H);
        } else if (is_standard(m_env) && is_not(m_env, e, arg1)) {
            expr new_e = mk_iff(arg1, mk_false());
            expr new_H = mk_app(mk_constant(get_iff_false_intro_name()), arg1, H);
            return mk_singleton(new_e, new_H);
        } else if (is_standard(m_env) && is_and(e, arg1, arg2)) {
            // TODO(Leo): we can extend this trick to any type that has only one constructor
            expr H1 = mk_app(mk_constant(get_and_elim_left_name()), arg1, arg2, H);
            expr H2 = mk_app(mk_constant(get_and_elim_right_name()), arg1, arg2, H);
            auto r1 = apply(arg1, H1, restrited);
            auto r2 = apply(arg2, H2, restrited);
            return append(r1, r2);
        } else if (is_pi(e)) {
            expr local = mk_local(m_tc.mk_fresh_name(), binding_name(e), binding_domain(e), binding_info(e));
            expr new_e = instantiate(binding_body(e), local);
            expr new_H = mk_app(H, local);
            auto r = apply(new_e, new_H, restrited);
            unsigned len = length(r);
            if (len == 0) {
                return r;
            } else if (len == 1 && head(r).first == new_e && head(r).second == new_H) {
                return mk_singleton(e, H);
            } else {
                return lift(local, r);
            }
        } else if (is_standard(m_env) && is_ite(e, c, Hdec, A, arg1, arg2) && is_prop(e)) {
            // TODO(Leo): support HoTT mode if users request
            expr not_c = mk_not(m_tc, c);
            expr Hc    = mk_local(m_tc.mk_fresh_name(), c);
            expr Hnc   = mk_local(m_tc.mk_fresh_name(), not_c);
            expr H1    = mk_app({mk_constant(get_implies_of_if_pos_name()),
                                 c, arg1, arg2, Hdec, e, Hc});
            expr H2    = mk_app({mk_constant(get_implies_of_if_neg_name()),
                                 c, arg1, arg2, Hdec, e, Hnc});
            auto r1    = lift(Hc, apply(arg1, H1, restrited));
            auto r2    = lift(Hnc, apply(arg2, H2, restrited));
            return append(r1, r2);
        } else if (!restrited) {
            constraint_seq cs;
            expr new_e = m_tc.whnf(e, cs);
            if (new_e != e && !cs) {
                if (auto r = apply(new_e, H, true))
                    return r;
            }
            if (is_standard(m_env) && is_prop(e)) {
                expr new_e = mk_iff(e, mk_true());
                expr new_H = mk_app(mk_constant(get_iff_true_intro_name()), arg1, H);
                return mk_singleton(new_e, new_H);
            } else {
                return list<expr_pair>();
            }
        } else {
            return list<expr_pair>();
        }
    }
public:
    to_ceqvs_fn(type_checker & tc):m_env(tc.env()), m_tc(tc) {}

    list<expr_pair> operator()(expr const & e, expr const & H) {
        bool restrited = false;
        list<expr_pair> lst = apply(e, H, restrited);
        return filter(lst, [&](expr_pair const & p) { return is_ceqv(m_tc, p.first); });
    }
};

list<expr_pair> to_ceqvs(type_checker & tc, expr const & e, expr const & H) {
    return to_ceqvs_fn(tc)(e, H);
}

bool is_simp_relation(environment const & env, expr const & e, expr & rel, expr & lhs, expr & rhs) {
    buffer<expr> args;
    rel = get_app_args(e, args);
    if (!is_constant(rel) || !is_simp_relation(env, const_name(rel)))
        return false;
    relation_info const * rel_info = get_relation_info(env, const_name(rel));
    if (!rel_info || rel_info->get_lhs_pos() >= args.size() || rel_info->get_rhs_pos() >= args.size())
        return false;
    lhs = args[rel_info->get_lhs_pos()];
    rhs = args[rel_info->get_rhs_pos()];
    return true;
}

bool is_simp_relation(environment const & env, expr const & e, expr & lhs, expr & rhs) {
    expr rel;
    return is_simp_relation(env, e, rel, lhs, rhs);
}

bool is_ceqv(type_checker & tc, expr e) {
    if (has_expr_metavar(e))
        return false;
    name_set to_find;
    // Define a procedure for removing arguments from to_find.
    auto visitor_fn = [&](expr const & e, unsigned) {
        if (is_local(e)) {
            to_find.erase(mlocal_name(e));
            return false;
        } else if (is_metavar(e)) {
            return false;
        } else {
            return true;
        }
    };
    environment const & env = tc.env();
    bool is_std = is_standard(env);
    buffer<expr> hypotheses; // arguments that are propositions
    while (is_pi(e)) {
        if (!to_find.empty()) {
            // Support for dependent types.
            // We may find the instantiation for the previous arguments
            // by matching the type.
            for_each(binding_domain(e), visitor_fn);
        }
        expr local = mk_local(tc.mk_fresh_name(), binding_domain(e));
        if (binding_info(e).is_inst_implicit()) {
            // If the argument can be instantiated by type class resolution, then
            // we don't need to find it in the lhs
        } else if (is_std && tc.is_prop(binding_domain(e)).first) {
            // If the argument is a proposition, we store it in hypotheses.
            // We check whether the lhs occurs in hypotheses or not.
            hypotheses.push_back(binding_domain(e));
        } else {
            to_find.insert(mlocal_name(local));
        }
        e = instantiate(binding_body(e), local);
    }
    expr lhs, rhs;
    if (!is_simp_relation(env, e, lhs, rhs))
        return false;
    // traverse lhs, and remove found variables from to_find
    for_each(lhs, visitor_fn);
    if (!to_find.empty())
        return false;
    // basic looping ceq detection: the left-hand-side should not occur in the right-hand-side,
    // nor it should occur in any of the hypothesis
    if (occurs(lhs, rhs))
        return false;
    if (std::any_of(hypotheses.begin(), hypotheses.end(), [&](expr const & h) { return occurs(lhs, h); }))
        return false;
    return true;
}

static bool is_permutation(expr const & lhs, expr const & rhs, unsigned offset, buffer<optional<unsigned>> & p) {
    if (lhs.kind() != rhs.kind())
        return false;
    switch (lhs.kind()) {
    case expr_kind::Constant: case expr_kind::Sort:
    case expr_kind::Meta: case expr_kind::Local:
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
            is_permutation(binding_domain(lhs), binding_domain(rhs), offset, p) &&
            is_permutation(binding_body(lhs), binding_body(rhs), offset+1, p);
    case expr_kind::App:
        return
            is_permutation(app_fn(lhs), app_fn(rhs), offset, p) &&
            is_permutation(app_arg(lhs), app_arg(rhs), offset, p);
    case expr_kind::Macro:
        if (macro_def(lhs) != macro_def(rhs) ||
            macro_num_args(lhs) != macro_num_args(rhs))
            return false;
        for (unsigned i = 0; i < macro_num_args(lhs); i++) {
            if (!is_permutation(macro_arg(lhs, i), macro_arg(rhs, i), offset, p))
                return false;
        }
        return true;
    }
    lean_unreachable();
}

bool is_permutation_ceqv(environment const & env, expr e) {
    unsigned num_args = 0;
    while (is_pi(e)) {
        e = binding_body(e);
        num_args++;
    }
    expr lhs, rhs;
    if (is_simp_relation(env, e, lhs, rhs)) {
        buffer<optional<unsigned>> permutation;
        permutation.resize(num_args);
        return is_permutation(lhs, rhs, 0, permutation);
    } else {
        return false;
    }
}
}
