/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include <unordered_map>
#include "kernel/environment.h"
#include "library/relation_manager.h"
#include "library/reducible.h"
#include "library/type_context.h"

namespace lean {
class app_builder_exception : public exception {
public:
    // We may provide more information in the future.
    app_builder_exception():
        exception("app_builder_exception, more information can be obtained using command "
                  "`set_option trace.app_builder true`") {}
};

/** \brief Create an application (d.{_ ... _} _ ... _ args[0] ... args[nargs-1]).
    The missing arguments and universes levels are inferred using type inference.

    \remark The method throwns an app_builder_exception if: not all arguments can be inferred;
    or constraints are created during type inference; or an exception is thrown
    during type inference.

    \remark This methods uses just higher-order pattern matching.

    \remark if the transparency mode is not provided, then mk_app will use Semireducible
    if the ctx.mode() is Reducible or None.
*/
expr mk_app(type_context_old & ctx, name const & c, unsigned nargs, expr const * args,
            optional<transparency_mode> const & md = optional<transparency_mode>());

inline expr mk_app(type_context_old & ctx, name const & c, std::initializer_list<expr> const & args,
                   optional<transparency_mode> const & md = optional<transparency_mode>()) {
    return mk_app(ctx, c, args.size(), args.begin(), md);
}

inline expr mk_app(type_context_old & ctx, name const & c, expr const & a1) {
    return mk_app(ctx, c, {a1});
}

inline expr mk_app(type_context_old & ctx, name const & c, expr const & a1, expr const & a2) {
    return mk_app(ctx, c, {a1, a2});
}

inline expr mk_app(type_context_old & ctx, name const & c, expr const & a1, expr const & a2, expr const & a3) {
    return mk_app(ctx, c, {a1, a2, a3});
}

inline expr mk_app(type_context_old & ctx, name const & c, expr const & a1, expr const & a2, expr const & a3, expr const & a4) {
    return mk_app(ctx, c, {a1, a2, a3, a4});
}

expr mk_app(type_context_old & ctx, name const & c, unsigned mask_sz, bool const * mask, expr const * args);

/** \brief Shortcut for mk_app(c, total_nargs, mask, expl_nargs), where
    \c mask starts with total_nargs - expl_nargs false's followed by expl_nargs true's
    \pre total_nargs >= expl_nargs */
expr mk_app(type_context_old & ctx, name const & c, unsigned total_nargs, unsigned expl_nargs, expr const * expl_args);

inline expr mk_app(type_context_old & ctx, name const & c, unsigned total_nargs, std::initializer_list<expr> const & args) {
    return mk_app(ctx, c, total_nargs, args.size(), args.begin());
}

inline expr mk_app(type_context_old & ctx, name const & c, unsigned total_nargs, expr const & a1) {
    return mk_app(ctx, c, total_nargs, {a1});
}

inline expr mk_app(type_context_old & ctx, name const & c, unsigned total_nargs, expr const & a1, expr const & a2) {
    return mk_app(ctx, c, total_nargs, {a1, a2});
}

inline expr mk_app(type_context_old & ctx, name const & c, unsigned total_nargs, expr const & a1, expr const & a2, expr const & a3) {
    return mk_app(ctx, c, total_nargs, {a1, a2, a3});
}

/** \brief Similar to mk_app(n, lhs, rhs), but handles eq and iff more efficiently. */
expr mk_rel(type_context_old & ctx, name const & n, expr const & lhs, expr const & rhs);
expr mk_eq(type_context_old & ctx, expr const & lhs, expr const & rhs);
expr mk_iff(type_context_old & ctx, expr const & lhs, expr const & rhs);
expr mk_heq(type_context_old & ctx, expr const & lhs, expr const & rhs);

/** \brief Similar a reflexivity proof for the given relation */
expr mk_refl(type_context_old & ctx, name const & relname, expr const & a);
expr mk_eq_refl(type_context_old & ctx, expr const & a);
expr mk_iff_refl(type_context_old & ctx, expr const & a);
expr mk_heq_refl(type_context_old & ctx, expr const & a);

/** \brief Similar a symmetry proof for the given relation */
expr mk_symm(type_context_old & ctx, name const & relname, expr const & H);
expr mk_eq_symm(type_context_old & ctx, expr const & H);
expr mk_eq_symm(type_context_old & ctx, expr const & a, expr const & b, expr const & H);
expr mk_iff_symm(type_context_old & ctx, expr const & H);
expr mk_heq_symm(type_context_old & ctx, expr const & H);

/** \brief Similar a transitivity proof for the given relation */
expr mk_trans(type_context_old & ctx, name const & relname, expr const & H1, expr const & H2);
expr mk_eq_trans(type_context_old & ctx, expr const & H1, expr const & H2);
expr mk_eq_trans(type_context_old & ctx, expr const & a, expr const & b, expr const & c, expr const & H1, expr const & H2);
expr mk_iff_trans(type_context_old & ctx, expr const & H1, expr const & H2);
expr mk_heq_trans(type_context_old & ctx, expr const & H1, expr const & H2);

/** \brief Create a (non-dependent) eq.rec application.
    C is the motive. The expected types for C, H1 and H2 are
    C : A -> Type
    H1 : C a
    H2 : a = b
    The resultant application is
    @eq.rec A a C H1 b H2 */
expr mk_eq_rec(type_context_old & ctx, expr const & C, expr const & H1, expr const & H2);

/** \brief Create a (dependent) eq.drec application.
    C is the motive. The expected types for C, H1 and H2 are
    C : Pi (x : A), a = x -> Type
    H1 : C a (eq.refl a)
    H2 : a = b
    The resultant application is
    @eq.drec A a C H1 b H2 */
expr mk_eq_drec(type_context_old & ctx, expr const & C, expr const & H1, expr const & H2);

expr mk_eq_of_heq(type_context_old & ctx, expr const & H);
expr mk_heq_of_eq(type_context_old & ctx, expr const & H);

expr mk_congr_arg(type_context_old & ctx, expr const & f, expr const & H, bool skip_arrow_test = false);
expr mk_congr_fun(type_context_old & ctx, expr const & H, expr const & a);
expr mk_congr(type_context_old & ctx, expr const & H1, expr const & H2, bool skip_arrow_test = false);

expr mk_funext(type_context_old & ctx, expr const & lam_pf);

/** \brief Given a reflexive relation R, and a proof H : a = b,
    build a proof for (R a b) */
expr lift_from_eq(type_context_old & ctx, name const & R, expr const & H);

/** \brief not p -> (p <-> false) */
expr mk_iff_false_intro(type_context_old & ctx, expr const & H);
/** \brief p -> (p <-> true) */
expr mk_iff_true_intro(type_context_old & ctx, expr const & H);
/** \brief (p <-> false) -> not p */
expr mk_not_of_iff_false(type_context_old & ctx, expr const & H);
/** \brief (p <-> true) -> p */
expr mk_of_iff_true(type_context_old & ctx, expr const & H);
/** \brief (true <-> false) -> false */
expr mk_false_of_true_iff_false(type_context_old & ctx, expr const & H);
/** \brief (true = false) -> false */
expr mk_false_of_true_eq_false(type_context_old & ctx, expr const & H);

/** \brief not p -> (p = false) */
expr mk_eq_false_intro(type_context_old & ctx, expr const & H);
/** \brief p -> (p = true) */
expr mk_eq_true_intro(type_context_old & ctx, expr const & H);
/** not(p <-> q) -> not(p = q) */
expr mk_neq_of_not_iff(type_context_old & ctx, expr const & H);

expr mk_of_eq_true(type_context_old & ctx, expr const & H);
expr mk_not_of_eq_false(type_context_old & ctx, expr const & H);

expr mk_not(type_context_old & ctx, expr const & H);

/** p -> not p -> b */
expr mk_absurd(type_context_old & ctx, expr const & Hp, expr const & Hnp, expr const & b);

expr mk_partial_add(type_context_old & ctx, expr const & A);
expr mk_partial_mul(type_context_old & ctx, expr const & A);
expr mk_zero(type_context_old & ctx, expr const & A);
expr mk_one(type_context_old & ctx, expr const & A);
expr mk_partial_left_distrib(type_context_old & ctx, expr const & A);
expr mk_partial_right_distrib(type_context_old & ctx, expr const & A);

expr mk_ss_elim(type_context_old & ctx, expr const & A, expr const & ss_inst, expr const & old_e, expr const & new_e);

/** \brief False elimination */
expr mk_false_rec(type_context_old & ctx, expr const & c, expr const & H);

/* (if c then t else e) */
expr mk_ite(type_context_old & ctx, expr const & c, expr const & t, expr const & e);

/* (@id type h) */
expr mk_id(type_context_old & ctx, expr const & type, expr const & h);
/* (id h) */
expr mk_id(type_context_old & ctx, expr const & h);

/* (id_rhs h) */
expr mk_id_rhs(type_context_old & ctx, expr const & h);

/* (id_delta h) */
expr mk_id_delta(type_context_old & ctx, expr const & h);

expr mk_iff_mp(type_context_old & ctx, expr const & h1, expr const & h2);
expr mk_iff_mpr(type_context_old & ctx, expr const & h1, expr const & h2);
expr mk_eq_mp(type_context_old & ctx, expr const & h1, expr const & h2);
expr mk_eq_mpr(type_context_old & ctx, expr const & h1, expr const & h2);

void initialize_app_builder();
void finalize_app_builder();
}
