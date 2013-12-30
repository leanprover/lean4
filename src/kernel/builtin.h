/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
// See src/builtin/kernel.lean for signatures.
extern expr const TypeM;
extern expr const TypeU;

/** \brief Return the Lean Boolean type. */
expr mk_bool_type();
extern expr const Bool;
bool is_bool(expr const & e);

/** \brief Create a Lean Boolean value (true/false) */
expr mk_bool_value(bool v);
extern expr const True;
extern expr const False;
/** \brief Return true iff \c e is a Lean Boolean value. */
bool is_bool_value(expr const & e);
/**
    \brief Convert a Lean Boolean value into a C++ Boolean value.
    \pre is_bool_value(e)
*/
bool to_bool(expr const & e);
/** \brief Return true iff \c e is the Lean true value. */
bool is_true(expr const & e);
/** \brief Return true iff \c e is the Lean false value. */
bool is_false(expr const & e);

expr mk_if_fn();
bool is_if_fn(expr const & e);
inline bool is_if(expr const & e) { return is_app(e) && is_if_fn(arg(e, 0)); }
inline expr mk_if(expr const & A, expr const & c, expr const & t, expr const & e) { return mk_app(mk_if_fn(), A, c, t, e); }
inline expr If(expr const & A, expr const & c, expr const & t, expr const & e) { return mk_if(A, c, t, e); }
inline expr mk_bool_if(expr const & c, expr const & t, expr const & e) { return mk_if(mk_bool_type(), c, t, e); }
inline expr bIf(expr const & c, expr const & t, expr const & e) { return mk_bool_if(c, t, e); }

expr mk_implies_fn();
bool is_implies_fn(expr const & e);
inline bool is_implies(expr const & e) { return is_app(e) && is_implies_fn(arg(e, 0)); }
inline expr mk_implies(expr const & e1, expr const & e2) { return mk_app(mk_implies_fn(), e1, e2); }
inline expr Implies(expr const & e1, expr const & e2) { return mk_implies(e1, e2); }

expr mk_iff_fn();
bool is_iff_fn(expr const & e);
inline bool is_iff(expr const & e) { return is_app(e) && is_iff_fn(arg(e, 0)); }
inline expr mk_iff(expr const & e1, expr const & e2) { return mk_app(mk_iff_fn(), e1, e2); }
inline expr Iff(expr const & e1, expr const & e2) { return mk_iff(e1, e2); }

expr mk_and_fn();
bool is_and_fn(expr const & e);
inline bool is_and(expr const & e) { return is_app(e) && is_and_fn(arg(e, 0)); }
inline expr mk_and(expr const & e1, expr const & e2) { return mk_app(mk_and_fn(), e1, e2); }
inline expr And(expr const & e1, expr const & e2) { return mk_and(e1, e2); }

expr mk_or_fn();
bool is_or_fn(expr const & e);
inline bool is_or(expr const & e) { return is_app(e) && is_or_fn(arg(e, 0)); }
inline expr mk_or(expr const & e1, expr const & e2) { return mk_app(mk_or_fn(), e1, e2); }
inline expr Or(expr const & e1, expr const & e2) { return mk_or(e1, e2); }

expr mk_not_fn();
bool is_not_fn(expr const & e);
inline bool is_not(expr const & e) { return is_app(e) && is_not_fn(arg(e, 0)); }
inline expr mk_not(expr const & e) { return mk_app(mk_not_fn(), e); }
inline expr Not(expr const & e) { return mk_not(e); }

expr mk_forall_fn();
bool is_forall_fn(expr const & e);
inline bool is_forall(expr const & e) { return is_app(e) && is_forall_fn(arg(e, 0)); }
inline expr mk_forall(expr const & A, expr const & P) { return mk_app(mk_forall_fn(), A, P); }
inline expr Forall(expr const & A, expr const & P) { return mk_forall(A, P); }

expr mk_exists_fn();
bool is_exists_fn(expr const & e);
inline bool is_exists(expr const & e) { return is_app(e) && is_exists_fn(arg(e, 0)); }
inline expr mk_exists(expr const & A, expr const & P) { return mk_app(mk_exists_fn(), A, P); }
inline expr Exists(expr const & A, expr const & P) { return mk_exists(A, P); }

expr mk_homo_eq_fn();
bool is_homo_eq_fn(expr const & e);
inline bool is_homo_eq(expr const & e) { return is_app(e) && is_homo_eq_fn(arg(e, 0)); }
inline expr mk_homo_eq(expr const & A, expr const & l, expr const & r) { return mk_app(mk_homo_eq_fn(), A, l, r); }
inline expr hEq(expr const & A, expr const & l, expr const & r) { return mk_homo_eq(A, l, r); }

expr mk_mp_fn();
inline expr MP(expr const & a, expr const & b, expr const & H1, expr const & H2) { return mk_app(mk_mp_fn(), a, b, H1, H2); }

expr mk_discharge_fn();
inline expr Discharge(expr const & a, expr const & b, expr const & H) { return mk_app(mk_discharge_fn(), a, b, H); }

expr mk_case_fn();
inline expr Case(expr const & P, expr const & H1, expr const & H2, expr const & a) { return mk_app(mk_case_fn(), P, H1, H2, a); }

expr mk_refl_fn();
inline expr Refl(expr const & A, expr const & a) { return mk_app(mk_refl_fn(), A, a); }

expr mk_subst_fn();
inline expr Subst(expr const & A, expr const & a, expr const & b, expr const & P, expr const & H1, expr const & H2) { return mk_app({mk_subst_fn(), A, a, b, P, H1, H2}); }

expr mk_eta_fn();
inline expr Eta(expr const & A, expr const & B, expr const & f) { return mk_app(mk_eta_fn(), A, B, f); }

expr mk_imp_antisym_fn();
inline expr ImpAntisym(expr const & a, expr const & b, expr const & H1, expr const & H2) { return mk_app(mk_imp_antisym_fn(), a, b, H1, H2); }

expr mk_abst_fn();
inline expr Abst(expr const & A, expr const & B, expr const & f, expr const & g, expr const & H) { return mk_app({mk_abst_fn(), A, B, f, g, H}); }

expr mk_hsymm_fn();
inline expr HSymm(expr const & A, expr const & B, expr const & a, expr const & b, expr const & H1) { return mk_app({mk_hsymm_fn(), A, B, a, b, H1}); }

expr mk_htrans_fn();
inline expr HTrans(expr const & A, expr const & B, expr const & C, expr const & a, expr const & b, expr const & c, expr const & H1, expr const & H2) {
    return mk_app({mk_htrans_fn(), A, B, C, a, b, c, H1, H2});
}

expr mk_trivial();
#define Trivial mk_trivial()

expr mk_true_ne_false();
#define TrueNeFalse mk_true_ne_false();

expr mk_em_fn();
inline expr EM(expr const & a) { return mk_app(mk_em_fn(), a); }

expr mk_false_elim_fn();
inline expr FalseElim(expr const & a, expr const & H) { return mk_app(mk_false_elim_fn(), a, H); }

expr mk_absurd_fn();
inline expr Absurd(expr const & a, expr const & H1, expr const & H2) { return mk_app(mk_absurd_fn(), a, H1, H2); }

expr mk_double_neg_fn();
inline expr DoubleNeg(expr const & a) { return mk_app(mk_double_neg_fn(), a); }

expr mk_double_neg_elim_fn();
inline expr DoubleNegElim(expr const & P, expr const & H) { return mk_app(mk_double_neg_elim_fn(), P, H); }

expr mk_mt_fn();
inline expr MT(expr const & a, expr const & b, expr const & H1, expr const & H2) { return mk_app(mk_mt_fn(), a, b, H1, H2); }

expr mk_contrapos_fn();
inline expr Contrapos(expr const & a, expr const & b, expr const & H) { return mk_app(mk_contrapos_fn(), a, b, H); }

expr mk_false_imp_any_fn();
inline expr FalseImpAny(expr const & a) { return mk_app(mk_false_imp_any_fn(), a); }

expr mk_absurd_elim_fn();
inline expr AbsurdElim(expr const & a, expr const & c, expr const & H1, expr const & H2) {
    return mk_app(mk_absurd_elim_fn(), a, c, H1, H2);
}

expr mk_eq_mp_fn();
inline expr EqMP(expr const & a, expr const & b, expr const & H1, expr const & H2) { return mk_app(mk_eq_mp_fn(), a, b, H1, H2); }

expr mk_not_imp1_fn();
inline expr NotImp1(expr const & a, expr const & b, expr const & H) { return mk_app(mk_not_imp1_fn(), a, b, H); }

expr mk_not_imp2_fn();
inline expr NotImp2(expr const & a, expr const & b, expr const & H) { return mk_app(mk_not_imp2_fn(), a, b, H); }

expr mk_conj_fn();
inline expr Conj(expr const & a, expr const & b, expr const & H1, expr const & H2) { return mk_app(mk_conj_fn(), a, b, H1, H2); }

expr mk_conjunct1_fn();
inline expr Conjunct1(expr const & a, expr const & b, expr const & H) { return mk_app(mk_conjunct1_fn(), a, b, H); }

expr mk_conjunct2_fn();
inline expr Conjunct2(expr const & a, expr const & b, expr const & H) { return mk_app(mk_conjunct2_fn(), a, b, H); }

expr mk_disj1_fn();
inline expr Disj1(expr const & a, expr const & H, expr const & b) { return mk_app(mk_disj1_fn(), a, H, b); }

expr mk_disj2_fn();
inline expr Disj2(expr const & b, expr const & a, expr const & H) { return mk_app(mk_disj2_fn(), b, a, H); }

expr mk_disj_cases_fn();
inline expr DisjCases(expr const & a, expr const & b, expr const & c, expr const & H1, expr const & H2, expr const & H3) { return mk_app({mk_disj_cases_fn(), a, b, c, H1, H2, H3}); }

expr mk_refute_fn();
inline expr Refute(expr const & a, expr const & H) { return mk_app({mk_refute_fn(), a, H}); }

expr mk_symm_fn();
inline expr Symm(expr const & A, expr const & a, expr const & b, expr const & H) { return mk_app(mk_symm_fn(), A, a, b, H); }

expr mk_trans_fn();
inline expr Trans(expr const & A, expr const & a, expr const & b, expr const & c, expr const & H1, expr const & H2) { return mk_app({mk_trans_fn(), A, a, b, c, H1, H2}); }

expr mk_eqt_elim_fn();
inline expr EqTElim(expr const & a, expr const & H) { return mk_app(mk_eqt_elim_fn(), a, H); }

expr mk_eqt_intro_fn();
inline expr EqTIntro(expr const & a, expr const & H) { return mk_app(mk_eqt_intro_fn(), a, H); }

expr mk_congr1_fn();
inline expr Congr1(expr const & A, expr const & B, expr const & f, expr const & g, expr const & a, expr const & H) { return mk_app({mk_congr1_fn(), A, B, f, g, a, H}); }

expr mk_congr2_fn();
inline expr Congr2(expr const & A, expr const & B, expr const & a, expr const & b, expr const & f, expr const & H) { return mk_app({mk_congr2_fn(), A, B, a, b, f, H}); }

expr mk_congr_fn();
inline expr Congr(expr const & A, expr const & B, expr const & f, expr const & g, expr const & a, expr const & b, expr const & H1, expr const & H2) { return mk_app({mk_congr_fn(), A, B, f, g, a, b, H1, H2}); }

expr mk_forall_elim_fn();
inline expr ForallElim(expr const & A, expr const & P, expr const & H, expr const & a) { return mk_app(mk_forall_elim_fn(), A, P, H, a); }

expr mk_forall_intro_fn();
inline expr ForallIntro(expr const & A, expr const & P, expr const & H) { return mk_app(mk_forall_intro_fn(), A, P, H); }

expr mk_exists_elim_fn();
inline expr ExistsElim(expr const & A, expr const & P, expr const & B, expr const & H1, expr const & H2) { return mk_app({mk_exists_elim_fn(), A, P, B, H1, H2}); }

expr mk_exists_intro_fn();
inline expr ExistsIntro(expr const & A, expr const & P, expr const & a, expr const & H) { return mk_app(mk_exists_intro_fn(), A, P, a, H); }

void import_kernel(environment const & env);
}
