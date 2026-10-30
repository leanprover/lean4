// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.Types
// Imports: public import Init.Data.Int.Linear public import Lean.Meta.Tactic.Grind.Arith.Util public import Lean.Meta.Tactic.Grind.Arith.CommRing.Types
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_Meta_Grind_registerSolverExtension___redArg(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0;
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core0_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core0_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_coreToInt_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_coreToInt_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_hyp_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_hyp_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defn_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defn_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnExpr_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnExpr_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_norm_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_norm_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_divCoeffs_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_divCoeffs_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_subst_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_subst_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofLeGe_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofLeGe_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofZeroDvd_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofZeroDvd_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofDvdDiv_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofDvdDiv_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_reorder_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_reorder_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_commRingNorm_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_commRingNorm_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnCommRing_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnCommRing_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnExprCommRing_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnExprCommRing_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mul_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mul_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_div_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_div_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mod_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mod_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_pow_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_pow_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_dec_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_dec_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_last_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_last_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_core_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_core_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_coreOfNat_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_coreOfNat_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_norm_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_norm_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_divCoeffs_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_divCoeffs_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_bmodCoeffs_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_bmodCoeffs_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveCombine_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveCombine_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveElim_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveElim_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_elim_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_elim_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ofEqZero_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ofEqZero_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_subst_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_subst_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2081_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2081_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2082_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2082_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_reorder_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_reorder_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_commRingNorm_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_commRingNorm_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_core_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_core_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreNeg_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreNeg_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreToInt_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreToInt_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreExpr_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreExpr_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofNatNonneg_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofNatNonneg_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_hyp_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_hyp_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_bound_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_bound_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dec_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dec_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_norm_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_norm_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_divCoeffs_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_divCoeffs_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combine_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combine_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combineDivCoeffs_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combineDivCoeffs_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_subst_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_subst_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofLeDiseq_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofLeDiseq_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofDiseqSplit_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofDiseqSplit_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_cooper_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_cooper_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dvdTightMod_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dvdTightMod_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_reorder_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_reorder_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_commRingNorm_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_commRingNorm_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core0_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core0_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_coreToInt_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_coreToInt_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_norm_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_norm_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_divCoeffs_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_divCoeffs_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_neg_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_neg_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_subst_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_subst_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_reorder_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_reorder_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_commRingNorm_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_commRingNorm_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_dvd_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_dvd_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_le_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_le_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_eq_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_eq_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_diseq_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_diseq_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_cooper_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_cooper_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0(void){
_start:
{
lean_object* v_natZero_1_; lean_object* v_intZero_2_; 
v_natZero_1_ = lean_unsigned_to_nat(0u);
v_intZero_2_ = lean_nat_to_int(v_natZero_1_);
return v_intZero_2_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(lean_object* v_x_3_){
_start:
{
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v_k_4_; uint64_t v___x_5_; lean_object* v_intZero_6_; uint8_t v_isNeg_7_; 
v_k_4_ = lean_ctor_get(v_x_3_, 0);
v___x_5_ = 0ULL;
v_intZero_6_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0);
v_isNeg_7_ = lean_int_dec_lt(v_k_4_, v_intZero_6_);
if (v_isNeg_7_ == 0)
{
lean_object* v_a_8_; lean_object* v___x_9_; lean_object* v___x_10_; uint64_t v___x_11_; uint64_t v___x_12_; 
v_a_8_ = lean_nat_abs(v_k_4_);
v___x_9_ = lean_unsigned_to_nat(2u);
v___x_10_ = lean_nat_mul(v___x_9_, v_a_8_);
lean_dec(v_a_8_);
v___x_11_ = lean_uint64_of_nat(v___x_10_);
lean_dec(v___x_10_);
v___x_12_ = lean_uint64_mix_hash(v___x_5_, v___x_11_);
return v___x_12_;
}
else
{
lean_object* v_abs_13_; lean_object* v_one_14_; lean_object* v_a_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; uint64_t v___x_19_; uint64_t v___x_20_; 
v_abs_13_ = lean_nat_abs(v_k_4_);
v_one_14_ = lean_unsigned_to_nat(1u);
v_a_15_ = lean_nat_sub(v_abs_13_, v_one_14_);
lean_dec(v_abs_13_);
v___x_16_ = lean_unsigned_to_nat(2u);
v___x_17_ = lean_nat_mul(v___x_16_, v_a_15_);
lean_dec(v_a_15_);
v___x_18_ = lean_nat_add(v___x_17_, v_one_14_);
lean_dec(v___x_17_);
v___x_19_ = lean_uint64_of_nat(v___x_18_);
lean_dec(v___x_18_);
v___x_20_ = lean_uint64_mix_hash(v___x_5_, v___x_19_);
return v___x_20_;
}
}
else
{
lean_object* v_k_21_; lean_object* v_v_22_; lean_object* v_p_23_; uint64_t v___x_24_; uint64_t v___y_26_; lean_object* v_intZero_32_; uint8_t v_isNeg_33_; 
v_k_21_ = lean_ctor_get(v_x_3_, 0);
v_v_22_ = lean_ctor_get(v_x_3_, 1);
v_p_23_ = lean_ctor_get(v_x_3_, 2);
v___x_24_ = 1ULL;
v_intZero_32_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0);
v_isNeg_33_ = lean_int_dec_lt(v_k_21_, v_intZero_32_);
if (v_isNeg_33_ == 0)
{
lean_object* v_a_34_; lean_object* v___x_35_; lean_object* v___x_36_; uint64_t v___x_37_; 
v_a_34_ = lean_nat_abs(v_k_21_);
v___x_35_ = lean_unsigned_to_nat(2u);
v___x_36_ = lean_nat_mul(v___x_35_, v_a_34_);
lean_dec(v_a_34_);
v___x_37_ = lean_uint64_of_nat(v___x_36_);
lean_dec(v___x_36_);
v___y_26_ = v___x_37_;
goto v___jp_25_;
}
else
{
lean_object* v_abs_38_; lean_object* v_one_39_; lean_object* v_a_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; uint64_t v___x_44_; 
v_abs_38_ = lean_nat_abs(v_k_21_);
v_one_39_ = lean_unsigned_to_nat(1u);
v_a_40_ = lean_nat_sub(v_abs_38_, v_one_39_);
lean_dec(v_abs_38_);
v___x_41_ = lean_unsigned_to_nat(2u);
v___x_42_ = lean_nat_mul(v___x_41_, v_a_40_);
lean_dec(v_a_40_);
v___x_43_ = lean_nat_add(v___x_42_, v_one_39_);
lean_dec(v___x_42_);
v___x_44_ = lean_uint64_of_nat(v___x_43_);
lean_dec(v___x_43_);
v___y_26_ = v___x_44_;
goto v___jp_25_;
}
v___jp_25_:
{
uint64_t v___x_27_; uint64_t v___x_28_; uint64_t v___x_29_; uint64_t v___x_30_; uint64_t v___x_31_; 
v___x_27_ = lean_uint64_mix_hash(v___x_24_, v___y_26_);
v___x_28_ = lean_uint64_of_nat(v_v_22_);
v___x_29_ = lean_uint64_mix_hash(v___x_27_, v___x_28_);
v___x_30_ = l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(v_p_23_);
v___x_31_ = lean_uint64_mix_hash(v___x_29_, v___x_30_);
return v___x_31_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___boxed(lean_object* v_x_45_){
_start:
{
uint64_t v_res_46_; lean_object* v_r_47_; 
v_res_46_ = l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(v_x_45_);
lean_dec_ref(v_x_45_);
v_r_47_ = lean_box_uint64(v_res_46_);
return v_r_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorIdx___impl(lean_object* v_x_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lean_obj_tag_nat(v_x_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorIdx___impl___boxed(lean_object* v_x_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorIdx___impl(v_x_52_);
lean_dec_ref(v_x_52_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(lean_object* v_t_54_, lean_object* v_k_55_){
_start:
{
switch(lean_obj_tag(v_t_54_))
{
case 0:
{
lean_object* v_a_56_; lean_object* v_zero_57_; lean_object* v___x_58_; 
v_a_56_ = lean_ctor_get(v_t_54_, 0);
lean_inc_ref(v_a_56_);
v_zero_57_ = lean_ctor_get(v_t_54_, 1);
lean_inc_ref(v_zero_57_);
lean_dec_ref_known(v_t_54_, 2);
v___x_58_ = lean_apply_2(v_k_55_, v_a_56_, v_zero_57_);
return v___x_58_;
}
case 1:
{
lean_object* v_a_59_; lean_object* v_b_60_; lean_object* v_p_u2081_61_; lean_object* v_p_u2082_62_; lean_object* v___x_63_; 
v_a_59_ = lean_ctor_get(v_t_54_, 0);
lean_inc_ref(v_a_59_);
v_b_60_ = lean_ctor_get(v_t_54_, 1);
lean_inc_ref(v_b_60_);
v_p_u2081_61_ = lean_ctor_get(v_t_54_, 2);
lean_inc_ref(v_p_u2081_61_);
v_p_u2082_62_ = lean_ctor_get(v_t_54_, 3);
lean_inc_ref(v_p_u2082_62_);
lean_dec_ref_known(v_t_54_, 4);
v___x_63_ = lean_apply_4(v_k_55_, v_a_59_, v_b_60_, v_p_u2081_61_, v_p_u2082_62_);
return v___x_63_;
}
case 2:
{
lean_object* v_a_64_; lean_object* v_b_65_; lean_object* v_toIntThm_66_; lean_object* v_lhs_67_; lean_object* v_rhs_68_; lean_object* v___x_69_; 
v_a_64_ = lean_ctor_get(v_t_54_, 0);
lean_inc_ref(v_a_64_);
v_b_65_ = lean_ctor_get(v_t_54_, 1);
lean_inc_ref(v_b_65_);
v_toIntThm_66_ = lean_ctor_get(v_t_54_, 2);
lean_inc_ref(v_toIntThm_66_);
v_lhs_67_ = lean_ctor_get(v_t_54_, 3);
lean_inc_ref(v_lhs_67_);
v_rhs_68_ = lean_ctor_get(v_t_54_, 4);
lean_inc_ref(v_rhs_68_);
lean_dec_ref_known(v_t_54_, 5);
v___x_69_ = lean_apply_5(v_k_55_, v_a_64_, v_b_65_, v_toIntThm_66_, v_lhs_67_, v_rhs_68_);
return v___x_69_;
}
case 3:
{
lean_object* v_h_70_; lean_object* v_lhs_71_; lean_object* v_rhs_72_; lean_object* v___x_73_; 
v_h_70_ = lean_ctor_get(v_t_54_, 0);
lean_inc_ref(v_h_70_);
v_lhs_71_ = lean_ctor_get(v_t_54_, 1);
lean_inc_ref(v_lhs_71_);
v_rhs_72_ = lean_ctor_get(v_t_54_, 2);
lean_inc_ref(v_rhs_72_);
lean_dec_ref_known(v_t_54_, 3);
v___x_73_ = lean_apply_3(v_k_55_, v_h_70_, v_lhs_71_, v_rhs_72_);
return v___x_73_;
}
case 4:
{
lean_object* v_e_74_; lean_object* v_p_75_; lean_object* v___x_76_; 
v_e_74_ = lean_ctor_get(v_t_54_, 0);
lean_inc_ref(v_e_74_);
v_p_75_ = lean_ctor_get(v_t_54_, 1);
lean_inc_ref(v_p_75_);
lean_dec_ref_known(v_t_54_, 2);
v___x_76_ = lean_apply_2(v_k_55_, v_e_74_, v_p_75_);
return v___x_76_;
}
case 5:
{
lean_object* v_h_77_; lean_object* v_x_78_; lean_object* v_e_x27_79_; lean_object* v___x_80_; 
v_h_77_ = lean_ctor_get(v_t_54_, 0);
lean_inc_ref(v_h_77_);
v_x_78_ = lean_ctor_get(v_t_54_, 1);
lean_inc(v_x_78_);
v_e_x27_79_ = lean_ctor_get(v_t_54_, 2);
lean_inc_ref(v_e_x27_79_);
lean_dec_ref_known(v_t_54_, 3);
v___x_80_ = lean_apply_3(v_k_55_, v_h_77_, v_x_78_, v_e_x27_79_);
return v___x_80_;
}
case 8:
{
lean_object* v_x_81_; lean_object* v_c_u2081_82_; lean_object* v_c_u2082_83_; lean_object* v___x_84_; 
v_x_81_ = lean_ctor_get(v_t_54_, 0);
lean_inc(v_x_81_);
v_c_u2081_82_ = lean_ctor_get(v_t_54_, 1);
lean_inc_ref(v_c_u2081_82_);
v_c_u2082_83_ = lean_ctor_get(v_t_54_, 2);
lean_inc_ref(v_c_u2082_83_);
lean_dec_ref_known(v_t_54_, 3);
v___x_84_ = lean_apply_3(v_k_55_, v_x_81_, v_c_u2081_82_, v_c_u2082_83_);
return v___x_84_;
}
case 9:
{
lean_object* v_c_u2081_85_; lean_object* v_c_u2082_86_; lean_object* v___x_87_; 
v_c_u2081_85_ = lean_ctor_get(v_t_54_, 0);
lean_inc_ref(v_c_u2081_85_);
v_c_u2082_86_ = lean_ctor_get(v_t_54_, 1);
lean_inc_ref(v_c_u2082_86_);
lean_dec_ref_known(v_t_54_, 2);
v___x_87_ = lean_apply_2(v_k_55_, v_c_u2081_85_, v_c_u2082_86_);
return v___x_87_;
}
case 11:
{
lean_object* v_c_88_; lean_object* v_e_89_; lean_object* v_x_90_; lean_object* v_t_91_; lean_object* v___x_92_; 
v_c_88_ = lean_ctor_get(v_t_54_, 0);
lean_inc_ref(v_c_88_);
v_e_89_ = lean_ctor_get(v_t_54_, 1);
lean_inc_ref(v_e_89_);
v_x_90_ = lean_ctor_get(v_t_54_, 2);
lean_inc(v_x_90_);
v_t_91_ = lean_ctor_get(v_t_54_, 3);
lean_inc_ref(v_t_91_);
lean_dec_ref_known(v_t_54_, 4);
v___x_92_ = lean_apply_4(v_k_55_, v_c_88_, v_e_89_, v_x_90_, v_t_91_);
return v___x_92_;
}
case 13:
{
lean_object* v_c_93_; lean_object* v_e_94_; lean_object* v_p_95_; lean_object* v___x_96_; 
v_c_93_ = lean_ctor_get(v_t_54_, 0);
lean_inc_ref(v_c_93_);
v_e_94_ = lean_ctor_get(v_t_54_, 1);
lean_inc_ref(v_e_94_);
v_p_95_ = lean_ctor_get(v_t_54_, 2);
lean_inc_ref(v_p_95_);
lean_dec_ref_known(v_t_54_, 3);
v___x_96_ = lean_apply_3(v_k_55_, v_c_93_, v_e_94_, v_p_95_);
return v___x_96_;
}
case 14:
{
lean_object* v_e_97_; lean_object* v_p_98_; lean_object* v_re_99_; lean_object* v_rp_100_; lean_object* v_p_x27_101_; lean_object* v___x_102_; 
v_e_97_ = lean_ctor_get(v_t_54_, 0);
lean_inc_ref(v_e_97_);
v_p_98_ = lean_ctor_get(v_t_54_, 1);
lean_inc_ref(v_p_98_);
v_re_99_ = lean_ctor_get(v_t_54_, 2);
lean_inc_ref(v_re_99_);
v_rp_100_ = lean_ctor_get(v_t_54_, 3);
lean_inc_ref(v_rp_100_);
v_p_x27_101_ = lean_ctor_get(v_t_54_, 4);
lean_inc_ref(v_p_x27_101_);
lean_dec_ref_known(v_t_54_, 5);
v___x_102_ = lean_apply_5(v_k_55_, v_e_97_, v_p_98_, v_re_99_, v_rp_100_, v_p_x27_101_);
return v___x_102_;
}
case 15:
{
lean_object* v_h_103_; lean_object* v_x_104_; lean_object* v_e_x27_105_; lean_object* v_p_106_; lean_object* v_re_107_; lean_object* v_rp_108_; lean_object* v_p_x27_109_; lean_object* v___x_110_; 
v_h_103_ = lean_ctor_get(v_t_54_, 0);
lean_inc_ref(v_h_103_);
v_x_104_ = lean_ctor_get(v_t_54_, 1);
lean_inc(v_x_104_);
v_e_x27_105_ = lean_ctor_get(v_t_54_, 2);
lean_inc_ref(v_e_x27_105_);
v_p_106_ = lean_ctor_get(v_t_54_, 3);
lean_inc_ref(v_p_106_);
v_re_107_ = lean_ctor_get(v_t_54_, 4);
lean_inc_ref(v_re_107_);
v_rp_108_ = lean_ctor_get(v_t_54_, 5);
lean_inc_ref(v_rp_108_);
v_p_x27_109_ = lean_ctor_get(v_t_54_, 6);
lean_inc_ref(v_p_x27_109_);
lean_dec_ref_known(v_t_54_, 7);
v___x_110_ = lean_apply_7(v_k_55_, v_h_103_, v_x_104_, v_e_x27_105_, v_p_106_, v_re_107_, v_rp_108_, v_p_x27_109_);
return v___x_110_;
}
case 16:
{
lean_object* v_a_x3f_111_; lean_object* v_cs_112_; lean_object* v___x_113_; 
v_a_x3f_111_ = lean_ctor_get(v_t_54_, 0);
lean_inc(v_a_x3f_111_);
v_cs_112_ = lean_ctor_get(v_t_54_, 1);
lean_inc_ref(v_cs_112_);
lean_dec_ref_known(v_t_54_, 2);
v___x_113_ = lean_apply_2(v_k_55_, v_a_x3f_111_, v_cs_112_);
return v___x_113_;
}
case 17:
{
lean_object* v_k_114_; lean_object* v_y_x3f_115_; lean_object* v_c_116_; lean_object* v___x_117_; 
v_k_114_ = lean_ctor_get(v_t_54_, 0);
lean_inc(v_k_114_);
v_y_x3f_115_ = lean_ctor_get(v_t_54_, 1);
lean_inc(v_y_x3f_115_);
v_c_116_ = lean_ctor_get(v_t_54_, 2);
lean_inc_ref(v_c_116_);
lean_dec_ref_known(v_t_54_, 3);
v___x_117_ = lean_apply_3(v_k_55_, v_k_114_, v_y_x3f_115_, v_c_116_);
return v___x_117_;
}
case 18:
{
lean_object* v_k_118_; lean_object* v_y_x3f_119_; lean_object* v_c_120_; lean_object* v___x_121_; 
v_k_118_ = lean_ctor_get(v_t_54_, 0);
lean_inc(v_k_118_);
v_y_x3f_119_ = lean_ctor_get(v_t_54_, 1);
lean_inc(v_y_x3f_119_);
v_c_120_ = lean_ctor_get(v_t_54_, 2);
lean_inc_ref(v_c_120_);
lean_dec_ref_known(v_t_54_, 3);
v___x_121_ = lean_apply_3(v_k_55_, v_k_118_, v_y_x3f_119_, v_c_120_);
return v___x_121_;
}
case 19:
{
lean_object* v_ka_122_; lean_object* v_ca_x3f_123_; lean_object* v_kb_124_; lean_object* v_cb_x3f_125_; lean_object* v___x_126_; 
v_ka_122_ = lean_ctor_get(v_t_54_, 0);
lean_inc(v_ka_122_);
v_ca_x3f_123_ = lean_ctor_get(v_t_54_, 1);
lean_inc(v_ca_x3f_123_);
v_kb_124_ = lean_ctor_get(v_t_54_, 2);
lean_inc(v_kb_124_);
v_cb_x3f_125_ = lean_ctor_get(v_t_54_, 3);
lean_inc(v_cb_x3f_125_);
lean_dec_ref_known(v_t_54_, 4);
v___x_126_ = lean_apply_4(v_k_55_, v_ka_122_, v_ca_x3f_123_, v_kb_124_, v_cb_x3f_125_);
return v___x_126_;
}
default: 
{
lean_object* v_c_127_; lean_object* v___x_128_; 
v_c_127_ = lean_ctor_get(v_t_54_, 0);
lean_inc_ref(v_c_127_);
lean_dec_ref(v_t_54_);
v___x_128_ = lean_apply_1(v_k_55_, v_c_127_);
return v___x_128_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim(lean_object* v_motive__2_129_, lean_object* v_ctorIdx_130_, lean_object* v_t_131_, lean_object* v_h_132_, lean_object* v_k_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_131_, v_k_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___boxed(lean_object* v_motive__2_135_, lean_object* v_ctorIdx_136_, lean_object* v_t_137_, lean_object* v_h_138_, lean_object* v_k_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim(v_motive__2_135_, v_ctorIdx_136_, v_t_137_, v_h_138_, v_k_139_);
lean_dec(v_ctorIdx_136_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core0_elim___redArg(lean_object* v_t_141_, lean_object* v_core0_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_141_, v_core0_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core0_elim(lean_object* v_motive__2_144_, lean_object* v_t_145_, lean_object* v_h_146_, lean_object* v_core0_147_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_145_, v_core0_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core_elim___redArg(lean_object* v_t_149_, lean_object* v_core_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_149_, v_core_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core_elim(lean_object* v_motive__2_152_, lean_object* v_t_153_, lean_object* v_h_154_, lean_object* v_core_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_153_, v_core_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_coreToInt_elim___redArg(lean_object* v_t_157_, lean_object* v_coreToInt_158_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_157_, v_coreToInt_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_coreToInt_elim(lean_object* v_motive__2_160_, lean_object* v_t_161_, lean_object* v_h_162_, lean_object* v_coreToInt_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_161_, v_coreToInt_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_hyp_elim___redArg(lean_object* v_t_165_, lean_object* v_hyp_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_165_, v_hyp_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_hyp_elim(lean_object* v_motive__2_168_, lean_object* v_t_169_, lean_object* v_h_170_, lean_object* v_hyp_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_169_, v_hyp_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defn_elim___redArg(lean_object* v_t_173_, lean_object* v_defn_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_173_, v_defn_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defn_elim(lean_object* v_motive__2_176_, lean_object* v_t_177_, lean_object* v_h_178_, lean_object* v_defn_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_177_, v_defn_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnExpr_elim___redArg(lean_object* v_t_181_, lean_object* v_defnExpr_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_181_, v_defnExpr_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnExpr_elim(lean_object* v_motive__2_184_, lean_object* v_t_185_, lean_object* v_h_186_, lean_object* v_defnExpr_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_185_, v_defnExpr_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_norm_elim___redArg(lean_object* v_t_189_, lean_object* v_norm_190_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_189_, v_norm_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_norm_elim(lean_object* v_motive__2_192_, lean_object* v_t_193_, lean_object* v_h_194_, lean_object* v_norm_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_193_, v_norm_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_divCoeffs_elim___redArg(lean_object* v_t_197_, lean_object* v_divCoeffs_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_197_, v_divCoeffs_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_divCoeffs_elim(lean_object* v_motive__2_200_, lean_object* v_t_201_, lean_object* v_h_202_, lean_object* v_divCoeffs_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_201_, v_divCoeffs_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_subst_elim___redArg(lean_object* v_t_205_, lean_object* v_subst_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_205_, v_subst_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_subst_elim(lean_object* v_motive__2_208_, lean_object* v_t_209_, lean_object* v_h_210_, lean_object* v_subst_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_209_, v_subst_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofLeGe_elim___redArg(lean_object* v_t_213_, lean_object* v_ofLeGe_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_213_, v_ofLeGe_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofLeGe_elim(lean_object* v_motive__2_216_, lean_object* v_t_217_, lean_object* v_h_218_, lean_object* v_ofLeGe_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_217_, v_ofLeGe_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofZeroDvd_elim___redArg(lean_object* v_t_221_, lean_object* v_ofZeroDvd_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_221_, v_ofZeroDvd_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofZeroDvd_elim(lean_object* v_motive__2_224_, lean_object* v_t_225_, lean_object* v_h_226_, lean_object* v_ofZeroDvd_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_225_, v_ofZeroDvd_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofDvdDiv_elim___redArg(lean_object* v_t_229_, lean_object* v_ofDvdDiv_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_229_, v_ofDvdDiv_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofDvdDiv_elim(lean_object* v_motive__2_232_, lean_object* v_t_233_, lean_object* v_h_234_, lean_object* v_ofDvdDiv_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_233_, v_ofDvdDiv_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_reorder_elim___redArg(lean_object* v_t_237_, lean_object* v_reorder_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_237_, v_reorder_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_reorder_elim(lean_object* v_motive__2_240_, lean_object* v_t_241_, lean_object* v_h_242_, lean_object* v_reorder_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_241_, v_reorder_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_commRingNorm_elim___redArg(lean_object* v_t_245_, lean_object* v_commRingNorm_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_245_, v_commRingNorm_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_commRingNorm_elim(lean_object* v_motive__2_248_, lean_object* v_t_249_, lean_object* v_h_250_, lean_object* v_commRingNorm_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_249_, v_commRingNorm_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnCommRing_elim___redArg(lean_object* v_t_253_, lean_object* v_defnCommRing_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_253_, v_defnCommRing_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnCommRing_elim(lean_object* v_motive__2_256_, lean_object* v_t_257_, lean_object* v_h_258_, lean_object* v_defnCommRing_259_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_257_, v_defnCommRing_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnExprCommRing_elim___redArg(lean_object* v_t_261_, lean_object* v_defnExprCommRing_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_261_, v_defnExprCommRing_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnExprCommRing_elim(lean_object* v_motive__2_264_, lean_object* v_t_265_, lean_object* v_h_266_, lean_object* v_defnExprCommRing_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_265_, v_defnExprCommRing_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mul_elim___redArg(lean_object* v_t_269_, lean_object* v_mul_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_269_, v_mul_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mul_elim(lean_object* v_motive__2_272_, lean_object* v_t_273_, lean_object* v_h_274_, lean_object* v_mul_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_273_, v_mul_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_div_elim___redArg(lean_object* v_t_277_, lean_object* v_div_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_277_, v_div_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_div_elim(lean_object* v_motive__2_280_, lean_object* v_t_281_, lean_object* v_h_282_, lean_object* v_div_283_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_281_, v_div_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mod_elim___redArg(lean_object* v_t_285_, lean_object* v_mod_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_285_, v_mod_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mod_elim(lean_object* v_motive__2_288_, lean_object* v_t_289_, lean_object* v_h_290_, lean_object* v_mod_291_){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_289_, v_mod_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_pow_elim___redArg(lean_object* v_t_293_, lean_object* v_pow_294_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_293_, v_pow_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_pow_elim(lean_object* v_motive__2_296_, lean_object* v_t_297_, lean_object* v_h_298_, lean_object* v_pow_299_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_297_, v_pow_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorIdx___impl(lean_object* v_x_301_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = lean_obj_tag_nat(v_x_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorIdx___impl___boxed(lean_object* v_x_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorIdx___impl(v_x_303_);
lean_dec_ref(v_x_303_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(lean_object* v_t_305_, lean_object* v_k_306_){
_start:
{
if (lean_obj_tag(v_t_305_) == 0)
{
lean_object* v_h_307_; lean_object* v___x_308_; 
v_h_307_ = lean_ctor_get(v_t_305_, 0);
lean_inc(v_h_307_);
lean_dec_ref_known(v_t_305_, 1);
v___x_308_ = lean_apply_1(v_k_306_, v_h_307_);
return v___x_308_;
}
else
{
lean_object* v_hs_309_; lean_object* v_decVars_310_; lean_object* v___x_311_; 
v_hs_309_ = lean_ctor_get(v_t_305_, 0);
lean_inc_ref(v_hs_309_);
v_decVars_310_ = lean_ctor_get(v_t_305_, 1);
lean_inc_ref(v_decVars_310_);
lean_dec_ref_known(v_t_305_, 2);
v___x_311_ = lean_apply_2(v_k_306_, v_hs_309_, v_decVars_310_);
return v___x_311_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim(lean_object* v_motive__6_312_, lean_object* v_ctorIdx_313_, lean_object* v_t_314_, lean_object* v_h_315_, lean_object* v_k_316_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_314_, v_k_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___boxed(lean_object* v_motive__6_318_, lean_object* v_ctorIdx_319_, lean_object* v_t_320_, lean_object* v_h_321_, lean_object* v_k_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim(v_motive__6_318_, v_ctorIdx_319_, v_t_320_, v_h_321_, v_k_322_);
lean_dec(v_ctorIdx_319_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_dec_elim___redArg(lean_object* v_t_324_, lean_object* v_dec_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_324_, v_dec_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_dec_elim(lean_object* v_motive__6_327_, lean_object* v_t_328_, lean_object* v_h_329_, lean_object* v_dec_330_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_328_, v_dec_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_last_elim___redArg(lean_object* v_t_332_, lean_object* v_last_333_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_332_, v_last_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_last_elim(lean_object* v_motive__6_335_, lean_object* v_t_336_, lean_object* v_h_337_, lean_object* v_last_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_336_, v_last_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorIdx___impl(lean_object* v_x_340_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = lean_obj_tag_nat(v_x_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorIdx___impl___boxed(lean_object* v_x_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorIdx___impl(v_x_342_);
lean_dec_ref(v_x_342_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(lean_object* v_t_344_, lean_object* v_k_345_){
_start:
{
switch(lean_obj_tag(v_t_344_))
{
case 1:
{
lean_object* v_e_346_; lean_object* v_thm_347_; lean_object* v_d_348_; lean_object* v_a_349_; lean_object* v___x_350_; 
v_e_346_ = lean_ctor_get(v_t_344_, 0);
lean_inc_ref(v_e_346_);
v_thm_347_ = lean_ctor_get(v_t_344_, 1);
lean_inc_ref(v_thm_347_);
v_d_348_ = lean_ctor_get(v_t_344_, 2);
lean_inc(v_d_348_);
v_a_349_ = lean_ctor_get(v_t_344_, 3);
lean_inc_ref(v_a_349_);
lean_dec_ref_known(v_t_344_, 4);
v___x_350_ = lean_apply_4(v_k_345_, v_e_346_, v_thm_347_, v_d_348_, v_a_349_);
return v___x_350_;
}
case 4:
{
lean_object* v_c_351_; lean_object* v_a_352_; lean_object* v___x_353_; 
v_c_351_ = lean_ctor_get(v_t_344_, 0);
lean_inc_ref(v_c_351_);
v_a_352_ = lean_ctor_get(v_t_344_, 1);
lean_inc(v_a_352_);
lean_dec_ref_known(v_t_344_, 2);
v___x_353_ = lean_apply_2(v_k_345_, v_c_351_, v_a_352_);
return v___x_353_;
}
case 5:
{
lean_object* v_c_u2081_354_; lean_object* v_c_u2082_355_; lean_object* v___x_356_; 
v_c_u2081_354_ = lean_ctor_get(v_t_344_, 0);
lean_inc_ref(v_c_u2081_354_);
v_c_u2082_355_ = lean_ctor_get(v_t_344_, 1);
lean_inc_ref(v_c_u2082_355_);
lean_dec_ref_known(v_t_344_, 2);
v___x_356_ = lean_apply_2(v_k_345_, v_c_u2081_354_, v_c_u2082_355_);
return v___x_356_;
}
case 6:
{
lean_object* v_c_u2081_357_; lean_object* v_c_u2082_358_; lean_object* v___x_359_; 
v_c_u2081_357_ = lean_ctor_get(v_t_344_, 0);
lean_inc_ref(v_c_u2081_357_);
v_c_u2082_358_ = lean_ctor_get(v_t_344_, 1);
lean_inc_ref(v_c_u2082_358_);
lean_dec_ref_known(v_t_344_, 2);
v___x_359_ = lean_apply_2(v_k_345_, v_c_u2081_357_, v_c_u2082_358_);
return v___x_359_;
}
case 9:
{
lean_object* v_x_360_; lean_object* v_c_u2081_361_; lean_object* v_c_u2082_362_; lean_object* v___x_363_; 
v_x_360_ = lean_ctor_get(v_t_344_, 0);
lean_inc(v_x_360_);
v_c_u2081_361_ = lean_ctor_get(v_t_344_, 1);
lean_inc_ref(v_c_u2081_361_);
v_c_u2082_362_ = lean_ctor_get(v_t_344_, 2);
lean_inc_ref(v_c_u2082_362_);
lean_dec_ref_known(v_t_344_, 3);
v___x_363_ = lean_apply_3(v_k_345_, v_x_360_, v_c_u2081_361_, v_c_u2082_362_);
return v___x_363_;
}
case 13:
{
lean_object* v_c_364_; lean_object* v_e_365_; lean_object* v_p_366_; lean_object* v___x_367_; 
v_c_364_ = lean_ctor_get(v_t_344_, 0);
lean_inc_ref(v_c_364_);
v_e_365_ = lean_ctor_get(v_t_344_, 1);
lean_inc_ref(v_e_365_);
v_p_366_ = lean_ctor_get(v_t_344_, 2);
lean_inc_ref(v_p_366_);
lean_dec_ref_known(v_t_344_, 3);
v___x_367_ = lean_apply_3(v_k_345_, v_c_364_, v_e_365_, v_p_366_);
return v___x_367_;
}
default: 
{
lean_object* v_e_368_; lean_object* v___x_369_; 
v_e_368_ = lean_ctor_get(v_t_344_, 0);
lean_inc_ref(v_e_368_);
lean_dec_ref(v_t_344_);
v___x_369_ = lean_apply_1(v_k_345_, v_e_368_);
return v___x_369_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim(lean_object* v_motive__7_370_, lean_object* v_ctorIdx_371_, lean_object* v_t_372_, lean_object* v_h_373_, lean_object* v_k_374_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_372_, v_k_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___boxed(lean_object* v_motive__7_376_, lean_object* v_ctorIdx_377_, lean_object* v_t_378_, lean_object* v_h_379_, lean_object* v_k_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim(v_motive__7_376_, v_ctorIdx_377_, v_t_378_, v_h_379_, v_k_380_);
lean_dec(v_ctorIdx_377_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_core_elim___redArg(lean_object* v_t_382_, lean_object* v_core_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_382_, v_core_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_core_elim(lean_object* v_motive__7_385_, lean_object* v_t_386_, lean_object* v_h_387_, lean_object* v_core_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_386_, v_core_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_coreOfNat_elim___redArg(lean_object* v_t_390_, lean_object* v_coreOfNat_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_390_, v_coreOfNat_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_coreOfNat_elim(lean_object* v_motive__7_393_, lean_object* v_t_394_, lean_object* v_h_395_, lean_object* v_coreOfNat_396_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_394_, v_coreOfNat_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_norm_elim___redArg(lean_object* v_t_398_, lean_object* v_norm_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_398_, v_norm_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_norm_elim(lean_object* v_motive__7_401_, lean_object* v_t_402_, lean_object* v_h_403_, lean_object* v_norm_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_402_, v_norm_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_divCoeffs_elim___redArg(lean_object* v_t_406_, lean_object* v_divCoeffs_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_406_, v_divCoeffs_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_divCoeffs_elim(lean_object* v_motive__7_409_, lean_object* v_t_410_, lean_object* v_h_411_, lean_object* v_divCoeffs_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_410_, v_divCoeffs_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_bmodCoeffs_elim___redArg(lean_object* v_t_414_, lean_object* v_bmodCoeffs_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_414_, v_bmodCoeffs_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_bmodCoeffs_elim(lean_object* v_motive__7_417_, lean_object* v_t_418_, lean_object* v_h_419_, lean_object* v_bmodCoeffs_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_418_, v_bmodCoeffs_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveCombine_elim___redArg(lean_object* v_t_422_, lean_object* v_solveCombine_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_422_, v_solveCombine_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveCombine_elim(lean_object* v_motive__7_425_, lean_object* v_t_426_, lean_object* v_h_427_, lean_object* v_solveCombine_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_426_, v_solveCombine_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveElim_elim___redArg(lean_object* v_t_430_, lean_object* v_solveElim_431_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_430_, v_solveElim_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveElim_elim(lean_object* v_motive__7_433_, lean_object* v_t_434_, lean_object* v_h_435_, lean_object* v_solveElim_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_434_, v_solveElim_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_elim_elim___redArg(lean_object* v_t_438_, lean_object* v_elim_439_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_438_, v_elim_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_elim_elim(lean_object* v_motive__7_441_, lean_object* v_t_442_, lean_object* v_h_443_, lean_object* v_elim_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_442_, v_elim_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ofEqZero_elim___redArg(lean_object* v_t_446_, lean_object* v_ofEqZero_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_446_, v_ofEqZero_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ofEqZero_elim(lean_object* v_motive__7_449_, lean_object* v_t_450_, lean_object* v_h_451_, lean_object* v_ofEqZero_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_450_, v_ofEqZero_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_subst_elim___redArg(lean_object* v_t_454_, lean_object* v_subst_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_454_, v_subst_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_subst_elim(lean_object* v_motive__7_457_, lean_object* v_t_458_, lean_object* v_h_459_, lean_object* v_subst_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_458_, v_subst_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2081_elim___redArg(lean_object* v_t_462_, lean_object* v_cooper_u2081_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_462_, v_cooper_u2081_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2081_elim(lean_object* v_motive__7_465_, lean_object* v_t_466_, lean_object* v_h_467_, lean_object* v_cooper_u2081_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_466_, v_cooper_u2081_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2082_elim___redArg(lean_object* v_t_470_, lean_object* v_cooper_u2082_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_470_, v_cooper_u2082_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2082_elim(lean_object* v_motive__7_473_, lean_object* v_t_474_, lean_object* v_h_475_, lean_object* v_cooper_u2082_476_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_474_, v_cooper_u2082_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_reorder_elim___redArg(lean_object* v_t_478_, lean_object* v_reorder_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_478_, v_reorder_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_reorder_elim(lean_object* v_motive__7_481_, lean_object* v_t_482_, lean_object* v_h_483_, lean_object* v_reorder_484_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_482_, v_reorder_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_commRingNorm_elim___redArg(lean_object* v_t_486_, lean_object* v_commRingNorm_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_486_, v_commRingNorm_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_commRingNorm_elim(lean_object* v_motive__7_489_, lean_object* v_t_490_, lean_object* v_h_491_, lean_object* v_commRingNorm_492_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_490_, v_commRingNorm_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorIdx___impl(lean_object* v_x_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = lean_obj_tag_nat(v_x_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorIdx___impl___boxed(lean_object* v_x_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorIdx___impl(v_x_496_);
lean_dec_ref(v_x_496_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(lean_object* v_t_498_, lean_object* v_k_499_){
_start:
{
switch(lean_obj_tag(v_t_498_))
{
case 1:
{
lean_object* v_e_500_; lean_object* v_p_501_; lean_object* v___x_502_; 
v_e_500_ = lean_ctor_get(v_t_498_, 0);
lean_inc_ref(v_e_500_);
v_p_501_ = lean_ctor_get(v_t_498_, 1);
lean_inc_ref(v_p_501_);
lean_dec_ref_known(v_t_498_, 2);
v___x_502_ = lean_apply_2(v_k_499_, v_e_500_, v_p_501_);
return v___x_502_;
}
case 2:
{
lean_object* v_e_503_; uint8_t v_pos_504_; lean_object* v_toIntThm_505_; lean_object* v_lhs_506_; lean_object* v_rhs_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v_e_503_ = lean_ctor_get(v_t_498_, 0);
lean_inc_ref(v_e_503_);
v_pos_504_ = lean_ctor_get_uint8(v_t_498_, sizeof(void*)*4);
v_toIntThm_505_ = lean_ctor_get(v_t_498_, 1);
lean_inc_ref(v_toIntThm_505_);
v_lhs_506_ = lean_ctor_get(v_t_498_, 2);
lean_inc_ref(v_lhs_506_);
v_rhs_507_ = lean_ctor_get(v_t_498_, 3);
lean_inc_ref(v_rhs_507_);
lean_dec_ref_known(v_t_498_, 4);
v___x_508_ = lean_box(v_pos_504_);
v___x_509_ = lean_apply_5(v_k_499_, v_e_503_, v___x_508_, v_toIntThm_505_, v_lhs_506_, v_rhs_507_);
return v___x_509_;
}
case 3:
{
lean_object* v_e_510_; uint8_t v_pos_511_; lean_object* v_lhs_512_; lean_object* v_rhs_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v_e_510_ = lean_ctor_get(v_t_498_, 0);
lean_inc_ref(v_e_510_);
v_pos_511_ = lean_ctor_get_uint8(v_t_498_, sizeof(void*)*3);
v_lhs_512_ = lean_ctor_get(v_t_498_, 1);
lean_inc_ref(v_lhs_512_);
v_rhs_513_ = lean_ctor_get(v_t_498_, 2);
lean_inc_ref(v_rhs_513_);
lean_dec_ref_known(v_t_498_, 3);
v___x_514_ = lean_box(v_pos_511_);
v___x_515_ = lean_apply_4(v_k_499_, v_e_510_, v___x_514_, v_lhs_512_, v_rhs_513_);
return v___x_515_;
}
case 5:
{
lean_object* v_h_516_; lean_object* v_lhs_517_; lean_object* v_rhs_518_; lean_object* v___x_519_; 
v_h_516_ = lean_ctor_get(v_t_498_, 0);
lean_inc_ref(v_h_516_);
v_lhs_517_ = lean_ctor_get(v_t_498_, 1);
lean_inc_ref(v_lhs_517_);
v_rhs_518_ = lean_ctor_get(v_t_498_, 2);
lean_inc_ref(v_rhs_518_);
lean_dec_ref_known(v_t_498_, 3);
v___x_519_ = lean_apply_3(v_k_499_, v_h_516_, v_lhs_517_, v_rhs_518_);
return v___x_519_;
}
case 7:
{
lean_object* v_h_520_; lean_object* v___x_521_; 
v_h_520_ = lean_ctor_get(v_t_498_, 0);
lean_inc(v_h_520_);
lean_dec_ref_known(v_t_498_, 1);
v___x_521_ = lean_apply_1(v_k_499_, v_h_520_);
return v___x_521_;
}
case 10:
{
lean_object* v_c_u2081_522_; lean_object* v_c_u2082_523_; lean_object* v___x_524_; 
v_c_u2081_522_ = lean_ctor_get(v_t_498_, 0);
lean_inc_ref(v_c_u2081_522_);
v_c_u2082_523_ = lean_ctor_get(v_t_498_, 1);
lean_inc_ref(v_c_u2082_523_);
lean_dec_ref_known(v_t_498_, 2);
v___x_524_ = lean_apply_2(v_k_499_, v_c_u2081_522_, v_c_u2082_523_);
return v___x_524_;
}
case 11:
{
lean_object* v_c_u2081_525_; lean_object* v_c_u2082_526_; lean_object* v_k_527_; lean_object* v___x_528_; 
v_c_u2081_525_ = lean_ctor_get(v_t_498_, 0);
lean_inc_ref(v_c_u2081_525_);
v_c_u2082_526_ = lean_ctor_get(v_t_498_, 1);
lean_inc_ref(v_c_u2082_526_);
v_k_527_ = lean_ctor_get(v_t_498_, 2);
lean_inc(v_k_527_);
lean_dec_ref_known(v_t_498_, 3);
v___x_528_ = lean_apply_3(v_k_499_, v_c_u2081_525_, v_c_u2082_526_, v_k_527_);
return v___x_528_;
}
case 12:
{
lean_object* v_x_529_; lean_object* v_c_u2081_530_; lean_object* v_c_u2082_531_; lean_object* v___x_532_; 
v_x_529_ = lean_ctor_get(v_t_498_, 0);
lean_inc(v_x_529_);
v_c_u2081_530_ = lean_ctor_get(v_t_498_, 1);
lean_inc_ref(v_c_u2081_530_);
v_c_u2082_531_ = lean_ctor_get(v_t_498_, 2);
lean_inc_ref(v_c_u2082_531_);
lean_dec_ref_known(v_t_498_, 3);
v___x_532_ = lean_apply_3(v_k_499_, v_x_529_, v_c_u2081_530_, v_c_u2082_531_);
return v___x_532_;
}
case 13:
{
lean_object* v_c_u2081_533_; lean_object* v_c_u2082_534_; lean_object* v___x_535_; 
v_c_u2081_533_ = lean_ctor_get(v_t_498_, 0);
lean_inc_ref(v_c_u2081_533_);
v_c_u2082_534_ = lean_ctor_get(v_t_498_, 1);
lean_inc_ref(v_c_u2082_534_);
lean_dec_ref_known(v_t_498_, 2);
v___x_535_ = lean_apply_2(v_k_499_, v_c_u2081_533_, v_c_u2082_534_);
return v___x_535_;
}
case 14:
{
lean_object* v_c_u2081_536_; lean_object* v_decVar_537_; lean_object* v_h_538_; lean_object* v_decVars_539_; lean_object* v___x_540_; 
v_c_u2081_536_ = lean_ctor_get(v_t_498_, 0);
lean_inc_ref(v_c_u2081_536_);
v_decVar_537_ = lean_ctor_get(v_t_498_, 1);
lean_inc(v_decVar_537_);
v_h_538_ = lean_ctor_get(v_t_498_, 2);
lean_inc_ref(v_h_538_);
v_decVars_539_ = lean_ctor_get(v_t_498_, 3);
lean_inc_ref(v_decVars_539_);
lean_dec_ref_known(v_t_498_, 4);
v___x_540_ = lean_apply_4(v_k_499_, v_c_u2081_536_, v_decVar_537_, v_h_538_, v_decVars_539_);
return v___x_540_;
}
case 16:
{
lean_object* v_c_u2081_541_; lean_object* v_c_u2082_542_; lean_object* v_t_543_; lean_object* v_g_544_; lean_object* v___x_545_; 
v_c_u2081_541_ = lean_ctor_get(v_t_498_, 0);
lean_inc_ref(v_c_u2081_541_);
v_c_u2082_542_ = lean_ctor_get(v_t_498_, 1);
lean_inc_ref(v_c_u2082_542_);
v_t_543_ = lean_ctor_get(v_t_498_, 2);
lean_inc(v_t_543_);
v_g_544_ = lean_ctor_get(v_t_498_, 3);
lean_inc(v_g_544_);
lean_dec_ref_known(v_t_498_, 4);
v___x_545_ = lean_apply_4(v_k_499_, v_c_u2081_541_, v_c_u2082_542_, v_t_543_, v_g_544_);
return v___x_545_;
}
case 18:
{
lean_object* v_c_546_; lean_object* v_e_547_; lean_object* v_p_548_; lean_object* v___x_549_; 
v_c_546_ = lean_ctor_get(v_t_498_, 0);
lean_inc_ref(v_c_546_);
v_e_547_ = lean_ctor_get(v_t_498_, 1);
lean_inc_ref(v_e_547_);
v_p_548_ = lean_ctor_get(v_t_498_, 2);
lean_inc_ref(v_p_548_);
lean_dec_ref_known(v_t_498_, 3);
v___x_549_ = lean_apply_3(v_k_499_, v_c_546_, v_e_547_, v_p_548_);
return v___x_549_;
}
default: 
{
lean_object* v_e_550_; lean_object* v___x_551_; 
v_e_550_ = lean_ctor_get(v_t_498_, 0);
lean_inc_ref(v_e_550_);
lean_dec_ref(v_t_498_);
v___x_551_ = lean_apply_1(v_k_499_, v_e_550_);
return v___x_551_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim(lean_object* v_motive__9_552_, lean_object* v_ctorIdx_553_, lean_object* v_t_554_, lean_object* v_h_555_, lean_object* v_k_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_554_, v_k_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___boxed(lean_object* v_motive__9_558_, lean_object* v_ctorIdx_559_, lean_object* v_t_560_, lean_object* v_h_561_, lean_object* v_k_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim(v_motive__9_558_, v_ctorIdx_559_, v_t_560_, v_h_561_, v_k_562_);
lean_dec(v_ctorIdx_559_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_core_elim___redArg(lean_object* v_t_564_, lean_object* v_core_565_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_564_, v_core_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_core_elim(lean_object* v_motive__9_567_, lean_object* v_t_568_, lean_object* v_h_569_, lean_object* v_core_570_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_568_, v_core_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreNeg_elim___redArg(lean_object* v_t_572_, lean_object* v_coreNeg_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_572_, v_coreNeg_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreNeg_elim(lean_object* v_motive__9_575_, lean_object* v_t_576_, lean_object* v_h_577_, lean_object* v_coreNeg_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_576_, v_coreNeg_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreToInt_elim___redArg(lean_object* v_t_580_, lean_object* v_coreToInt_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_580_, v_coreToInt_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreToInt_elim(lean_object* v_motive__9_583_, lean_object* v_t_584_, lean_object* v_h_585_, lean_object* v_coreToInt_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_584_, v_coreToInt_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreExpr_elim___redArg(lean_object* v_t_588_, lean_object* v_coreExpr_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_588_, v_coreExpr_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreExpr_elim(lean_object* v_motive__9_591_, lean_object* v_t_592_, lean_object* v_h_593_, lean_object* v_coreExpr_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_592_, v_coreExpr_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofNatNonneg_elim___redArg(lean_object* v_t_596_, lean_object* v_ofNatNonneg_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_596_, v_ofNatNonneg_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofNatNonneg_elim(lean_object* v_motive__9_599_, lean_object* v_t_600_, lean_object* v_h_601_, lean_object* v_ofNatNonneg_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_600_, v_ofNatNonneg_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_hyp_elim___redArg(lean_object* v_t_604_, lean_object* v_hyp_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_604_, v_hyp_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_hyp_elim(lean_object* v_motive__9_607_, lean_object* v_t_608_, lean_object* v_h_609_, lean_object* v_hyp_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_608_, v_hyp_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_bound_elim___redArg(lean_object* v_t_612_, lean_object* v_bound_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_612_, v_bound_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_bound_elim(lean_object* v_motive__9_615_, lean_object* v_t_616_, lean_object* v_h_617_, lean_object* v_bound_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_616_, v_bound_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dec_elim___redArg(lean_object* v_t_620_, lean_object* v_dec_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_620_, v_dec_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dec_elim(lean_object* v_motive__9_623_, lean_object* v_t_624_, lean_object* v_h_625_, lean_object* v_dec_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_624_, v_dec_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_norm_elim___redArg(lean_object* v_t_628_, lean_object* v_norm_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_628_, v_norm_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_norm_elim(lean_object* v_motive__9_631_, lean_object* v_t_632_, lean_object* v_h_633_, lean_object* v_norm_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_632_, v_norm_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_divCoeffs_elim___redArg(lean_object* v_t_636_, lean_object* v_divCoeffs_637_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_636_, v_divCoeffs_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_divCoeffs_elim(lean_object* v_motive__9_639_, lean_object* v_t_640_, lean_object* v_h_641_, lean_object* v_divCoeffs_642_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_640_, v_divCoeffs_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combine_elim___redArg(lean_object* v_t_644_, lean_object* v_combine_645_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_644_, v_combine_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combine_elim(lean_object* v_motive__9_647_, lean_object* v_t_648_, lean_object* v_h_649_, lean_object* v_combine_650_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_648_, v_combine_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combineDivCoeffs_elim___redArg(lean_object* v_t_652_, lean_object* v_combineDivCoeffs_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_652_, v_combineDivCoeffs_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combineDivCoeffs_elim(lean_object* v_motive__9_655_, lean_object* v_t_656_, lean_object* v_h_657_, lean_object* v_combineDivCoeffs_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_656_, v_combineDivCoeffs_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_subst_elim___redArg(lean_object* v_t_660_, lean_object* v_subst_661_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_660_, v_subst_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_subst_elim(lean_object* v_motive__9_663_, lean_object* v_t_664_, lean_object* v_h_665_, lean_object* v_subst_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_664_, v_subst_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofLeDiseq_elim___redArg(lean_object* v_t_668_, lean_object* v_ofLeDiseq_669_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_668_, v_ofLeDiseq_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofLeDiseq_elim(lean_object* v_motive__9_671_, lean_object* v_t_672_, lean_object* v_h_673_, lean_object* v_ofLeDiseq_674_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_672_, v_ofLeDiseq_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofDiseqSplit_elim___redArg(lean_object* v_t_676_, lean_object* v_ofDiseqSplit_677_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_676_, v_ofDiseqSplit_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofDiseqSplit_elim(lean_object* v_motive__9_679_, lean_object* v_t_680_, lean_object* v_h_681_, lean_object* v_ofDiseqSplit_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_680_, v_ofDiseqSplit_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_cooper_elim___redArg(lean_object* v_t_684_, lean_object* v_cooper_685_){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_684_, v_cooper_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_cooper_elim(lean_object* v_motive__9_687_, lean_object* v_t_688_, lean_object* v_h_689_, lean_object* v_cooper_690_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_688_, v_cooper_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dvdTightMod_elim___redArg(lean_object* v_t_692_, lean_object* v_dvdTightMod_693_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_692_, v_dvdTightMod_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dvdTightMod_elim(lean_object* v_motive__9_695_, lean_object* v_t_696_, lean_object* v_h_697_, lean_object* v_dvdTightMod_698_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_696_, v_dvdTightMod_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_reorder_elim___redArg(lean_object* v_t_700_, lean_object* v_reorder_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_700_, v_reorder_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_reorder_elim(lean_object* v_motive__9_703_, lean_object* v_t_704_, lean_object* v_h_705_, lean_object* v_reorder_706_){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_704_, v_reorder_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_commRingNorm_elim___redArg(lean_object* v_t_708_, lean_object* v_commRingNorm_709_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_708_, v_commRingNorm_709_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_commRingNorm_elim(lean_object* v_motive__9_711_, lean_object* v_t_712_, lean_object* v_h_713_, lean_object* v_commRingNorm_714_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_712_, v_commRingNorm_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorIdx___impl(lean_object* v_x_716_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = lean_obj_tag_nat(v_x_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorIdx___impl___boxed(lean_object* v_x_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorIdx___impl(v_x_718_);
lean_dec_ref(v_x_718_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(lean_object* v_t_720_, lean_object* v_k_721_){
_start:
{
switch(lean_obj_tag(v_t_720_))
{
case 0:
{
lean_object* v_a_722_; lean_object* v_zero_723_; lean_object* v___x_724_; 
v_a_722_ = lean_ctor_get(v_t_720_, 0);
lean_inc_ref(v_a_722_);
v_zero_723_ = lean_ctor_get(v_t_720_, 1);
lean_inc_ref(v_zero_723_);
lean_dec_ref_known(v_t_720_, 2);
v___x_724_ = lean_apply_2(v_k_721_, v_a_722_, v_zero_723_);
return v___x_724_;
}
case 1:
{
lean_object* v_a_725_; lean_object* v_b_726_; lean_object* v_p_u2081_727_; lean_object* v_p_u2082_728_; lean_object* v___x_729_; 
v_a_725_ = lean_ctor_get(v_t_720_, 0);
lean_inc_ref(v_a_725_);
v_b_726_ = lean_ctor_get(v_t_720_, 1);
lean_inc_ref(v_b_726_);
v_p_u2081_727_ = lean_ctor_get(v_t_720_, 2);
lean_inc_ref(v_p_u2081_727_);
v_p_u2082_728_ = lean_ctor_get(v_t_720_, 3);
lean_inc_ref(v_p_u2082_728_);
lean_dec_ref_known(v_t_720_, 4);
v___x_729_ = lean_apply_4(v_k_721_, v_a_725_, v_b_726_, v_p_u2081_727_, v_p_u2082_728_);
return v___x_729_;
}
case 2:
{
lean_object* v_a_730_; lean_object* v_b_731_; lean_object* v_toIntThm_732_; lean_object* v_lhs_733_; lean_object* v_rhs_734_; lean_object* v___x_735_; 
v_a_730_ = lean_ctor_get(v_t_720_, 0);
lean_inc_ref(v_a_730_);
v_b_731_ = lean_ctor_get(v_t_720_, 1);
lean_inc_ref(v_b_731_);
v_toIntThm_732_ = lean_ctor_get(v_t_720_, 2);
lean_inc_ref(v_toIntThm_732_);
v_lhs_733_ = lean_ctor_get(v_t_720_, 3);
lean_inc_ref(v_lhs_733_);
v_rhs_734_ = lean_ctor_get(v_t_720_, 4);
lean_inc_ref(v_rhs_734_);
lean_dec_ref_known(v_t_720_, 5);
v___x_735_ = lean_apply_5(v_k_721_, v_a_730_, v_b_731_, v_toIntThm_732_, v_lhs_733_, v_rhs_734_);
return v___x_735_;
}
case 6:
{
lean_object* v_x_736_; lean_object* v_c_u2081_737_; lean_object* v_c_u2082_738_; lean_object* v___x_739_; 
v_x_736_ = lean_ctor_get(v_t_720_, 0);
lean_inc(v_x_736_);
v_c_u2081_737_ = lean_ctor_get(v_t_720_, 1);
lean_inc_ref(v_c_u2081_737_);
v_c_u2082_738_ = lean_ctor_get(v_t_720_, 2);
lean_inc_ref(v_c_u2082_738_);
lean_dec_ref_known(v_t_720_, 3);
v___x_739_ = lean_apply_3(v_k_721_, v_x_736_, v_c_u2081_737_, v_c_u2082_738_);
return v___x_739_;
}
case 8:
{
lean_object* v_c_740_; lean_object* v_e_741_; lean_object* v_p_742_; lean_object* v___x_743_; 
v_c_740_ = lean_ctor_get(v_t_720_, 0);
lean_inc_ref(v_c_740_);
v_e_741_ = lean_ctor_get(v_t_720_, 1);
lean_inc_ref(v_e_741_);
v_p_742_ = lean_ctor_get(v_t_720_, 2);
lean_inc_ref(v_p_742_);
lean_dec_ref_known(v_t_720_, 3);
v___x_743_ = lean_apply_3(v_k_721_, v_c_740_, v_e_741_, v_p_742_);
return v___x_743_;
}
default: 
{
lean_object* v_c_744_; lean_object* v___x_745_; 
v_c_744_ = lean_ctor_get(v_t_720_, 0);
lean_inc_ref(v_c_744_);
lean_dec_ref(v_t_720_);
v___x_745_ = lean_apply_1(v_k_721_, v_c_744_);
return v___x_745_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim(lean_object* v_motive__11_746_, lean_object* v_ctorIdx_747_, lean_object* v_t_748_, lean_object* v_h_749_, lean_object* v_k_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_748_, v_k_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___boxed(lean_object* v_motive__11_752_, lean_object* v_ctorIdx_753_, lean_object* v_t_754_, lean_object* v_h_755_, lean_object* v_k_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim(v_motive__11_752_, v_ctorIdx_753_, v_t_754_, v_h_755_, v_k_756_);
lean_dec(v_ctorIdx_753_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core0_elim___redArg(lean_object* v_t_758_, lean_object* v_core0_759_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_758_, v_core0_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core0_elim(lean_object* v_motive__11_761_, lean_object* v_t_762_, lean_object* v_h_763_, lean_object* v_core0_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_762_, v_core0_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core_elim___redArg(lean_object* v_t_766_, lean_object* v_core_767_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_766_, v_core_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core_elim(lean_object* v_motive__11_769_, lean_object* v_t_770_, lean_object* v_h_771_, lean_object* v_core_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_770_, v_core_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_coreToInt_elim___redArg(lean_object* v_t_774_, lean_object* v_coreToInt_775_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_774_, v_coreToInt_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_coreToInt_elim(lean_object* v_motive__11_777_, lean_object* v_t_778_, lean_object* v_h_779_, lean_object* v_coreToInt_780_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_778_, v_coreToInt_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_norm_elim___redArg(lean_object* v_t_782_, lean_object* v_norm_783_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_782_, v_norm_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_norm_elim(lean_object* v_motive__11_785_, lean_object* v_t_786_, lean_object* v_h_787_, lean_object* v_norm_788_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_786_, v_norm_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_divCoeffs_elim___redArg(lean_object* v_t_790_, lean_object* v_divCoeffs_791_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_790_, v_divCoeffs_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_divCoeffs_elim(lean_object* v_motive__11_793_, lean_object* v_t_794_, lean_object* v_h_795_, lean_object* v_divCoeffs_796_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_794_, v_divCoeffs_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_neg_elim___redArg(lean_object* v_t_798_, lean_object* v_neg_799_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_798_, v_neg_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_neg_elim(lean_object* v_motive__11_801_, lean_object* v_t_802_, lean_object* v_h_803_, lean_object* v_neg_804_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_802_, v_neg_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_subst_elim___redArg(lean_object* v_t_806_, lean_object* v_subst_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_806_, v_subst_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_subst_elim(lean_object* v_motive__11_809_, lean_object* v_t_810_, lean_object* v_h_811_, lean_object* v_subst_812_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_810_, v_subst_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_reorder_elim___redArg(lean_object* v_t_814_, lean_object* v_reorder_815_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_814_, v_reorder_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_reorder_elim(lean_object* v_motive__11_817_, lean_object* v_t_818_, lean_object* v_h_819_, lean_object* v_reorder_820_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_818_, v_reorder_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_commRingNorm_elim___redArg(lean_object* v_t_822_, lean_object* v_commRingNorm_823_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_822_, v_commRingNorm_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_commRingNorm_elim(lean_object* v_motive__11_825_, lean_object* v_t_826_, lean_object* v_h_827_, lean_object* v_commRingNorm_828_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_826_, v_commRingNorm_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorIdx___impl(lean_object* v_x_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = lean_obj_tag_nat(v_x_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorIdx___impl___boxed(lean_object* v_x_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorIdx___impl(v_x_832_);
lean_dec_ref(v_x_832_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(lean_object* v_t_834_, lean_object* v_k_835_){
_start:
{
if (lean_obj_tag(v_t_834_) == 4)
{
lean_object* v_c_u2081_836_; lean_object* v_c_u2082_837_; lean_object* v_c_u2083_838_; lean_object* v___x_839_; 
v_c_u2081_836_ = lean_ctor_get(v_t_834_, 0);
lean_inc_ref(v_c_u2081_836_);
v_c_u2082_837_ = lean_ctor_get(v_t_834_, 1);
lean_inc_ref(v_c_u2082_837_);
v_c_u2083_838_ = lean_ctor_get(v_t_834_, 2);
lean_inc_ref(v_c_u2083_838_);
lean_dec_ref_known(v_t_834_, 3);
v___x_839_ = lean_apply_3(v_k_835_, v_c_u2081_836_, v_c_u2082_837_, v_c_u2083_838_);
return v___x_839_;
}
else
{
lean_object* v_c_840_; lean_object* v___x_841_; 
v_c_840_ = lean_ctor_get(v_t_834_, 0);
lean_inc_ref(v_c_840_);
lean_dec_ref(v_t_834_);
v___x_841_ = lean_apply_1(v_k_835_, v_c_840_);
return v___x_841_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim(lean_object* v_motive__12_842_, lean_object* v_ctorIdx_843_, lean_object* v_t_844_, lean_object* v_h_845_, lean_object* v_k_846_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_844_, v_k_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___boxed(lean_object* v_motive__12_848_, lean_object* v_ctorIdx_849_, lean_object* v_t_850_, lean_object* v_h_851_, lean_object* v_k_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim(v_motive__12_848_, v_ctorIdx_849_, v_t_850_, v_h_851_, v_k_852_);
lean_dec(v_ctorIdx_849_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_dvd_elim___redArg(lean_object* v_t_854_, lean_object* v_dvd_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_854_, v_dvd_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_dvd_elim(lean_object* v_motive__12_857_, lean_object* v_t_858_, lean_object* v_h_859_, lean_object* v_dvd_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_858_, v_dvd_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_le_elim___redArg(lean_object* v_t_862_, lean_object* v_le_863_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_862_, v_le_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_le_elim(lean_object* v_motive__12_865_, lean_object* v_t_866_, lean_object* v_h_867_, lean_object* v_le_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_866_, v_le_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_eq_elim___redArg(lean_object* v_t_870_, lean_object* v_eq_871_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_870_, v_eq_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_eq_elim(lean_object* v_motive__12_873_, lean_object* v_t_874_, lean_object* v_h_875_, lean_object* v_eq_876_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_874_, v_eq_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_diseq_elim___redArg(lean_object* v_t_878_, lean_object* v_diseq_879_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_878_, v_diseq_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_diseq_elim(lean_object* v_motive__12_881_, lean_object* v_t_882_, lean_object* v_h_883_, lean_object* v_diseq_884_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_882_, v_diseq_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_cooper_elim___redArg(lean_object* v_t_886_, lean_object* v_cooper_887_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_886_, v_cooper_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_cooper_elim(lean_object* v_motive__12_889_, lean_object* v_t_890_, lean_object* v_h_891_, lean_object* v_cooper_892_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_890_, v_cooper_892_);
return v___x_893_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0(void){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_894_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0);
v___x_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
return v___x_895_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_899_ = lean_box(0);
v___x_900_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__2));
v___x_901_ = l_Lean_Expr_const___override(v___x_900_, v___x_899_);
return v___x_901_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_902_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3);
v___x_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_903_, 0, v___x_902_);
return v___x_903_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_904_ = lean_box(0);
v___x_905_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4);
v___x_906_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0);
v___x_907_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
lean_ctor_set(v___x_907_, 1, v___x_905_);
lean_ctor_set(v___x_907_, 2, v___x_904_);
return v___x_907_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr(void){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5);
return v___x_908_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0(void){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_909_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3);
v___x_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_910_, 0, v___x_909_);
return v___x_910_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1(void){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_911_ = lean_box(0);
v___x_912_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0);
v___x_913_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0);
v___x_914_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0);
v___x_915_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
lean_ctor_set(v___x_915_, 1, v___x_913_);
lean_ctor_set(v___x_915_, 2, v___x_912_);
lean_ctor_set(v___x_915_, 3, v___x_911_);
return v___x_915_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr(void){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1);
return v___x_916_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0(void){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; uint8_t v___x_919_; lean_object* v___x_920_; 
v___x_917_ = lean_box(0);
v___x_918_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5);
v___x_919_ = 0;
v___x_920_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_920_, 0, v___x_918_);
lean_ctor_set(v___x_920_, 1, v___x_918_);
lean_ctor_set(v___x_920_, 2, v___x_917_);
lean_ctor_set_uint8(v___x_920_, sizeof(void*)*3, v___x_919_);
return v___x_920_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred(void){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0);
return v___x_921_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1(void){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_924_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__0));
v___x_925_ = lean_unsigned_to_nat(0u);
v___x_926_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0);
v___x_927_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
lean_ctor_set(v___x_927_, 1, v___x_925_);
lean_ctor_set(v___x_927_, 2, v___x_924_);
return v___x_927_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit(void){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1);
return v___x_928_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_929_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_930_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0);
v___x_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_931_, 0, v___x_930_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg(){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__1);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___boxed(lean_object* v___dummy_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg();
return v_res_935_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg();
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0(lean_object* v_00_u03b2_937_){
_start:
{
lean_object* v___x_938_; 
v___x_938_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0);
return v___x_938_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0(void){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_939_ = lean_unsigned_to_nat(32u);
v___x_940_ = lean_mk_empty_array_with_capacity(v___x_939_);
v___x_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
return v___x_941_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1(void){
_start:
{
size_t v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_942_ = ((size_t)5ULL);
v___x_943_ = lean_unsigned_to_nat(0u);
v___x_944_ = lean_unsigned_to_nat(32u);
v___x_945_ = lean_mk_empty_array_with_capacity(v___x_944_);
v___x_946_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0);
v___x_947_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_947_, 0, v___x_946_);
lean_ctor_set(v___x_947_, 1, v___x_945_);
lean_ctor_set(v___x_947_, 2, v___x_943_);
lean_ctor_set(v___x_947_, 3, v___x_943_);
lean_ctor_set_usize(v___x_947_, 4, v___x_942_);
return v___x_947_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2(void){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0);
v___x_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
return v___x_949_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; uint8_t v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_950_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0);
v___x_951_ = lean_box(0);
v___x_952_ = 0;
v___x_953_ = lean_unsigned_to_nat(0u);
v___x_954_ = lean_box(0);
v___x_955_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2);
v___x_956_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1);
v___x_957_ = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(v___x_957_, 0, v___x_956_);
lean_ctor_set(v___x_957_, 1, v___x_955_);
lean_ctor_set(v___x_957_, 2, v___x_956_);
lean_ctor_set(v___x_957_, 3, v___x_955_);
lean_ctor_set(v___x_957_, 4, v___x_955_);
lean_ctor_set(v___x_957_, 5, v___x_956_);
lean_ctor_set(v___x_957_, 6, v___x_956_);
lean_ctor_set(v___x_957_, 7, v___x_956_);
lean_ctor_set(v___x_957_, 8, v___x_956_);
lean_ctor_set(v___x_957_, 9, v___x_956_);
lean_ctor_set(v___x_957_, 10, v___x_954_);
lean_ctor_set(v___x_957_, 11, v___x_956_);
lean_ctor_set(v___x_957_, 12, v___x_956_);
lean_ctor_set(v___x_957_, 13, v___x_953_);
lean_ctor_set(v___x_957_, 14, v___x_953_);
lean_ctor_set(v___x_957_, 15, v___x_955_);
lean_ctor_set(v___x_957_, 16, v___x_953_);
lean_ctor_set(v___x_957_, 17, v___x_951_);
lean_ctor_set(v___x_957_, 18, v___x_955_);
lean_ctor_set(v___x_957_, 19, v___x_950_);
lean_ctor_set(v___x_957_, 20, v___x_955_);
lean_ctor_set_uint8(v___x_957_, sizeof(void*)*21, v___x_952_);
lean_ctor_set_uint8(v___x_957_, sizeof(void*)*21 + 1, v___x_952_);
return v___x_957_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default(void){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3);
return v___x_958_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState(void){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default;
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(lean_object* v___x_960_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_962_, 0, v___x_960_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2____boxed(lean_object* v___x_963_, lean_object* v___y_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(v___x_963_);
return v_res_965_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_966_; lean_object* v___f_967_; 
v___x_966_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3);
v___f_967_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_967_, 0, v___x_966_);
return v___f_967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_969_; lean_object* v___x_970_; 
v___f_969_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_);
v___x_970_ = l_Lean_Meta_Grind_registerSolverExtension___redArg(v___f_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2____boxed(lean_object* v_a_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_();
return v_res_972_;
}
}
lean_object* runtime_initialize_Init_Data_Int_Linear(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Int_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Int_Linear(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Int_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
}
#ifdef __cplusplus
}
#endif
