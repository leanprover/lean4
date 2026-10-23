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
lean_object* v_e_70_; lean_object* v_p_71_; lean_object* v___x_72_; 
v_e_70_ = lean_ctor_get(v_t_54_, 0);
lean_inc_ref(v_e_70_);
v_p_71_ = lean_ctor_get(v_t_54_, 1);
lean_inc_ref(v_p_71_);
lean_dec_ref_known(v_t_54_, 2);
v___x_72_ = lean_apply_2(v_k_55_, v_e_70_, v_p_71_);
return v___x_72_;
}
case 4:
{
lean_object* v_h_73_; lean_object* v_x_74_; lean_object* v_e_x27_75_; lean_object* v___x_76_; 
v_h_73_ = lean_ctor_get(v_t_54_, 0);
lean_inc_ref(v_h_73_);
v_x_74_ = lean_ctor_get(v_t_54_, 1);
lean_inc(v_x_74_);
v_e_x27_75_ = lean_ctor_get(v_t_54_, 2);
lean_inc_ref(v_e_x27_75_);
lean_dec_ref_known(v_t_54_, 3);
v___x_76_ = lean_apply_3(v_k_55_, v_h_73_, v_x_74_, v_e_x27_75_);
return v___x_76_;
}
case 7:
{
lean_object* v_x_77_; lean_object* v_c_u2081_78_; lean_object* v_c_u2082_79_; lean_object* v___x_80_; 
v_x_77_ = lean_ctor_get(v_t_54_, 0);
lean_inc(v_x_77_);
v_c_u2081_78_ = lean_ctor_get(v_t_54_, 1);
lean_inc_ref(v_c_u2081_78_);
v_c_u2082_79_ = lean_ctor_get(v_t_54_, 2);
lean_inc_ref(v_c_u2082_79_);
lean_dec_ref_known(v_t_54_, 3);
v___x_80_ = lean_apply_3(v_k_55_, v_x_77_, v_c_u2081_78_, v_c_u2082_79_);
return v___x_80_;
}
case 8:
{
lean_object* v_c_u2081_81_; lean_object* v_c_u2082_82_; lean_object* v___x_83_; 
v_c_u2081_81_ = lean_ctor_get(v_t_54_, 0);
lean_inc_ref(v_c_u2081_81_);
v_c_u2082_82_ = lean_ctor_get(v_t_54_, 1);
lean_inc_ref(v_c_u2082_82_);
lean_dec_ref_known(v_t_54_, 2);
v___x_83_ = lean_apply_2(v_k_55_, v_c_u2081_81_, v_c_u2082_82_);
return v___x_83_;
}
case 10:
{
lean_object* v_c_84_; lean_object* v_e_85_; lean_object* v_x_86_; lean_object* v_t_87_; lean_object* v___x_88_; 
v_c_84_ = lean_ctor_get(v_t_54_, 0);
lean_inc_ref(v_c_84_);
v_e_85_ = lean_ctor_get(v_t_54_, 1);
lean_inc_ref(v_e_85_);
v_x_86_ = lean_ctor_get(v_t_54_, 2);
lean_inc(v_x_86_);
v_t_87_ = lean_ctor_get(v_t_54_, 3);
lean_inc_ref(v_t_87_);
lean_dec_ref_known(v_t_54_, 4);
v___x_88_ = lean_apply_4(v_k_55_, v_c_84_, v_e_85_, v_x_86_, v_t_87_);
return v___x_88_;
}
case 12:
{
lean_object* v_c_89_; lean_object* v_e_90_; lean_object* v_p_91_; lean_object* v___x_92_; 
v_c_89_ = lean_ctor_get(v_t_54_, 0);
lean_inc_ref(v_c_89_);
v_e_90_ = lean_ctor_get(v_t_54_, 1);
lean_inc_ref(v_e_90_);
v_p_91_ = lean_ctor_get(v_t_54_, 2);
lean_inc_ref(v_p_91_);
lean_dec_ref_known(v_t_54_, 3);
v___x_92_ = lean_apply_3(v_k_55_, v_c_89_, v_e_90_, v_p_91_);
return v___x_92_;
}
case 13:
{
lean_object* v_e_93_; lean_object* v_p_94_; lean_object* v_re_95_; lean_object* v_rp_96_; lean_object* v_p_x27_97_; lean_object* v___x_98_; 
v_e_93_ = lean_ctor_get(v_t_54_, 0);
lean_inc_ref(v_e_93_);
v_p_94_ = lean_ctor_get(v_t_54_, 1);
lean_inc_ref(v_p_94_);
v_re_95_ = lean_ctor_get(v_t_54_, 2);
lean_inc_ref(v_re_95_);
v_rp_96_ = lean_ctor_get(v_t_54_, 3);
lean_inc_ref(v_rp_96_);
v_p_x27_97_ = lean_ctor_get(v_t_54_, 4);
lean_inc_ref(v_p_x27_97_);
lean_dec_ref_known(v_t_54_, 5);
v___x_98_ = lean_apply_5(v_k_55_, v_e_93_, v_p_94_, v_re_95_, v_rp_96_, v_p_x27_97_);
return v___x_98_;
}
case 14:
{
lean_object* v_h_99_; lean_object* v_x_100_; lean_object* v_e_x27_101_; lean_object* v_p_102_; lean_object* v_re_103_; lean_object* v_rp_104_; lean_object* v_p_x27_105_; lean_object* v___x_106_; 
v_h_99_ = lean_ctor_get(v_t_54_, 0);
lean_inc_ref(v_h_99_);
v_x_100_ = lean_ctor_get(v_t_54_, 1);
lean_inc(v_x_100_);
v_e_x27_101_ = lean_ctor_get(v_t_54_, 2);
lean_inc_ref(v_e_x27_101_);
v_p_102_ = lean_ctor_get(v_t_54_, 3);
lean_inc_ref(v_p_102_);
v_re_103_ = lean_ctor_get(v_t_54_, 4);
lean_inc_ref(v_re_103_);
v_rp_104_ = lean_ctor_get(v_t_54_, 5);
lean_inc_ref(v_rp_104_);
v_p_x27_105_ = lean_ctor_get(v_t_54_, 6);
lean_inc_ref(v_p_x27_105_);
lean_dec_ref_known(v_t_54_, 7);
v___x_106_ = lean_apply_7(v_k_55_, v_h_99_, v_x_100_, v_e_x27_101_, v_p_102_, v_re_103_, v_rp_104_, v_p_x27_105_);
return v___x_106_;
}
case 15:
{
lean_object* v_a_x3f_107_; lean_object* v_cs_108_; lean_object* v___x_109_; 
v_a_x3f_107_ = lean_ctor_get(v_t_54_, 0);
lean_inc(v_a_x3f_107_);
v_cs_108_ = lean_ctor_get(v_t_54_, 1);
lean_inc_ref(v_cs_108_);
lean_dec_ref_known(v_t_54_, 2);
v___x_109_ = lean_apply_2(v_k_55_, v_a_x3f_107_, v_cs_108_);
return v___x_109_;
}
case 16:
{
lean_object* v_k_110_; lean_object* v_y_x3f_111_; lean_object* v_c_112_; lean_object* v___x_113_; 
v_k_110_ = lean_ctor_get(v_t_54_, 0);
lean_inc(v_k_110_);
v_y_x3f_111_ = lean_ctor_get(v_t_54_, 1);
lean_inc(v_y_x3f_111_);
v_c_112_ = lean_ctor_get(v_t_54_, 2);
lean_inc_ref(v_c_112_);
lean_dec_ref_known(v_t_54_, 3);
v___x_113_ = lean_apply_3(v_k_55_, v_k_110_, v_y_x3f_111_, v_c_112_);
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
lean_object* v_ka_118_; lean_object* v_ca_x3f_119_; lean_object* v_kb_120_; lean_object* v_cb_x3f_121_; lean_object* v___x_122_; 
v_ka_118_ = lean_ctor_get(v_t_54_, 0);
lean_inc(v_ka_118_);
v_ca_x3f_119_ = lean_ctor_get(v_t_54_, 1);
lean_inc(v_ca_x3f_119_);
v_kb_120_ = lean_ctor_get(v_t_54_, 2);
lean_inc(v_kb_120_);
v_cb_x3f_121_ = lean_ctor_get(v_t_54_, 3);
lean_inc(v_cb_x3f_121_);
lean_dec_ref_known(v_t_54_, 4);
v___x_122_ = lean_apply_4(v_k_55_, v_ka_118_, v_ca_x3f_119_, v_kb_120_, v_cb_x3f_121_);
return v___x_122_;
}
default: 
{
lean_object* v_c_123_; lean_object* v___x_124_; 
v_c_123_ = lean_ctor_get(v_t_54_, 0);
lean_inc_ref(v_c_123_);
lean_dec_ref(v_t_54_);
v___x_124_ = lean_apply_1(v_k_55_, v_c_123_);
return v___x_124_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim(lean_object* v_motive__2_125_, lean_object* v_ctorIdx_126_, lean_object* v_t_127_, lean_object* v_h_128_, lean_object* v_k_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_127_, v_k_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___boxed(lean_object* v_motive__2_131_, lean_object* v_ctorIdx_132_, lean_object* v_t_133_, lean_object* v_h_134_, lean_object* v_k_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim(v_motive__2_131_, v_ctorIdx_132_, v_t_133_, v_h_134_, v_k_135_);
lean_dec(v_ctorIdx_132_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core0_elim___redArg(lean_object* v_t_137_, lean_object* v_core0_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_137_, v_core0_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core0_elim(lean_object* v_motive__2_140_, lean_object* v_t_141_, lean_object* v_h_142_, lean_object* v_core0_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_141_, v_core0_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core_elim___redArg(lean_object* v_t_145_, lean_object* v_core_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_145_, v_core_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core_elim(lean_object* v_motive__2_148_, lean_object* v_t_149_, lean_object* v_h_150_, lean_object* v_core_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_149_, v_core_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_coreToInt_elim___redArg(lean_object* v_t_153_, lean_object* v_coreToInt_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_153_, v_coreToInt_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_coreToInt_elim(lean_object* v_motive__2_156_, lean_object* v_t_157_, lean_object* v_h_158_, lean_object* v_coreToInt_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_157_, v_coreToInt_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defn_elim___redArg(lean_object* v_t_161_, lean_object* v_defn_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_161_, v_defn_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defn_elim(lean_object* v_motive__2_164_, lean_object* v_t_165_, lean_object* v_h_166_, lean_object* v_defn_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_165_, v_defn_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnExpr_elim___redArg(lean_object* v_t_169_, lean_object* v_defnExpr_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_169_, v_defnExpr_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnExpr_elim(lean_object* v_motive__2_172_, lean_object* v_t_173_, lean_object* v_h_174_, lean_object* v_defnExpr_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_173_, v_defnExpr_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_norm_elim___redArg(lean_object* v_t_177_, lean_object* v_norm_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_177_, v_norm_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_norm_elim(lean_object* v_motive__2_180_, lean_object* v_t_181_, lean_object* v_h_182_, lean_object* v_norm_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_181_, v_norm_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_divCoeffs_elim___redArg(lean_object* v_t_185_, lean_object* v_divCoeffs_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_185_, v_divCoeffs_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_divCoeffs_elim(lean_object* v_motive__2_188_, lean_object* v_t_189_, lean_object* v_h_190_, lean_object* v_divCoeffs_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_189_, v_divCoeffs_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_subst_elim___redArg(lean_object* v_t_193_, lean_object* v_subst_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_193_, v_subst_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_subst_elim(lean_object* v_motive__2_196_, lean_object* v_t_197_, lean_object* v_h_198_, lean_object* v_subst_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_197_, v_subst_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofLeGe_elim___redArg(lean_object* v_t_201_, lean_object* v_ofLeGe_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_201_, v_ofLeGe_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofLeGe_elim(lean_object* v_motive__2_204_, lean_object* v_t_205_, lean_object* v_h_206_, lean_object* v_ofLeGe_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_205_, v_ofLeGe_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofZeroDvd_elim___redArg(lean_object* v_t_209_, lean_object* v_ofZeroDvd_210_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_209_, v_ofZeroDvd_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofZeroDvd_elim(lean_object* v_motive__2_212_, lean_object* v_t_213_, lean_object* v_h_214_, lean_object* v_ofZeroDvd_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_213_, v_ofZeroDvd_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofDvdDiv_elim___redArg(lean_object* v_t_217_, lean_object* v_ofDvdDiv_218_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_217_, v_ofDvdDiv_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofDvdDiv_elim(lean_object* v_motive__2_220_, lean_object* v_t_221_, lean_object* v_h_222_, lean_object* v_ofDvdDiv_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_221_, v_ofDvdDiv_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_reorder_elim___redArg(lean_object* v_t_225_, lean_object* v_reorder_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_225_, v_reorder_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_reorder_elim(lean_object* v_motive__2_228_, lean_object* v_t_229_, lean_object* v_h_230_, lean_object* v_reorder_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_229_, v_reorder_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_commRingNorm_elim___redArg(lean_object* v_t_233_, lean_object* v_commRingNorm_234_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_233_, v_commRingNorm_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_commRingNorm_elim(lean_object* v_motive__2_236_, lean_object* v_t_237_, lean_object* v_h_238_, lean_object* v_commRingNorm_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_237_, v_commRingNorm_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnCommRing_elim___redArg(lean_object* v_t_241_, lean_object* v_defnCommRing_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_241_, v_defnCommRing_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnCommRing_elim(lean_object* v_motive__2_244_, lean_object* v_t_245_, lean_object* v_h_246_, lean_object* v_defnCommRing_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_245_, v_defnCommRing_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnExprCommRing_elim___redArg(lean_object* v_t_249_, lean_object* v_defnExprCommRing_250_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_249_, v_defnExprCommRing_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnExprCommRing_elim(lean_object* v_motive__2_252_, lean_object* v_t_253_, lean_object* v_h_254_, lean_object* v_defnExprCommRing_255_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_253_, v_defnExprCommRing_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mul_elim___redArg(lean_object* v_t_257_, lean_object* v_mul_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_257_, v_mul_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mul_elim(lean_object* v_motive__2_260_, lean_object* v_t_261_, lean_object* v_h_262_, lean_object* v_mul_263_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_261_, v_mul_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_div_elim___redArg(lean_object* v_t_265_, lean_object* v_div_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_265_, v_div_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_div_elim(lean_object* v_motive__2_268_, lean_object* v_t_269_, lean_object* v_h_270_, lean_object* v_div_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_269_, v_div_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mod_elim___redArg(lean_object* v_t_273_, lean_object* v_mod_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_273_, v_mod_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mod_elim(lean_object* v_motive__2_276_, lean_object* v_t_277_, lean_object* v_h_278_, lean_object* v_mod_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_277_, v_mod_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_pow_elim___redArg(lean_object* v_t_281_, lean_object* v_pow_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_281_, v_pow_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_pow_elim(lean_object* v_motive__2_284_, lean_object* v_t_285_, lean_object* v_h_286_, lean_object* v_pow_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_285_, v_pow_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorIdx___impl(lean_object* v_x_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = lean_obj_tag_nat(v_x_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorIdx___impl___boxed(lean_object* v_x_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorIdx___impl(v_x_291_);
lean_dec_ref(v_x_291_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(lean_object* v_t_293_, lean_object* v_k_294_){
_start:
{
if (lean_obj_tag(v_t_293_) == 0)
{
lean_object* v_h_295_; lean_object* v___x_296_; 
v_h_295_ = lean_ctor_get(v_t_293_, 0);
lean_inc(v_h_295_);
lean_dec_ref_known(v_t_293_, 1);
v___x_296_ = lean_apply_1(v_k_294_, v_h_295_);
return v___x_296_;
}
else
{
lean_object* v_hs_297_; lean_object* v_decVars_298_; lean_object* v___x_299_; 
v_hs_297_ = lean_ctor_get(v_t_293_, 0);
lean_inc_ref(v_hs_297_);
v_decVars_298_ = lean_ctor_get(v_t_293_, 1);
lean_inc_ref(v_decVars_298_);
lean_dec_ref_known(v_t_293_, 2);
v___x_299_ = lean_apply_2(v_k_294_, v_hs_297_, v_decVars_298_);
return v___x_299_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim(lean_object* v_motive__6_300_, lean_object* v_ctorIdx_301_, lean_object* v_t_302_, lean_object* v_h_303_, lean_object* v_k_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_302_, v_k_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___boxed(lean_object* v_motive__6_306_, lean_object* v_ctorIdx_307_, lean_object* v_t_308_, lean_object* v_h_309_, lean_object* v_k_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim(v_motive__6_306_, v_ctorIdx_307_, v_t_308_, v_h_309_, v_k_310_);
lean_dec(v_ctorIdx_307_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_dec_elim___redArg(lean_object* v_t_312_, lean_object* v_dec_313_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_312_, v_dec_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_dec_elim(lean_object* v_motive__6_315_, lean_object* v_t_316_, lean_object* v_h_317_, lean_object* v_dec_318_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_316_, v_dec_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_last_elim___redArg(lean_object* v_t_320_, lean_object* v_last_321_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_320_, v_last_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_last_elim(lean_object* v_motive__6_323_, lean_object* v_t_324_, lean_object* v_h_325_, lean_object* v_last_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_324_, v_last_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorIdx___impl(lean_object* v_x_328_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = lean_obj_tag_nat(v_x_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorIdx___impl___boxed(lean_object* v_x_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorIdx___impl(v_x_330_);
lean_dec_ref(v_x_330_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(lean_object* v_t_332_, lean_object* v_k_333_){
_start:
{
switch(lean_obj_tag(v_t_332_))
{
case 1:
{
lean_object* v_e_334_; lean_object* v_thm_335_; lean_object* v_d_336_; lean_object* v_a_337_; lean_object* v___x_338_; 
v_e_334_ = lean_ctor_get(v_t_332_, 0);
lean_inc_ref(v_e_334_);
v_thm_335_ = lean_ctor_get(v_t_332_, 1);
lean_inc_ref(v_thm_335_);
v_d_336_ = lean_ctor_get(v_t_332_, 2);
lean_inc(v_d_336_);
v_a_337_ = lean_ctor_get(v_t_332_, 3);
lean_inc_ref(v_a_337_);
lean_dec_ref_known(v_t_332_, 4);
v___x_338_ = lean_apply_4(v_k_333_, v_e_334_, v_thm_335_, v_d_336_, v_a_337_);
return v___x_338_;
}
case 4:
{
lean_object* v_c_339_; lean_object* v_a_340_; lean_object* v___x_341_; 
v_c_339_ = lean_ctor_get(v_t_332_, 0);
lean_inc_ref(v_c_339_);
v_a_340_ = lean_ctor_get(v_t_332_, 1);
lean_inc(v_a_340_);
lean_dec_ref_known(v_t_332_, 2);
v___x_341_ = lean_apply_2(v_k_333_, v_c_339_, v_a_340_);
return v___x_341_;
}
case 5:
{
lean_object* v_c_u2081_342_; lean_object* v_c_u2082_343_; lean_object* v___x_344_; 
v_c_u2081_342_ = lean_ctor_get(v_t_332_, 0);
lean_inc_ref(v_c_u2081_342_);
v_c_u2082_343_ = lean_ctor_get(v_t_332_, 1);
lean_inc_ref(v_c_u2082_343_);
lean_dec_ref_known(v_t_332_, 2);
v___x_344_ = lean_apply_2(v_k_333_, v_c_u2081_342_, v_c_u2082_343_);
return v___x_344_;
}
case 6:
{
lean_object* v_c_u2081_345_; lean_object* v_c_u2082_346_; lean_object* v___x_347_; 
v_c_u2081_345_ = lean_ctor_get(v_t_332_, 0);
lean_inc_ref(v_c_u2081_345_);
v_c_u2082_346_ = lean_ctor_get(v_t_332_, 1);
lean_inc_ref(v_c_u2082_346_);
lean_dec_ref_known(v_t_332_, 2);
v___x_347_ = lean_apply_2(v_k_333_, v_c_u2081_345_, v_c_u2082_346_);
return v___x_347_;
}
case 9:
{
lean_object* v_x_348_; lean_object* v_c_u2081_349_; lean_object* v_c_u2082_350_; lean_object* v___x_351_; 
v_x_348_ = lean_ctor_get(v_t_332_, 0);
lean_inc(v_x_348_);
v_c_u2081_349_ = lean_ctor_get(v_t_332_, 1);
lean_inc_ref(v_c_u2081_349_);
v_c_u2082_350_ = lean_ctor_get(v_t_332_, 2);
lean_inc_ref(v_c_u2082_350_);
lean_dec_ref_known(v_t_332_, 3);
v___x_351_ = lean_apply_3(v_k_333_, v_x_348_, v_c_u2081_349_, v_c_u2082_350_);
return v___x_351_;
}
case 13:
{
lean_object* v_c_352_; lean_object* v_e_353_; lean_object* v_p_354_; lean_object* v___x_355_; 
v_c_352_ = lean_ctor_get(v_t_332_, 0);
lean_inc_ref(v_c_352_);
v_e_353_ = lean_ctor_get(v_t_332_, 1);
lean_inc_ref(v_e_353_);
v_p_354_ = lean_ctor_get(v_t_332_, 2);
lean_inc_ref(v_p_354_);
lean_dec_ref_known(v_t_332_, 3);
v___x_355_ = lean_apply_3(v_k_333_, v_c_352_, v_e_353_, v_p_354_);
return v___x_355_;
}
default: 
{
lean_object* v_e_356_; lean_object* v___x_357_; 
v_e_356_ = lean_ctor_get(v_t_332_, 0);
lean_inc_ref(v_e_356_);
lean_dec_ref(v_t_332_);
v___x_357_ = lean_apply_1(v_k_333_, v_e_356_);
return v___x_357_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim(lean_object* v_motive__7_358_, lean_object* v_ctorIdx_359_, lean_object* v_t_360_, lean_object* v_h_361_, lean_object* v_k_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_360_, v_k_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___boxed(lean_object* v_motive__7_364_, lean_object* v_ctorIdx_365_, lean_object* v_t_366_, lean_object* v_h_367_, lean_object* v_k_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim(v_motive__7_364_, v_ctorIdx_365_, v_t_366_, v_h_367_, v_k_368_);
lean_dec(v_ctorIdx_365_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_core_elim___redArg(lean_object* v_t_370_, lean_object* v_core_371_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_370_, v_core_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_core_elim(lean_object* v_motive__7_373_, lean_object* v_t_374_, lean_object* v_h_375_, lean_object* v_core_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_374_, v_core_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_coreOfNat_elim___redArg(lean_object* v_t_378_, lean_object* v_coreOfNat_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_378_, v_coreOfNat_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_coreOfNat_elim(lean_object* v_motive__7_381_, lean_object* v_t_382_, lean_object* v_h_383_, lean_object* v_coreOfNat_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_382_, v_coreOfNat_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_norm_elim___redArg(lean_object* v_t_386_, lean_object* v_norm_387_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_386_, v_norm_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_norm_elim(lean_object* v_motive__7_389_, lean_object* v_t_390_, lean_object* v_h_391_, lean_object* v_norm_392_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_390_, v_norm_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_divCoeffs_elim___redArg(lean_object* v_t_394_, lean_object* v_divCoeffs_395_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_394_, v_divCoeffs_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_divCoeffs_elim(lean_object* v_motive__7_397_, lean_object* v_t_398_, lean_object* v_h_399_, lean_object* v_divCoeffs_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_398_, v_divCoeffs_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_bmodCoeffs_elim___redArg(lean_object* v_t_402_, lean_object* v_bmodCoeffs_403_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_402_, v_bmodCoeffs_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_bmodCoeffs_elim(lean_object* v_motive__7_405_, lean_object* v_t_406_, lean_object* v_h_407_, lean_object* v_bmodCoeffs_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_406_, v_bmodCoeffs_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveCombine_elim___redArg(lean_object* v_t_410_, lean_object* v_solveCombine_411_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_410_, v_solveCombine_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveCombine_elim(lean_object* v_motive__7_413_, lean_object* v_t_414_, lean_object* v_h_415_, lean_object* v_solveCombine_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_414_, v_solveCombine_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveElim_elim___redArg(lean_object* v_t_418_, lean_object* v_solveElim_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_418_, v_solveElim_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveElim_elim(lean_object* v_motive__7_421_, lean_object* v_t_422_, lean_object* v_h_423_, lean_object* v_solveElim_424_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_422_, v_solveElim_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_elim_elim___redArg(lean_object* v_t_426_, lean_object* v_elim_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_426_, v_elim_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_elim_elim(lean_object* v_motive__7_429_, lean_object* v_t_430_, lean_object* v_h_431_, lean_object* v_elim_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_430_, v_elim_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ofEqZero_elim___redArg(lean_object* v_t_434_, lean_object* v_ofEqZero_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_434_, v_ofEqZero_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ofEqZero_elim(lean_object* v_motive__7_437_, lean_object* v_t_438_, lean_object* v_h_439_, lean_object* v_ofEqZero_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_438_, v_ofEqZero_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_subst_elim___redArg(lean_object* v_t_442_, lean_object* v_subst_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_442_, v_subst_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_subst_elim(lean_object* v_motive__7_445_, lean_object* v_t_446_, lean_object* v_h_447_, lean_object* v_subst_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_446_, v_subst_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2081_elim___redArg(lean_object* v_t_450_, lean_object* v_cooper_u2081_451_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_450_, v_cooper_u2081_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2081_elim(lean_object* v_motive__7_453_, lean_object* v_t_454_, lean_object* v_h_455_, lean_object* v_cooper_u2081_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_454_, v_cooper_u2081_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2082_elim___redArg(lean_object* v_t_458_, lean_object* v_cooper_u2082_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_458_, v_cooper_u2082_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2082_elim(lean_object* v_motive__7_461_, lean_object* v_t_462_, lean_object* v_h_463_, lean_object* v_cooper_u2082_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_462_, v_cooper_u2082_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_reorder_elim___redArg(lean_object* v_t_466_, lean_object* v_reorder_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_466_, v_reorder_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_reorder_elim(lean_object* v_motive__7_469_, lean_object* v_t_470_, lean_object* v_h_471_, lean_object* v_reorder_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_470_, v_reorder_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_commRingNorm_elim___redArg(lean_object* v_t_474_, lean_object* v_commRingNorm_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_474_, v_commRingNorm_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_commRingNorm_elim(lean_object* v_motive__7_477_, lean_object* v_t_478_, lean_object* v_h_479_, lean_object* v_commRingNorm_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_478_, v_commRingNorm_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorIdx___impl(lean_object* v_x_482_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = lean_obj_tag_nat(v_x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorIdx___impl___boxed(lean_object* v_x_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorIdx___impl(v_x_484_);
lean_dec_ref(v_x_484_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(lean_object* v_t_486_, lean_object* v_k_487_){
_start:
{
switch(lean_obj_tag(v_t_486_))
{
case 1:
{
lean_object* v_e_488_; lean_object* v_p_489_; lean_object* v___x_490_; 
v_e_488_ = lean_ctor_get(v_t_486_, 0);
lean_inc_ref(v_e_488_);
v_p_489_ = lean_ctor_get(v_t_486_, 1);
lean_inc_ref(v_p_489_);
lean_dec_ref_known(v_t_486_, 2);
v___x_490_ = lean_apply_2(v_k_487_, v_e_488_, v_p_489_);
return v___x_490_;
}
case 2:
{
lean_object* v_e_491_; uint8_t v_pos_492_; lean_object* v_toIntThm_493_; lean_object* v_lhs_494_; lean_object* v_rhs_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v_e_491_ = lean_ctor_get(v_t_486_, 0);
lean_inc_ref(v_e_491_);
v_pos_492_ = lean_ctor_get_uint8(v_t_486_, sizeof(void*)*4);
v_toIntThm_493_ = lean_ctor_get(v_t_486_, 1);
lean_inc_ref(v_toIntThm_493_);
v_lhs_494_ = lean_ctor_get(v_t_486_, 2);
lean_inc_ref(v_lhs_494_);
v_rhs_495_ = lean_ctor_get(v_t_486_, 3);
lean_inc_ref(v_rhs_495_);
lean_dec_ref_known(v_t_486_, 4);
v___x_496_ = lean_box(v_pos_492_);
v___x_497_ = lean_apply_5(v_k_487_, v_e_491_, v___x_496_, v_toIntThm_493_, v_lhs_494_, v_rhs_495_);
return v___x_497_;
}
case 3:
{
lean_object* v_e_498_; uint8_t v_pos_499_; lean_object* v_lhs_500_; lean_object* v_rhs_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v_e_498_ = lean_ctor_get(v_t_486_, 0);
lean_inc_ref(v_e_498_);
v_pos_499_ = lean_ctor_get_uint8(v_t_486_, sizeof(void*)*3);
v_lhs_500_ = lean_ctor_get(v_t_486_, 1);
lean_inc_ref(v_lhs_500_);
v_rhs_501_ = lean_ctor_get(v_t_486_, 2);
lean_inc_ref(v_rhs_501_);
lean_dec_ref_known(v_t_486_, 3);
v___x_502_ = lean_box(v_pos_499_);
v___x_503_ = lean_apply_4(v_k_487_, v_e_498_, v___x_502_, v_lhs_500_, v_rhs_501_);
return v___x_503_;
}
case 6:
{
lean_object* v_h_504_; lean_object* v___x_505_; 
v_h_504_ = lean_ctor_get(v_t_486_, 0);
lean_inc(v_h_504_);
lean_dec_ref_known(v_t_486_, 1);
v___x_505_ = lean_apply_1(v_k_487_, v_h_504_);
return v___x_505_;
}
case 9:
{
lean_object* v_c_u2081_506_; lean_object* v_c_u2082_507_; lean_object* v___x_508_; 
v_c_u2081_506_ = lean_ctor_get(v_t_486_, 0);
lean_inc_ref(v_c_u2081_506_);
v_c_u2082_507_ = lean_ctor_get(v_t_486_, 1);
lean_inc_ref(v_c_u2082_507_);
lean_dec_ref_known(v_t_486_, 2);
v___x_508_ = lean_apply_2(v_k_487_, v_c_u2081_506_, v_c_u2082_507_);
return v___x_508_;
}
case 10:
{
lean_object* v_c_u2081_509_; lean_object* v_c_u2082_510_; lean_object* v_k_511_; lean_object* v___x_512_; 
v_c_u2081_509_ = lean_ctor_get(v_t_486_, 0);
lean_inc_ref(v_c_u2081_509_);
v_c_u2082_510_ = lean_ctor_get(v_t_486_, 1);
lean_inc_ref(v_c_u2082_510_);
v_k_511_ = lean_ctor_get(v_t_486_, 2);
lean_inc(v_k_511_);
lean_dec_ref_known(v_t_486_, 3);
v___x_512_ = lean_apply_3(v_k_487_, v_c_u2081_509_, v_c_u2082_510_, v_k_511_);
return v___x_512_;
}
case 11:
{
lean_object* v_x_513_; lean_object* v_c_u2081_514_; lean_object* v_c_u2082_515_; lean_object* v___x_516_; 
v_x_513_ = lean_ctor_get(v_t_486_, 0);
lean_inc(v_x_513_);
v_c_u2081_514_ = lean_ctor_get(v_t_486_, 1);
lean_inc_ref(v_c_u2081_514_);
v_c_u2082_515_ = lean_ctor_get(v_t_486_, 2);
lean_inc_ref(v_c_u2082_515_);
lean_dec_ref_known(v_t_486_, 3);
v___x_516_ = lean_apply_3(v_k_487_, v_x_513_, v_c_u2081_514_, v_c_u2082_515_);
return v___x_516_;
}
case 12:
{
lean_object* v_c_u2081_517_; lean_object* v_c_u2082_518_; lean_object* v___x_519_; 
v_c_u2081_517_ = lean_ctor_get(v_t_486_, 0);
lean_inc_ref(v_c_u2081_517_);
v_c_u2082_518_ = lean_ctor_get(v_t_486_, 1);
lean_inc_ref(v_c_u2082_518_);
lean_dec_ref_known(v_t_486_, 2);
v___x_519_ = lean_apply_2(v_k_487_, v_c_u2081_517_, v_c_u2082_518_);
return v___x_519_;
}
case 13:
{
lean_object* v_c_u2081_520_; lean_object* v_decVar_521_; lean_object* v_h_522_; lean_object* v_decVars_523_; lean_object* v___x_524_; 
v_c_u2081_520_ = lean_ctor_get(v_t_486_, 0);
lean_inc_ref(v_c_u2081_520_);
v_decVar_521_ = lean_ctor_get(v_t_486_, 1);
lean_inc(v_decVar_521_);
v_h_522_ = lean_ctor_get(v_t_486_, 2);
lean_inc_ref(v_h_522_);
v_decVars_523_ = lean_ctor_get(v_t_486_, 3);
lean_inc_ref(v_decVars_523_);
lean_dec_ref_known(v_t_486_, 4);
v___x_524_ = lean_apply_4(v_k_487_, v_c_u2081_520_, v_decVar_521_, v_h_522_, v_decVars_523_);
return v___x_524_;
}
case 15:
{
lean_object* v_c_u2081_525_; lean_object* v_c_u2082_526_; lean_object* v_t_527_; lean_object* v_g_528_; lean_object* v___x_529_; 
v_c_u2081_525_ = lean_ctor_get(v_t_486_, 0);
lean_inc_ref(v_c_u2081_525_);
v_c_u2082_526_ = lean_ctor_get(v_t_486_, 1);
lean_inc_ref(v_c_u2082_526_);
v_t_527_ = lean_ctor_get(v_t_486_, 2);
lean_inc(v_t_527_);
v_g_528_ = lean_ctor_get(v_t_486_, 3);
lean_inc(v_g_528_);
lean_dec_ref_known(v_t_486_, 4);
v___x_529_ = lean_apply_4(v_k_487_, v_c_u2081_525_, v_c_u2082_526_, v_t_527_, v_g_528_);
return v___x_529_;
}
case 17:
{
lean_object* v_c_530_; lean_object* v_e_531_; lean_object* v_p_532_; lean_object* v___x_533_; 
v_c_530_ = lean_ctor_get(v_t_486_, 0);
lean_inc_ref(v_c_530_);
v_e_531_ = lean_ctor_get(v_t_486_, 1);
lean_inc_ref(v_e_531_);
v_p_532_ = lean_ctor_get(v_t_486_, 2);
lean_inc_ref(v_p_532_);
lean_dec_ref_known(v_t_486_, 3);
v___x_533_ = lean_apply_3(v_k_487_, v_c_530_, v_e_531_, v_p_532_);
return v___x_533_;
}
default: 
{
lean_object* v_e_534_; lean_object* v___x_535_; 
v_e_534_ = lean_ctor_get(v_t_486_, 0);
lean_inc_ref(v_e_534_);
lean_dec_ref(v_t_486_);
v___x_535_ = lean_apply_1(v_k_487_, v_e_534_);
return v___x_535_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim(lean_object* v_motive__9_536_, lean_object* v_ctorIdx_537_, lean_object* v_t_538_, lean_object* v_h_539_, lean_object* v_k_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_538_, v_k_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___boxed(lean_object* v_motive__9_542_, lean_object* v_ctorIdx_543_, lean_object* v_t_544_, lean_object* v_h_545_, lean_object* v_k_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim(v_motive__9_542_, v_ctorIdx_543_, v_t_544_, v_h_545_, v_k_546_);
lean_dec(v_ctorIdx_543_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_core_elim___redArg(lean_object* v_t_548_, lean_object* v_core_549_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_548_, v_core_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_core_elim(lean_object* v_motive__9_551_, lean_object* v_t_552_, lean_object* v_h_553_, lean_object* v_core_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_552_, v_core_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreNeg_elim___redArg(lean_object* v_t_556_, lean_object* v_coreNeg_557_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_556_, v_coreNeg_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreNeg_elim(lean_object* v_motive__9_559_, lean_object* v_t_560_, lean_object* v_h_561_, lean_object* v_coreNeg_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_560_, v_coreNeg_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreToInt_elim___redArg(lean_object* v_t_564_, lean_object* v_coreToInt_565_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_564_, v_coreToInt_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreToInt_elim(lean_object* v_motive__9_567_, lean_object* v_t_568_, lean_object* v_h_569_, lean_object* v_coreToInt_570_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_568_, v_coreToInt_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreExpr_elim___redArg(lean_object* v_t_572_, lean_object* v_coreExpr_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_572_, v_coreExpr_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreExpr_elim(lean_object* v_motive__9_575_, lean_object* v_t_576_, lean_object* v_h_577_, lean_object* v_coreExpr_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_576_, v_coreExpr_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofNatNonneg_elim___redArg(lean_object* v_t_580_, lean_object* v_ofNatNonneg_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_580_, v_ofNatNonneg_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofNatNonneg_elim(lean_object* v_motive__9_583_, lean_object* v_t_584_, lean_object* v_h_585_, lean_object* v_ofNatNonneg_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_584_, v_ofNatNonneg_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_bound_elim___redArg(lean_object* v_t_588_, lean_object* v_bound_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_588_, v_bound_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_bound_elim(lean_object* v_motive__9_591_, lean_object* v_t_592_, lean_object* v_h_593_, lean_object* v_bound_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_592_, v_bound_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dec_elim___redArg(lean_object* v_t_596_, lean_object* v_dec_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_596_, v_dec_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dec_elim(lean_object* v_motive__9_599_, lean_object* v_t_600_, lean_object* v_h_601_, lean_object* v_dec_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_600_, v_dec_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_norm_elim___redArg(lean_object* v_t_604_, lean_object* v_norm_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_604_, v_norm_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_norm_elim(lean_object* v_motive__9_607_, lean_object* v_t_608_, lean_object* v_h_609_, lean_object* v_norm_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_608_, v_norm_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_divCoeffs_elim___redArg(lean_object* v_t_612_, lean_object* v_divCoeffs_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_612_, v_divCoeffs_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_divCoeffs_elim(lean_object* v_motive__9_615_, lean_object* v_t_616_, lean_object* v_h_617_, lean_object* v_divCoeffs_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_616_, v_divCoeffs_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combine_elim___redArg(lean_object* v_t_620_, lean_object* v_combine_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_620_, v_combine_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combine_elim(lean_object* v_motive__9_623_, lean_object* v_t_624_, lean_object* v_h_625_, lean_object* v_combine_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_624_, v_combine_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combineDivCoeffs_elim___redArg(lean_object* v_t_628_, lean_object* v_combineDivCoeffs_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_628_, v_combineDivCoeffs_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combineDivCoeffs_elim(lean_object* v_motive__9_631_, lean_object* v_t_632_, lean_object* v_h_633_, lean_object* v_combineDivCoeffs_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_632_, v_combineDivCoeffs_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_subst_elim___redArg(lean_object* v_t_636_, lean_object* v_subst_637_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_636_, v_subst_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_subst_elim(lean_object* v_motive__9_639_, lean_object* v_t_640_, lean_object* v_h_641_, lean_object* v_subst_642_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_640_, v_subst_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofLeDiseq_elim___redArg(lean_object* v_t_644_, lean_object* v_ofLeDiseq_645_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_644_, v_ofLeDiseq_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofLeDiseq_elim(lean_object* v_motive__9_647_, lean_object* v_t_648_, lean_object* v_h_649_, lean_object* v_ofLeDiseq_650_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_648_, v_ofLeDiseq_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofDiseqSplit_elim___redArg(lean_object* v_t_652_, lean_object* v_ofDiseqSplit_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_652_, v_ofDiseqSplit_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofDiseqSplit_elim(lean_object* v_motive__9_655_, lean_object* v_t_656_, lean_object* v_h_657_, lean_object* v_ofDiseqSplit_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_656_, v_ofDiseqSplit_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_cooper_elim___redArg(lean_object* v_t_660_, lean_object* v_cooper_661_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_660_, v_cooper_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_cooper_elim(lean_object* v_motive__9_663_, lean_object* v_t_664_, lean_object* v_h_665_, lean_object* v_cooper_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_664_, v_cooper_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dvdTightMod_elim___redArg(lean_object* v_t_668_, lean_object* v_dvdTightMod_669_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_668_, v_dvdTightMod_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dvdTightMod_elim(lean_object* v_motive__9_671_, lean_object* v_t_672_, lean_object* v_h_673_, lean_object* v_dvdTightMod_674_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_672_, v_dvdTightMod_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_reorder_elim___redArg(lean_object* v_t_676_, lean_object* v_reorder_677_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_676_, v_reorder_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_reorder_elim(lean_object* v_motive__9_679_, lean_object* v_t_680_, lean_object* v_h_681_, lean_object* v_reorder_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_680_, v_reorder_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_commRingNorm_elim___redArg(lean_object* v_t_684_, lean_object* v_commRingNorm_685_){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_684_, v_commRingNorm_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_commRingNorm_elim(lean_object* v_motive__9_687_, lean_object* v_t_688_, lean_object* v_h_689_, lean_object* v_commRingNorm_690_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_688_, v_commRingNorm_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorIdx___impl(lean_object* v_x_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = lean_obj_tag_nat(v_x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorIdx___impl___boxed(lean_object* v_x_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorIdx___impl(v_x_694_);
lean_dec_ref(v_x_694_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(lean_object* v_t_696_, lean_object* v_k_697_){
_start:
{
switch(lean_obj_tag(v_t_696_))
{
case 0:
{
lean_object* v_a_698_; lean_object* v_zero_699_; lean_object* v___x_700_; 
v_a_698_ = lean_ctor_get(v_t_696_, 0);
lean_inc_ref(v_a_698_);
v_zero_699_ = lean_ctor_get(v_t_696_, 1);
lean_inc_ref(v_zero_699_);
lean_dec_ref_known(v_t_696_, 2);
v___x_700_ = lean_apply_2(v_k_697_, v_a_698_, v_zero_699_);
return v___x_700_;
}
case 1:
{
lean_object* v_a_701_; lean_object* v_b_702_; lean_object* v_p_u2081_703_; lean_object* v_p_u2082_704_; lean_object* v___x_705_; 
v_a_701_ = lean_ctor_get(v_t_696_, 0);
lean_inc_ref(v_a_701_);
v_b_702_ = lean_ctor_get(v_t_696_, 1);
lean_inc_ref(v_b_702_);
v_p_u2081_703_ = lean_ctor_get(v_t_696_, 2);
lean_inc_ref(v_p_u2081_703_);
v_p_u2082_704_ = lean_ctor_get(v_t_696_, 3);
lean_inc_ref(v_p_u2082_704_);
lean_dec_ref_known(v_t_696_, 4);
v___x_705_ = lean_apply_4(v_k_697_, v_a_701_, v_b_702_, v_p_u2081_703_, v_p_u2082_704_);
return v___x_705_;
}
case 2:
{
lean_object* v_a_706_; lean_object* v_b_707_; lean_object* v_toIntThm_708_; lean_object* v_lhs_709_; lean_object* v_rhs_710_; lean_object* v___x_711_; 
v_a_706_ = lean_ctor_get(v_t_696_, 0);
lean_inc_ref(v_a_706_);
v_b_707_ = lean_ctor_get(v_t_696_, 1);
lean_inc_ref(v_b_707_);
v_toIntThm_708_ = lean_ctor_get(v_t_696_, 2);
lean_inc_ref(v_toIntThm_708_);
v_lhs_709_ = lean_ctor_get(v_t_696_, 3);
lean_inc_ref(v_lhs_709_);
v_rhs_710_ = lean_ctor_get(v_t_696_, 4);
lean_inc_ref(v_rhs_710_);
lean_dec_ref_known(v_t_696_, 5);
v___x_711_ = lean_apply_5(v_k_697_, v_a_706_, v_b_707_, v_toIntThm_708_, v_lhs_709_, v_rhs_710_);
return v___x_711_;
}
case 6:
{
lean_object* v_x_712_; lean_object* v_c_u2081_713_; lean_object* v_c_u2082_714_; lean_object* v___x_715_; 
v_x_712_ = lean_ctor_get(v_t_696_, 0);
lean_inc(v_x_712_);
v_c_u2081_713_ = lean_ctor_get(v_t_696_, 1);
lean_inc_ref(v_c_u2081_713_);
v_c_u2082_714_ = lean_ctor_get(v_t_696_, 2);
lean_inc_ref(v_c_u2082_714_);
lean_dec_ref_known(v_t_696_, 3);
v___x_715_ = lean_apply_3(v_k_697_, v_x_712_, v_c_u2081_713_, v_c_u2082_714_);
return v___x_715_;
}
case 8:
{
lean_object* v_c_716_; lean_object* v_e_717_; lean_object* v_p_718_; lean_object* v___x_719_; 
v_c_716_ = lean_ctor_get(v_t_696_, 0);
lean_inc_ref(v_c_716_);
v_e_717_ = lean_ctor_get(v_t_696_, 1);
lean_inc_ref(v_e_717_);
v_p_718_ = lean_ctor_get(v_t_696_, 2);
lean_inc_ref(v_p_718_);
lean_dec_ref_known(v_t_696_, 3);
v___x_719_ = lean_apply_3(v_k_697_, v_c_716_, v_e_717_, v_p_718_);
return v___x_719_;
}
default: 
{
lean_object* v_c_720_; lean_object* v___x_721_; 
v_c_720_ = lean_ctor_get(v_t_696_, 0);
lean_inc_ref(v_c_720_);
lean_dec_ref(v_t_696_);
v___x_721_ = lean_apply_1(v_k_697_, v_c_720_);
return v___x_721_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim(lean_object* v_motive__11_722_, lean_object* v_ctorIdx_723_, lean_object* v_t_724_, lean_object* v_h_725_, lean_object* v_k_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_724_, v_k_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___boxed(lean_object* v_motive__11_728_, lean_object* v_ctorIdx_729_, lean_object* v_t_730_, lean_object* v_h_731_, lean_object* v_k_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim(v_motive__11_728_, v_ctorIdx_729_, v_t_730_, v_h_731_, v_k_732_);
lean_dec(v_ctorIdx_729_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core0_elim___redArg(lean_object* v_t_734_, lean_object* v_core0_735_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_734_, v_core0_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core0_elim(lean_object* v_motive__11_737_, lean_object* v_t_738_, lean_object* v_h_739_, lean_object* v_core0_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_738_, v_core0_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core_elim___redArg(lean_object* v_t_742_, lean_object* v_core_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_742_, v_core_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core_elim(lean_object* v_motive__11_745_, lean_object* v_t_746_, lean_object* v_h_747_, lean_object* v_core_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_746_, v_core_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_coreToInt_elim___redArg(lean_object* v_t_750_, lean_object* v_coreToInt_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_750_, v_coreToInt_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_coreToInt_elim(lean_object* v_motive__11_753_, lean_object* v_t_754_, lean_object* v_h_755_, lean_object* v_coreToInt_756_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_754_, v_coreToInt_756_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_norm_elim___redArg(lean_object* v_t_758_, lean_object* v_norm_759_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_758_, v_norm_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_norm_elim(lean_object* v_motive__11_761_, lean_object* v_t_762_, lean_object* v_h_763_, lean_object* v_norm_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_762_, v_norm_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_divCoeffs_elim___redArg(lean_object* v_t_766_, lean_object* v_divCoeffs_767_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_766_, v_divCoeffs_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_divCoeffs_elim(lean_object* v_motive__11_769_, lean_object* v_t_770_, lean_object* v_h_771_, lean_object* v_divCoeffs_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_770_, v_divCoeffs_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_neg_elim___redArg(lean_object* v_t_774_, lean_object* v_neg_775_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_774_, v_neg_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_neg_elim(lean_object* v_motive__11_777_, lean_object* v_t_778_, lean_object* v_h_779_, lean_object* v_neg_780_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_778_, v_neg_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_subst_elim___redArg(lean_object* v_t_782_, lean_object* v_subst_783_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_782_, v_subst_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_subst_elim(lean_object* v_motive__11_785_, lean_object* v_t_786_, lean_object* v_h_787_, lean_object* v_subst_788_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_786_, v_subst_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_reorder_elim___redArg(lean_object* v_t_790_, lean_object* v_reorder_791_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_790_, v_reorder_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_reorder_elim(lean_object* v_motive__11_793_, lean_object* v_t_794_, lean_object* v_h_795_, lean_object* v_reorder_796_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_794_, v_reorder_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_commRingNorm_elim___redArg(lean_object* v_t_798_, lean_object* v_commRingNorm_799_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_798_, v_commRingNorm_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_commRingNorm_elim(lean_object* v_motive__11_801_, lean_object* v_t_802_, lean_object* v_h_803_, lean_object* v_commRingNorm_804_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_802_, v_commRingNorm_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorIdx___impl(lean_object* v_x_806_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = lean_obj_tag_nat(v_x_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorIdx___impl___boxed(lean_object* v_x_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorIdx___impl(v_x_808_);
lean_dec_ref(v_x_808_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(lean_object* v_t_810_, lean_object* v_k_811_){
_start:
{
if (lean_obj_tag(v_t_810_) == 4)
{
lean_object* v_c_u2081_812_; lean_object* v_c_u2082_813_; lean_object* v_c_u2083_814_; lean_object* v___x_815_; 
v_c_u2081_812_ = lean_ctor_get(v_t_810_, 0);
lean_inc_ref(v_c_u2081_812_);
v_c_u2082_813_ = lean_ctor_get(v_t_810_, 1);
lean_inc_ref(v_c_u2082_813_);
v_c_u2083_814_ = lean_ctor_get(v_t_810_, 2);
lean_inc_ref(v_c_u2083_814_);
lean_dec_ref_known(v_t_810_, 3);
v___x_815_ = lean_apply_3(v_k_811_, v_c_u2081_812_, v_c_u2082_813_, v_c_u2083_814_);
return v___x_815_;
}
else
{
lean_object* v_c_816_; lean_object* v___x_817_; 
v_c_816_ = lean_ctor_get(v_t_810_, 0);
lean_inc_ref(v_c_816_);
lean_dec_ref(v_t_810_);
v___x_817_ = lean_apply_1(v_k_811_, v_c_816_);
return v___x_817_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim(lean_object* v_motive__12_818_, lean_object* v_ctorIdx_819_, lean_object* v_t_820_, lean_object* v_h_821_, lean_object* v_k_822_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_820_, v_k_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___boxed(lean_object* v_motive__12_824_, lean_object* v_ctorIdx_825_, lean_object* v_t_826_, lean_object* v_h_827_, lean_object* v_k_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim(v_motive__12_824_, v_ctorIdx_825_, v_t_826_, v_h_827_, v_k_828_);
lean_dec(v_ctorIdx_825_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_dvd_elim___redArg(lean_object* v_t_830_, lean_object* v_dvd_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_830_, v_dvd_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_dvd_elim(lean_object* v_motive__12_833_, lean_object* v_t_834_, lean_object* v_h_835_, lean_object* v_dvd_836_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_834_, v_dvd_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_le_elim___redArg(lean_object* v_t_838_, lean_object* v_le_839_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_838_, v_le_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_le_elim(lean_object* v_motive__12_841_, lean_object* v_t_842_, lean_object* v_h_843_, lean_object* v_le_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_842_, v_le_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_eq_elim___redArg(lean_object* v_t_846_, lean_object* v_eq_847_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_846_, v_eq_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_eq_elim(lean_object* v_motive__12_849_, lean_object* v_t_850_, lean_object* v_h_851_, lean_object* v_eq_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_850_, v_eq_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_diseq_elim___redArg(lean_object* v_t_854_, lean_object* v_diseq_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_854_, v_diseq_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_diseq_elim(lean_object* v_motive__12_857_, lean_object* v_t_858_, lean_object* v_h_859_, lean_object* v_diseq_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_858_, v_diseq_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_cooper_elim___redArg(lean_object* v_t_862_, lean_object* v_cooper_863_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_862_, v_cooper_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_cooper_elim(lean_object* v_motive__12_865_, lean_object* v_t_866_, lean_object* v_h_867_, lean_object* v_cooper_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_866_, v_cooper_868_);
return v___x_869_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0(void){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0);
v___x_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
return v___x_871_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3(void){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_875_ = lean_box(0);
v___x_876_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__2));
v___x_877_ = l_Lean_Expr_const___override(v___x_876_, v___x_875_);
return v___x_877_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4(void){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3);
v___x_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
return v___x_879_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5(void){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_880_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4);
v___x_881_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0);
v___x_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
lean_ctor_set(v___x_882_, 1, v___x_880_);
return v___x_882_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr(void){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5);
return v___x_883_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0(void){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3);
v___x_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
return v___x_885_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_886_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0);
v___x_887_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0);
v___x_888_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0);
v___x_889_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
lean_ctor_set(v___x_889_, 1, v___x_887_);
lean_ctor_set(v___x_889_, 2, v___x_886_);
return v___x_889_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr(void){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1);
return v___x_890_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0(void){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; uint8_t v___x_893_; lean_object* v___x_894_; 
v___x_891_ = lean_box(0);
v___x_892_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5);
v___x_893_ = 0;
v___x_894_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_894_, 0, v___x_892_);
lean_ctor_set(v___x_894_, 1, v___x_892_);
lean_ctor_set(v___x_894_, 2, v___x_891_);
lean_ctor_set_uint8(v___x_894_, sizeof(void*)*3, v___x_893_);
return v___x_894_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred(void){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0);
return v___x_895_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1(void){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_898_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__0));
v___x_899_ = lean_unsigned_to_nat(0u);
v___x_900_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0);
v___x_901_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
lean_ctor_set(v___x_901_, 1, v___x_899_);
lean_ctor_set(v___x_901_, 2, v___x_898_);
return v___x_901_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit(void){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1);
return v___x_902_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_903_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0);
v___x_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg(){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__1);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___boxed(lean_object* v___dummy_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg();
return v_res_909_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg();
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0(lean_object* v_00_u03b2_911_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0);
return v___x_912_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0(void){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_913_ = lean_unsigned_to_nat(32u);
v___x_914_ = lean_mk_empty_array_with_capacity(v___x_913_);
v___x_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
return v___x_915_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1(void){
_start:
{
size_t v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_916_ = ((size_t)5ULL);
v___x_917_ = lean_unsigned_to_nat(0u);
v___x_918_ = lean_unsigned_to_nat(32u);
v___x_919_ = lean_mk_empty_array_with_capacity(v___x_918_);
v___x_920_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0);
v___x_921_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_921_, 0, v___x_920_);
lean_ctor_set(v___x_921_, 1, v___x_919_);
lean_ctor_set(v___x_921_, 2, v___x_917_);
lean_ctor_set(v___x_921_, 3, v___x_917_);
lean_ctor_set_usize(v___x_921_, 4, v___x_916_);
return v___x_921_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0);
v___x_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
return v___x_923_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3(void){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; uint8_t v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_924_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0);
v___x_925_ = lean_box(0);
v___x_926_ = 0;
v___x_927_ = lean_unsigned_to_nat(0u);
v___x_928_ = lean_box(0);
v___x_929_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2);
v___x_930_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1);
v___x_931_ = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(v___x_931_, 0, v___x_930_);
lean_ctor_set(v___x_931_, 1, v___x_929_);
lean_ctor_set(v___x_931_, 2, v___x_930_);
lean_ctor_set(v___x_931_, 3, v___x_929_);
lean_ctor_set(v___x_931_, 4, v___x_929_);
lean_ctor_set(v___x_931_, 5, v___x_930_);
lean_ctor_set(v___x_931_, 6, v___x_930_);
lean_ctor_set(v___x_931_, 7, v___x_930_);
lean_ctor_set(v___x_931_, 8, v___x_930_);
lean_ctor_set(v___x_931_, 9, v___x_930_);
lean_ctor_set(v___x_931_, 10, v___x_928_);
lean_ctor_set(v___x_931_, 11, v___x_930_);
lean_ctor_set(v___x_931_, 12, v___x_930_);
lean_ctor_set(v___x_931_, 13, v___x_927_);
lean_ctor_set(v___x_931_, 14, v___x_927_);
lean_ctor_set(v___x_931_, 15, v___x_929_);
lean_ctor_set(v___x_931_, 16, v___x_927_);
lean_ctor_set(v___x_931_, 17, v___x_925_);
lean_ctor_set(v___x_931_, 18, v___x_929_);
lean_ctor_set(v___x_931_, 19, v___x_924_);
lean_ctor_set(v___x_931_, 20, v___x_929_);
lean_ctor_set_uint8(v___x_931_, sizeof(void*)*21, v___x_926_);
lean_ctor_set_uint8(v___x_931_, sizeof(void*)*21 + 1, v___x_926_);
return v___x_931_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default(void){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3);
return v___x_932_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState(void){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default;
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(lean_object* v___x_934_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_936_, 0, v___x_934_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2____boxed(lean_object* v___x_937_, lean_object* v___y_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(v___x_937_);
return v_res_939_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_940_; lean_object* v___f_941_; 
v___x_940_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3);
v___f_941_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_941_, 0, v___x_940_);
return v___f_941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_943_; lean_object* v___x_944_; 
v___f_943_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_);
v___x_944_ = l_Lean_Meta_Grind_registerSolverExtension___redArg(v___f_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2____boxed(lean_object* v_a_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_();
return v_res_946_;
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
