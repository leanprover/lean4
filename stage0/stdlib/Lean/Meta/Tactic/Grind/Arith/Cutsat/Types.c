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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnNat_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnNat_elim(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_reorder_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_reorder_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_commRingNorm_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_commRingNorm_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnCommRing_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnCommRing_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnNatCommRing_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnNatCommRing_elim(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveCombine_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveCombine_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveElim_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveElim_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_elim_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_elim_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ofEq_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ofEq_elim(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dvdTight_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dvdTight_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_negDvdTight_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_negDvdTight_elim(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_e_70_; lean_object* v_e_x27_71_; lean_object* v___x_72_; 
v_e_70_ = lean_ctor_get(v_t_54_, 0);
lean_inc_ref(v_e_70_);
v_e_x27_71_ = lean_ctor_get(v_t_54_, 1);
lean_inc_ref(v_e_x27_71_);
lean_dec_ref_known(v_t_54_, 2);
v___x_72_ = lean_apply_2(v_k_55_, v_e_70_, v_e_x27_71_);
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
case 11:
{
lean_object* v_c_84_; lean_object* v_e_85_; lean_object* v_p_86_; lean_object* v___x_87_; 
v_c_84_ = lean_ctor_get(v_t_54_, 0);
lean_inc_ref(v_c_84_);
v_e_85_ = lean_ctor_get(v_t_54_, 1);
lean_inc_ref(v_e_85_);
v_p_86_ = lean_ctor_get(v_t_54_, 2);
lean_inc_ref(v_p_86_);
lean_dec_ref_known(v_t_54_, 3);
v___x_87_ = lean_apply_3(v_k_55_, v_c_84_, v_e_85_, v_p_86_);
return v___x_87_;
}
case 12:
{
lean_object* v_e_88_; lean_object* v_e_x27_89_; lean_object* v_p_90_; lean_object* v_re_91_; lean_object* v_rp_92_; lean_object* v_p_x27_93_; lean_object* v___x_94_; 
v_e_88_ = lean_ctor_get(v_t_54_, 0);
lean_inc_ref(v_e_88_);
v_e_x27_89_ = lean_ctor_get(v_t_54_, 1);
lean_inc_ref(v_e_x27_89_);
v_p_90_ = lean_ctor_get(v_t_54_, 2);
lean_inc_ref(v_p_90_);
v_re_91_ = lean_ctor_get(v_t_54_, 3);
lean_inc_ref(v_re_91_);
v_rp_92_ = lean_ctor_get(v_t_54_, 4);
lean_inc_ref(v_rp_92_);
v_p_x27_93_ = lean_ctor_get(v_t_54_, 5);
lean_inc_ref(v_p_x27_93_);
lean_dec_ref_known(v_t_54_, 6);
v___x_94_ = lean_apply_6(v_k_55_, v_e_88_, v_e_x27_89_, v_p_90_, v_re_91_, v_rp_92_, v_p_x27_93_);
return v___x_94_;
}
case 13:
{
lean_object* v_h_95_; lean_object* v_x_96_; lean_object* v_e_x27_97_; lean_object* v_p_98_; lean_object* v_re_99_; lean_object* v_rp_100_; lean_object* v_p_x27_101_; lean_object* v___x_102_; 
v_h_95_ = lean_ctor_get(v_t_54_, 0);
lean_inc_ref(v_h_95_);
v_x_96_ = lean_ctor_get(v_t_54_, 1);
lean_inc(v_x_96_);
v_e_x27_97_ = lean_ctor_get(v_t_54_, 2);
lean_inc_ref(v_e_x27_97_);
v_p_98_ = lean_ctor_get(v_t_54_, 3);
lean_inc_ref(v_p_98_);
v_re_99_ = lean_ctor_get(v_t_54_, 4);
lean_inc_ref(v_re_99_);
v_rp_100_ = lean_ctor_get(v_t_54_, 5);
lean_inc_ref(v_rp_100_);
v_p_x27_101_ = lean_ctor_get(v_t_54_, 6);
lean_inc_ref(v_p_x27_101_);
lean_dec_ref_known(v_t_54_, 7);
v___x_102_ = lean_apply_7(v_k_55_, v_h_95_, v_x_96_, v_e_x27_97_, v_p_98_, v_re_99_, v_rp_100_, v_p_x27_101_);
return v___x_102_;
}
case 14:
{
lean_object* v_a_x3f_103_; lean_object* v_cs_104_; lean_object* v___x_105_; 
v_a_x3f_103_ = lean_ctor_get(v_t_54_, 0);
lean_inc(v_a_x3f_103_);
v_cs_104_ = lean_ctor_get(v_t_54_, 1);
lean_inc_ref(v_cs_104_);
lean_dec_ref_known(v_t_54_, 2);
v___x_105_ = lean_apply_2(v_k_55_, v_a_x3f_103_, v_cs_104_);
return v___x_105_;
}
case 15:
{
lean_object* v_k_106_; lean_object* v_y_x3f_107_; lean_object* v_c_108_; lean_object* v___x_109_; 
v_k_106_ = lean_ctor_get(v_t_54_, 0);
lean_inc(v_k_106_);
v_y_x3f_107_ = lean_ctor_get(v_t_54_, 1);
lean_inc(v_y_x3f_107_);
v_c_108_ = lean_ctor_get(v_t_54_, 2);
lean_inc_ref(v_c_108_);
lean_dec_ref_known(v_t_54_, 3);
v___x_109_ = lean_apply_3(v_k_55_, v_k_106_, v_y_x3f_107_, v_c_108_);
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
lean_object* v_ka_114_; lean_object* v_ca_x3f_115_; lean_object* v_kb_116_; lean_object* v_cb_x3f_117_; lean_object* v___x_118_; 
v_ka_114_ = lean_ctor_get(v_t_54_, 0);
lean_inc(v_ka_114_);
v_ca_x3f_115_ = lean_ctor_get(v_t_54_, 1);
lean_inc(v_ca_x3f_115_);
v_kb_116_ = lean_ctor_get(v_t_54_, 2);
lean_inc(v_kb_116_);
v_cb_x3f_117_ = lean_ctor_get(v_t_54_, 3);
lean_inc(v_cb_x3f_117_);
lean_dec_ref_known(v_t_54_, 4);
v___x_118_ = lean_apply_4(v_k_55_, v_ka_114_, v_ca_x3f_115_, v_kb_116_, v_cb_x3f_117_);
return v___x_118_;
}
default: 
{
lean_object* v_c_119_; lean_object* v___x_120_; 
v_c_119_ = lean_ctor_get(v_t_54_, 0);
lean_inc_ref(v_c_119_);
lean_dec_ref(v_t_54_);
v___x_120_ = lean_apply_1(v_k_55_, v_c_119_);
return v___x_120_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim(lean_object* v_motive__2_121_, lean_object* v_ctorIdx_122_, lean_object* v_t_123_, lean_object* v_h_124_, lean_object* v_k_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_123_, v_k_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___boxed(lean_object* v_motive__2_127_, lean_object* v_ctorIdx_128_, lean_object* v_t_129_, lean_object* v_h_130_, lean_object* v_k_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim(v_motive__2_127_, v_ctorIdx_128_, v_t_129_, v_h_130_, v_k_131_);
lean_dec(v_ctorIdx_128_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core0_elim___redArg(lean_object* v_t_133_, lean_object* v_core0_134_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_133_, v_core0_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core0_elim(lean_object* v_motive__2_136_, lean_object* v_t_137_, lean_object* v_h_138_, lean_object* v_core0_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_137_, v_core0_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core_elim___redArg(lean_object* v_t_141_, lean_object* v_core_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_141_, v_core_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core_elim(lean_object* v_motive__2_144_, lean_object* v_t_145_, lean_object* v_h_146_, lean_object* v_core_147_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_145_, v_core_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_coreToInt_elim___redArg(lean_object* v_t_149_, lean_object* v_coreToInt_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_149_, v_coreToInt_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_coreToInt_elim(lean_object* v_motive__2_152_, lean_object* v_t_153_, lean_object* v_h_154_, lean_object* v_coreToInt_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_153_, v_coreToInt_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defn_elim___redArg(lean_object* v_t_157_, lean_object* v_defn_158_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_157_, v_defn_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defn_elim(lean_object* v_motive__2_160_, lean_object* v_t_161_, lean_object* v_h_162_, lean_object* v_defn_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_161_, v_defn_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnNat_elim___redArg(lean_object* v_t_165_, lean_object* v_defnNat_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_165_, v_defnNat_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnNat_elim(lean_object* v_motive__2_168_, lean_object* v_t_169_, lean_object* v_h_170_, lean_object* v_defnNat_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_169_, v_defnNat_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_norm_elim___redArg(lean_object* v_t_173_, lean_object* v_norm_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_173_, v_norm_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_norm_elim(lean_object* v_motive__2_176_, lean_object* v_t_177_, lean_object* v_h_178_, lean_object* v_norm_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_177_, v_norm_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_divCoeffs_elim___redArg(lean_object* v_t_181_, lean_object* v_divCoeffs_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_181_, v_divCoeffs_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_divCoeffs_elim(lean_object* v_motive__2_184_, lean_object* v_t_185_, lean_object* v_h_186_, lean_object* v_divCoeffs_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_185_, v_divCoeffs_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_subst_elim___redArg(lean_object* v_t_189_, lean_object* v_subst_190_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_189_, v_subst_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_subst_elim(lean_object* v_motive__2_192_, lean_object* v_t_193_, lean_object* v_h_194_, lean_object* v_subst_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_193_, v_subst_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofLeGe_elim___redArg(lean_object* v_t_197_, lean_object* v_ofLeGe_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_197_, v_ofLeGe_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofLeGe_elim(lean_object* v_motive__2_200_, lean_object* v_t_201_, lean_object* v_h_202_, lean_object* v_ofLeGe_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_201_, v_ofLeGe_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofZeroDvd_elim___redArg(lean_object* v_t_205_, lean_object* v_ofZeroDvd_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_205_, v_ofZeroDvd_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofZeroDvd_elim(lean_object* v_motive__2_208_, lean_object* v_t_209_, lean_object* v_h_210_, lean_object* v_ofZeroDvd_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_209_, v_ofZeroDvd_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_reorder_elim___redArg(lean_object* v_t_213_, lean_object* v_reorder_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_213_, v_reorder_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_reorder_elim(lean_object* v_motive__2_216_, lean_object* v_t_217_, lean_object* v_h_218_, lean_object* v_reorder_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_217_, v_reorder_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_commRingNorm_elim___redArg(lean_object* v_t_221_, lean_object* v_commRingNorm_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_221_, v_commRingNorm_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_commRingNorm_elim(lean_object* v_motive__2_224_, lean_object* v_t_225_, lean_object* v_h_226_, lean_object* v_commRingNorm_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_225_, v_commRingNorm_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnCommRing_elim___redArg(lean_object* v_t_229_, lean_object* v_defnCommRing_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_229_, v_defnCommRing_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnCommRing_elim(lean_object* v_motive__2_232_, lean_object* v_t_233_, lean_object* v_h_234_, lean_object* v_defnCommRing_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_233_, v_defnCommRing_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnNatCommRing_elim___redArg(lean_object* v_t_237_, lean_object* v_defnNatCommRing_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_237_, v_defnNatCommRing_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnNatCommRing_elim(lean_object* v_motive__2_240_, lean_object* v_t_241_, lean_object* v_h_242_, lean_object* v_defnNatCommRing_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_241_, v_defnNatCommRing_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mul_elim___redArg(lean_object* v_t_245_, lean_object* v_mul_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_245_, v_mul_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mul_elim(lean_object* v_motive__2_248_, lean_object* v_t_249_, lean_object* v_h_250_, lean_object* v_mul_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_249_, v_mul_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_div_elim___redArg(lean_object* v_t_253_, lean_object* v_div_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_253_, v_div_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_div_elim(lean_object* v_motive__2_256_, lean_object* v_t_257_, lean_object* v_h_258_, lean_object* v_div_259_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_257_, v_div_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mod_elim___redArg(lean_object* v_t_261_, lean_object* v_mod_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_261_, v_mod_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mod_elim(lean_object* v_motive__2_264_, lean_object* v_t_265_, lean_object* v_h_266_, lean_object* v_mod_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_265_, v_mod_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_pow_elim___redArg(lean_object* v_t_269_, lean_object* v_pow_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_269_, v_pow_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_pow_elim(lean_object* v_motive__2_272_, lean_object* v_t_273_, lean_object* v_h_274_, lean_object* v_pow_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_273_, v_pow_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorIdx___impl(lean_object* v_x_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = lean_obj_tag_nat(v_x_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorIdx___impl___boxed(lean_object* v_x_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorIdx___impl(v_x_279_);
lean_dec_ref(v_x_279_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(lean_object* v_t_281_, lean_object* v_k_282_){
_start:
{
if (lean_obj_tag(v_t_281_) == 0)
{
lean_object* v_h_283_; lean_object* v___x_284_; 
v_h_283_ = lean_ctor_get(v_t_281_, 0);
lean_inc(v_h_283_);
lean_dec_ref_known(v_t_281_, 1);
v___x_284_ = lean_apply_1(v_k_282_, v_h_283_);
return v___x_284_;
}
else
{
lean_object* v_hs_285_; lean_object* v_decVars_286_; lean_object* v___x_287_; 
v_hs_285_ = lean_ctor_get(v_t_281_, 0);
lean_inc_ref(v_hs_285_);
v_decVars_286_ = lean_ctor_get(v_t_281_, 1);
lean_inc_ref(v_decVars_286_);
lean_dec_ref_known(v_t_281_, 2);
v___x_287_ = lean_apply_2(v_k_282_, v_hs_285_, v_decVars_286_);
return v___x_287_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim(lean_object* v_motive__6_288_, lean_object* v_ctorIdx_289_, lean_object* v_t_290_, lean_object* v_h_291_, lean_object* v_k_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_290_, v_k_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___boxed(lean_object* v_motive__6_294_, lean_object* v_ctorIdx_295_, lean_object* v_t_296_, lean_object* v_h_297_, lean_object* v_k_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim(v_motive__6_294_, v_ctorIdx_295_, v_t_296_, v_h_297_, v_k_298_);
lean_dec(v_ctorIdx_295_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_dec_elim___redArg(lean_object* v_t_300_, lean_object* v_dec_301_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_300_, v_dec_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_dec_elim(lean_object* v_motive__6_303_, lean_object* v_t_304_, lean_object* v_h_305_, lean_object* v_dec_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_304_, v_dec_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_last_elim___redArg(lean_object* v_t_308_, lean_object* v_last_309_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_308_, v_last_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_last_elim(lean_object* v_motive__6_311_, lean_object* v_t_312_, lean_object* v_h_313_, lean_object* v_last_314_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_312_, v_last_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorIdx___impl(lean_object* v_x_316_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = lean_obj_tag_nat(v_x_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorIdx___impl___boxed(lean_object* v_x_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorIdx___impl(v_x_318_);
lean_dec_ref(v_x_318_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(lean_object* v_t_320_, lean_object* v_k_321_){
_start:
{
switch(lean_obj_tag(v_t_320_))
{
case 1:
{
lean_object* v_e_322_; lean_object* v_thm_323_; lean_object* v_d_324_; lean_object* v_a_325_; lean_object* v___x_326_; 
v_e_322_ = lean_ctor_get(v_t_320_, 0);
lean_inc_ref(v_e_322_);
v_thm_323_ = lean_ctor_get(v_t_320_, 1);
lean_inc_ref(v_thm_323_);
v_d_324_ = lean_ctor_get(v_t_320_, 2);
lean_inc(v_d_324_);
v_a_325_ = lean_ctor_get(v_t_320_, 3);
lean_inc_ref(v_a_325_);
lean_dec_ref_known(v_t_320_, 4);
v___x_326_ = lean_apply_4(v_k_321_, v_e_322_, v_thm_323_, v_d_324_, v_a_325_);
return v___x_326_;
}
case 4:
{
lean_object* v_c_u2081_327_; lean_object* v_c_u2082_328_; lean_object* v___x_329_; 
v_c_u2081_327_ = lean_ctor_get(v_t_320_, 0);
lean_inc_ref(v_c_u2081_327_);
v_c_u2082_328_ = lean_ctor_get(v_t_320_, 1);
lean_inc_ref(v_c_u2082_328_);
lean_dec_ref_known(v_t_320_, 2);
v___x_329_ = lean_apply_2(v_k_321_, v_c_u2081_327_, v_c_u2082_328_);
return v___x_329_;
}
case 5:
{
lean_object* v_c_u2081_330_; lean_object* v_c_u2082_331_; lean_object* v___x_332_; 
v_c_u2081_330_ = lean_ctor_get(v_t_320_, 0);
lean_inc_ref(v_c_u2081_330_);
v_c_u2082_331_ = lean_ctor_get(v_t_320_, 1);
lean_inc_ref(v_c_u2082_331_);
lean_dec_ref_known(v_t_320_, 2);
v___x_332_ = lean_apply_2(v_k_321_, v_c_u2081_330_, v_c_u2082_331_);
return v___x_332_;
}
case 7:
{
lean_object* v_x_333_; lean_object* v_c_334_; lean_object* v___x_335_; 
v_x_333_ = lean_ctor_get(v_t_320_, 0);
lean_inc(v_x_333_);
v_c_334_ = lean_ctor_get(v_t_320_, 1);
lean_inc_ref(v_c_334_);
lean_dec_ref_known(v_t_320_, 2);
v___x_335_ = lean_apply_2(v_k_321_, v_x_333_, v_c_334_);
return v___x_335_;
}
case 8:
{
lean_object* v_x_336_; lean_object* v_c_u2081_337_; lean_object* v_c_u2082_338_; lean_object* v___x_339_; 
v_x_336_ = lean_ctor_get(v_t_320_, 0);
lean_inc(v_x_336_);
v_c_u2081_337_ = lean_ctor_get(v_t_320_, 1);
lean_inc_ref(v_c_u2081_337_);
v_c_u2082_338_ = lean_ctor_get(v_t_320_, 2);
lean_inc_ref(v_c_u2082_338_);
lean_dec_ref_known(v_t_320_, 3);
v___x_339_ = lean_apply_3(v_k_321_, v_x_336_, v_c_u2081_337_, v_c_u2082_338_);
return v___x_339_;
}
case 12:
{
lean_object* v_c_340_; lean_object* v_e_341_; lean_object* v_p_342_; lean_object* v___x_343_; 
v_c_340_ = lean_ctor_get(v_t_320_, 0);
lean_inc_ref(v_c_340_);
v_e_341_ = lean_ctor_get(v_t_320_, 1);
lean_inc_ref(v_e_341_);
v_p_342_ = lean_ctor_get(v_t_320_, 2);
lean_inc_ref(v_p_342_);
lean_dec_ref_known(v_t_320_, 3);
v___x_343_ = lean_apply_3(v_k_321_, v_c_340_, v_e_341_, v_p_342_);
return v___x_343_;
}
default: 
{
lean_object* v_e_344_; lean_object* v___x_345_; 
v_e_344_ = lean_ctor_get(v_t_320_, 0);
lean_inc_ref(v_e_344_);
lean_dec_ref(v_t_320_);
v___x_345_ = lean_apply_1(v_k_321_, v_e_344_);
return v___x_345_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim(lean_object* v_motive__7_346_, lean_object* v_ctorIdx_347_, lean_object* v_t_348_, lean_object* v_h_349_, lean_object* v_k_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_348_, v_k_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___boxed(lean_object* v_motive__7_352_, lean_object* v_ctorIdx_353_, lean_object* v_t_354_, lean_object* v_h_355_, lean_object* v_k_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim(v_motive__7_352_, v_ctorIdx_353_, v_t_354_, v_h_355_, v_k_356_);
lean_dec(v_ctorIdx_353_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_core_elim___redArg(lean_object* v_t_358_, lean_object* v_core_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_358_, v_core_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_core_elim(lean_object* v_motive__7_361_, lean_object* v_t_362_, lean_object* v_h_363_, lean_object* v_core_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_362_, v_core_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_coreOfNat_elim___redArg(lean_object* v_t_366_, lean_object* v_coreOfNat_367_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_366_, v_coreOfNat_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_coreOfNat_elim(lean_object* v_motive__7_369_, lean_object* v_t_370_, lean_object* v_h_371_, lean_object* v_coreOfNat_372_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_370_, v_coreOfNat_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_norm_elim___redArg(lean_object* v_t_374_, lean_object* v_norm_375_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_374_, v_norm_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_norm_elim(lean_object* v_motive__7_377_, lean_object* v_t_378_, lean_object* v_h_379_, lean_object* v_norm_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_378_, v_norm_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_divCoeffs_elim___redArg(lean_object* v_t_382_, lean_object* v_divCoeffs_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_382_, v_divCoeffs_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_divCoeffs_elim(lean_object* v_motive__7_385_, lean_object* v_t_386_, lean_object* v_h_387_, lean_object* v_divCoeffs_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_386_, v_divCoeffs_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveCombine_elim___redArg(lean_object* v_t_390_, lean_object* v_solveCombine_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_390_, v_solveCombine_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveCombine_elim(lean_object* v_motive__7_393_, lean_object* v_t_394_, lean_object* v_h_395_, lean_object* v_solveCombine_396_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_394_, v_solveCombine_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveElim_elim___redArg(lean_object* v_t_398_, lean_object* v_solveElim_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_398_, v_solveElim_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveElim_elim(lean_object* v_motive__7_401_, lean_object* v_t_402_, lean_object* v_h_403_, lean_object* v_solveElim_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_402_, v_solveElim_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_elim_elim___redArg(lean_object* v_t_406_, lean_object* v_elim_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_406_, v_elim_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_elim_elim(lean_object* v_motive__7_409_, lean_object* v_t_410_, lean_object* v_h_411_, lean_object* v_elim_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_410_, v_elim_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ofEq_elim___redArg(lean_object* v_t_414_, lean_object* v_ofEq_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_414_, v_ofEq_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ofEq_elim(lean_object* v_motive__7_417_, lean_object* v_t_418_, lean_object* v_h_419_, lean_object* v_ofEq_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_418_, v_ofEq_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_subst_elim___redArg(lean_object* v_t_422_, lean_object* v_subst_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_422_, v_subst_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_subst_elim(lean_object* v_motive__7_425_, lean_object* v_t_426_, lean_object* v_h_427_, lean_object* v_subst_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_426_, v_subst_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2081_elim___redArg(lean_object* v_t_430_, lean_object* v_cooper_u2081_431_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_430_, v_cooper_u2081_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2081_elim(lean_object* v_motive__7_433_, lean_object* v_t_434_, lean_object* v_h_435_, lean_object* v_cooper_u2081_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_434_, v_cooper_u2081_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2082_elim___redArg(lean_object* v_t_438_, lean_object* v_cooper_u2082_439_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_438_, v_cooper_u2082_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2082_elim(lean_object* v_motive__7_441_, lean_object* v_t_442_, lean_object* v_h_443_, lean_object* v_cooper_u2082_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_442_, v_cooper_u2082_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_reorder_elim___redArg(lean_object* v_t_446_, lean_object* v_reorder_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_446_, v_reorder_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_reorder_elim(lean_object* v_motive__7_449_, lean_object* v_t_450_, lean_object* v_h_451_, lean_object* v_reorder_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_450_, v_reorder_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_commRingNorm_elim___redArg(lean_object* v_t_454_, lean_object* v_commRingNorm_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_454_, v_commRingNorm_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_commRingNorm_elim(lean_object* v_motive__7_457_, lean_object* v_t_458_, lean_object* v_h_459_, lean_object* v_commRingNorm_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_458_, v_commRingNorm_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorIdx___impl(lean_object* v_x_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = lean_obj_tag_nat(v_x_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorIdx___impl___boxed(lean_object* v_x_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorIdx___impl(v_x_464_);
lean_dec_ref(v_x_464_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(lean_object* v_t_466_, lean_object* v_k_467_){
_start:
{
switch(lean_obj_tag(v_t_466_))
{
case 1:
{
lean_object* v_e_468_; lean_object* v_p_469_; lean_object* v___x_470_; 
v_e_468_ = lean_ctor_get(v_t_466_, 0);
lean_inc_ref(v_e_468_);
v_p_469_ = lean_ctor_get(v_t_466_, 1);
lean_inc_ref(v_p_469_);
lean_dec_ref_known(v_t_466_, 2);
v___x_470_ = lean_apply_2(v_k_467_, v_e_468_, v_p_469_);
return v___x_470_;
}
case 2:
{
lean_object* v_e_471_; uint8_t v_pos_472_; lean_object* v_toIntThm_473_; lean_object* v_lhs_474_; lean_object* v_rhs_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v_e_471_ = lean_ctor_get(v_t_466_, 0);
lean_inc_ref(v_e_471_);
v_pos_472_ = lean_ctor_get_uint8(v_t_466_, sizeof(void*)*4);
v_toIntThm_473_ = lean_ctor_get(v_t_466_, 1);
lean_inc_ref(v_toIntThm_473_);
v_lhs_474_ = lean_ctor_get(v_t_466_, 2);
lean_inc_ref(v_lhs_474_);
v_rhs_475_ = lean_ctor_get(v_t_466_, 3);
lean_inc_ref(v_rhs_475_);
lean_dec_ref_known(v_t_466_, 4);
v___x_476_ = lean_box(v_pos_472_);
v___x_477_ = lean_apply_5(v_k_467_, v_e_471_, v___x_476_, v_toIntThm_473_, v_lhs_474_, v_rhs_475_);
return v___x_477_;
}
case 5:
{
lean_object* v_h_478_; lean_object* v___x_479_; 
v_h_478_ = lean_ctor_get(v_t_466_, 0);
lean_inc(v_h_478_);
lean_dec_ref_known(v_t_466_, 1);
v___x_479_ = lean_apply_1(v_k_467_, v_h_478_);
return v___x_479_;
}
case 8:
{
lean_object* v_c_u2081_480_; lean_object* v_c_u2082_481_; lean_object* v___x_482_; 
v_c_u2081_480_ = lean_ctor_get(v_t_466_, 0);
lean_inc_ref(v_c_u2081_480_);
v_c_u2082_481_ = lean_ctor_get(v_t_466_, 1);
lean_inc_ref(v_c_u2082_481_);
lean_dec_ref_known(v_t_466_, 2);
v___x_482_ = lean_apply_2(v_k_467_, v_c_u2081_480_, v_c_u2082_481_);
return v___x_482_;
}
case 9:
{
lean_object* v_c_u2081_483_; lean_object* v_c_u2082_484_; lean_object* v_k_485_; lean_object* v___x_486_; 
v_c_u2081_483_ = lean_ctor_get(v_t_466_, 0);
lean_inc_ref(v_c_u2081_483_);
v_c_u2082_484_ = lean_ctor_get(v_t_466_, 1);
lean_inc_ref(v_c_u2082_484_);
v_k_485_ = lean_ctor_get(v_t_466_, 2);
lean_inc(v_k_485_);
lean_dec_ref_known(v_t_466_, 3);
v___x_486_ = lean_apply_3(v_k_467_, v_c_u2081_483_, v_c_u2082_484_, v_k_485_);
return v___x_486_;
}
case 10:
{
lean_object* v_x_487_; lean_object* v_c_u2081_488_; lean_object* v_c_u2082_489_; lean_object* v___x_490_; 
v_x_487_ = lean_ctor_get(v_t_466_, 0);
lean_inc(v_x_487_);
v_c_u2081_488_ = lean_ctor_get(v_t_466_, 1);
lean_inc_ref(v_c_u2081_488_);
v_c_u2082_489_ = lean_ctor_get(v_t_466_, 2);
lean_inc_ref(v_c_u2082_489_);
lean_dec_ref_known(v_t_466_, 3);
v___x_490_ = lean_apply_3(v_k_467_, v_x_487_, v_c_u2081_488_, v_c_u2082_489_);
return v___x_490_;
}
case 11:
{
lean_object* v_c_u2081_491_; lean_object* v_c_u2082_492_; lean_object* v___x_493_; 
v_c_u2081_491_ = lean_ctor_get(v_t_466_, 0);
lean_inc_ref(v_c_u2081_491_);
v_c_u2082_492_ = lean_ctor_get(v_t_466_, 1);
lean_inc_ref(v_c_u2082_492_);
lean_dec_ref_known(v_t_466_, 2);
v___x_493_ = lean_apply_2(v_k_467_, v_c_u2081_491_, v_c_u2082_492_);
return v___x_493_;
}
case 12:
{
lean_object* v_c_u2081_494_; lean_object* v_decVar_495_; lean_object* v_h_496_; lean_object* v_decVars_497_; lean_object* v___x_498_; 
v_c_u2081_494_ = lean_ctor_get(v_t_466_, 0);
lean_inc_ref(v_c_u2081_494_);
v_decVar_495_ = lean_ctor_get(v_t_466_, 1);
lean_inc(v_decVar_495_);
v_h_496_ = lean_ctor_get(v_t_466_, 2);
lean_inc_ref(v_h_496_);
v_decVars_497_ = lean_ctor_get(v_t_466_, 3);
lean_inc_ref(v_decVars_497_);
lean_dec_ref_known(v_t_466_, 4);
v___x_498_ = lean_apply_4(v_k_467_, v_c_u2081_494_, v_decVar_495_, v_h_496_, v_decVars_497_);
return v___x_498_;
}
case 14:
{
lean_object* v_c_u2081_499_; lean_object* v_c_u2082_500_; lean_object* v___x_501_; 
v_c_u2081_499_ = lean_ctor_get(v_t_466_, 0);
lean_inc_ref(v_c_u2081_499_);
v_c_u2082_500_ = lean_ctor_get(v_t_466_, 1);
lean_inc_ref(v_c_u2082_500_);
lean_dec_ref_known(v_t_466_, 2);
v___x_501_ = lean_apply_2(v_k_467_, v_c_u2081_499_, v_c_u2082_500_);
return v___x_501_;
}
case 15:
{
lean_object* v_c_u2081_502_; lean_object* v_c_u2082_503_; lean_object* v___x_504_; 
v_c_u2081_502_ = lean_ctor_get(v_t_466_, 0);
lean_inc_ref(v_c_u2081_502_);
v_c_u2082_503_ = lean_ctor_get(v_t_466_, 1);
lean_inc_ref(v_c_u2082_503_);
lean_dec_ref_known(v_t_466_, 2);
v___x_504_ = lean_apply_2(v_k_467_, v_c_u2081_502_, v_c_u2082_503_);
return v___x_504_;
}
case 17:
{
lean_object* v_c_505_; lean_object* v_e_506_; lean_object* v_p_507_; lean_object* v___x_508_; 
v_c_505_ = lean_ctor_get(v_t_466_, 0);
lean_inc_ref(v_c_505_);
v_e_506_ = lean_ctor_get(v_t_466_, 1);
lean_inc_ref(v_e_506_);
v_p_507_ = lean_ctor_get(v_t_466_, 2);
lean_inc_ref(v_p_507_);
lean_dec_ref_known(v_t_466_, 3);
v___x_508_ = lean_apply_3(v_k_467_, v_c_505_, v_e_506_, v_p_507_);
return v___x_508_;
}
default: 
{
lean_object* v_e_509_; lean_object* v___x_510_; 
v_e_509_ = lean_ctor_get(v_t_466_, 0);
lean_inc_ref(v_e_509_);
lean_dec_ref(v_t_466_);
v___x_510_ = lean_apply_1(v_k_467_, v_e_509_);
return v___x_510_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim(lean_object* v_motive__9_511_, lean_object* v_ctorIdx_512_, lean_object* v_t_513_, lean_object* v_h_514_, lean_object* v_k_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_513_, v_k_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___boxed(lean_object* v_motive__9_517_, lean_object* v_ctorIdx_518_, lean_object* v_t_519_, lean_object* v_h_520_, lean_object* v_k_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim(v_motive__9_517_, v_ctorIdx_518_, v_t_519_, v_h_520_, v_k_521_);
lean_dec(v_ctorIdx_518_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_core_elim___redArg(lean_object* v_t_523_, lean_object* v_core_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_523_, v_core_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_core_elim(lean_object* v_motive__9_526_, lean_object* v_t_527_, lean_object* v_h_528_, lean_object* v_core_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_527_, v_core_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreNeg_elim___redArg(lean_object* v_t_531_, lean_object* v_coreNeg_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_531_, v_coreNeg_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreNeg_elim(lean_object* v_motive__9_534_, lean_object* v_t_535_, lean_object* v_h_536_, lean_object* v_coreNeg_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_535_, v_coreNeg_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreToInt_elim___redArg(lean_object* v_t_539_, lean_object* v_coreToInt_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_539_, v_coreToInt_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreToInt_elim(lean_object* v_motive__9_542_, lean_object* v_t_543_, lean_object* v_h_544_, lean_object* v_coreToInt_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_543_, v_coreToInt_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofNatNonneg_elim___redArg(lean_object* v_t_547_, lean_object* v_ofNatNonneg_548_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_547_, v_ofNatNonneg_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofNatNonneg_elim(lean_object* v_motive__9_550_, lean_object* v_t_551_, lean_object* v_h_552_, lean_object* v_ofNatNonneg_553_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_551_, v_ofNatNonneg_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_bound_elim___redArg(lean_object* v_t_555_, lean_object* v_bound_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_555_, v_bound_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_bound_elim(lean_object* v_motive__9_558_, lean_object* v_t_559_, lean_object* v_h_560_, lean_object* v_bound_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_559_, v_bound_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dec_elim___redArg(lean_object* v_t_563_, lean_object* v_dec_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_563_, v_dec_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dec_elim(lean_object* v_motive__9_566_, lean_object* v_t_567_, lean_object* v_h_568_, lean_object* v_dec_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_567_, v_dec_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_norm_elim___redArg(lean_object* v_t_571_, lean_object* v_norm_572_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_571_, v_norm_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_norm_elim(lean_object* v_motive__9_574_, lean_object* v_t_575_, lean_object* v_h_576_, lean_object* v_norm_577_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_575_, v_norm_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_divCoeffs_elim___redArg(lean_object* v_t_579_, lean_object* v_divCoeffs_580_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_579_, v_divCoeffs_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_divCoeffs_elim(lean_object* v_motive__9_582_, lean_object* v_t_583_, lean_object* v_h_584_, lean_object* v_divCoeffs_585_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_583_, v_divCoeffs_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combine_elim___redArg(lean_object* v_t_587_, lean_object* v_combine_588_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_587_, v_combine_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combine_elim(lean_object* v_motive__9_590_, lean_object* v_t_591_, lean_object* v_h_592_, lean_object* v_combine_593_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_591_, v_combine_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combineDivCoeffs_elim___redArg(lean_object* v_t_595_, lean_object* v_combineDivCoeffs_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_595_, v_combineDivCoeffs_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combineDivCoeffs_elim(lean_object* v_motive__9_598_, lean_object* v_t_599_, lean_object* v_h_600_, lean_object* v_combineDivCoeffs_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_599_, v_combineDivCoeffs_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_subst_elim___redArg(lean_object* v_t_603_, lean_object* v_subst_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_603_, v_subst_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_subst_elim(lean_object* v_motive__9_606_, lean_object* v_t_607_, lean_object* v_h_608_, lean_object* v_subst_609_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_607_, v_subst_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofLeDiseq_elim___redArg(lean_object* v_t_611_, lean_object* v_ofLeDiseq_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_611_, v_ofLeDiseq_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofLeDiseq_elim(lean_object* v_motive__9_614_, lean_object* v_t_615_, lean_object* v_h_616_, lean_object* v_ofLeDiseq_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_615_, v_ofLeDiseq_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofDiseqSplit_elim___redArg(lean_object* v_t_619_, lean_object* v_ofDiseqSplit_620_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_619_, v_ofDiseqSplit_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofDiseqSplit_elim(lean_object* v_motive__9_622_, lean_object* v_t_623_, lean_object* v_h_624_, lean_object* v_ofDiseqSplit_625_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_623_, v_ofDiseqSplit_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_cooper_elim___redArg(lean_object* v_t_627_, lean_object* v_cooper_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_627_, v_cooper_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_cooper_elim(lean_object* v_motive__9_630_, lean_object* v_t_631_, lean_object* v_h_632_, lean_object* v_cooper_633_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_631_, v_cooper_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dvdTight_elim___redArg(lean_object* v_t_635_, lean_object* v_dvdTight_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_635_, v_dvdTight_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dvdTight_elim(lean_object* v_motive__9_638_, lean_object* v_t_639_, lean_object* v_h_640_, lean_object* v_dvdTight_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_639_, v_dvdTight_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_negDvdTight_elim___redArg(lean_object* v_t_643_, lean_object* v_negDvdTight_644_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_643_, v_negDvdTight_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_negDvdTight_elim(lean_object* v_motive__9_646_, lean_object* v_t_647_, lean_object* v_h_648_, lean_object* v_negDvdTight_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_647_, v_negDvdTight_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_reorder_elim___redArg(lean_object* v_t_651_, lean_object* v_reorder_652_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_651_, v_reorder_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_reorder_elim(lean_object* v_motive__9_654_, lean_object* v_t_655_, lean_object* v_h_656_, lean_object* v_reorder_657_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_655_, v_reorder_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_commRingNorm_elim___redArg(lean_object* v_t_659_, lean_object* v_commRingNorm_660_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_659_, v_commRingNorm_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_commRingNorm_elim(lean_object* v_motive__9_662_, lean_object* v_t_663_, lean_object* v_h_664_, lean_object* v_commRingNorm_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_663_, v_commRingNorm_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorIdx___impl(lean_object* v_x_667_){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = lean_obj_tag_nat(v_x_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorIdx___impl___boxed(lean_object* v_x_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorIdx___impl(v_x_669_);
lean_dec_ref(v_x_669_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(lean_object* v_t_671_, lean_object* v_k_672_){
_start:
{
switch(lean_obj_tag(v_t_671_))
{
case 0:
{
lean_object* v_a_673_; lean_object* v_zero_674_; lean_object* v___x_675_; 
v_a_673_ = lean_ctor_get(v_t_671_, 0);
lean_inc_ref(v_a_673_);
v_zero_674_ = lean_ctor_get(v_t_671_, 1);
lean_inc_ref(v_zero_674_);
lean_dec_ref_known(v_t_671_, 2);
v___x_675_ = lean_apply_2(v_k_672_, v_a_673_, v_zero_674_);
return v___x_675_;
}
case 1:
{
lean_object* v_a_676_; lean_object* v_b_677_; lean_object* v_p_u2081_678_; lean_object* v_p_u2082_679_; lean_object* v___x_680_; 
v_a_676_ = lean_ctor_get(v_t_671_, 0);
lean_inc_ref(v_a_676_);
v_b_677_ = lean_ctor_get(v_t_671_, 1);
lean_inc_ref(v_b_677_);
v_p_u2081_678_ = lean_ctor_get(v_t_671_, 2);
lean_inc_ref(v_p_u2081_678_);
v_p_u2082_679_ = lean_ctor_get(v_t_671_, 3);
lean_inc_ref(v_p_u2082_679_);
lean_dec_ref_known(v_t_671_, 4);
v___x_680_ = lean_apply_4(v_k_672_, v_a_676_, v_b_677_, v_p_u2081_678_, v_p_u2082_679_);
return v___x_680_;
}
case 2:
{
lean_object* v_a_681_; lean_object* v_b_682_; lean_object* v_toIntThm_683_; lean_object* v_lhs_684_; lean_object* v_rhs_685_; lean_object* v___x_686_; 
v_a_681_ = lean_ctor_get(v_t_671_, 0);
lean_inc_ref(v_a_681_);
v_b_682_ = lean_ctor_get(v_t_671_, 1);
lean_inc_ref(v_b_682_);
v_toIntThm_683_ = lean_ctor_get(v_t_671_, 2);
lean_inc_ref(v_toIntThm_683_);
v_lhs_684_ = lean_ctor_get(v_t_671_, 3);
lean_inc_ref(v_lhs_684_);
v_rhs_685_ = lean_ctor_get(v_t_671_, 4);
lean_inc_ref(v_rhs_685_);
lean_dec_ref_known(v_t_671_, 5);
v___x_686_ = lean_apply_5(v_k_672_, v_a_681_, v_b_682_, v_toIntThm_683_, v_lhs_684_, v_rhs_685_);
return v___x_686_;
}
case 6:
{
lean_object* v_x_687_; lean_object* v_c_u2081_688_; lean_object* v_c_u2082_689_; lean_object* v___x_690_; 
v_x_687_ = lean_ctor_get(v_t_671_, 0);
lean_inc(v_x_687_);
v_c_u2081_688_ = lean_ctor_get(v_t_671_, 1);
lean_inc_ref(v_c_u2081_688_);
v_c_u2082_689_ = lean_ctor_get(v_t_671_, 2);
lean_inc_ref(v_c_u2082_689_);
lean_dec_ref_known(v_t_671_, 3);
v___x_690_ = lean_apply_3(v_k_672_, v_x_687_, v_c_u2081_688_, v_c_u2082_689_);
return v___x_690_;
}
case 8:
{
lean_object* v_c_691_; lean_object* v_e_692_; lean_object* v_p_693_; lean_object* v___x_694_; 
v_c_691_ = lean_ctor_get(v_t_671_, 0);
lean_inc_ref(v_c_691_);
v_e_692_ = lean_ctor_get(v_t_671_, 1);
lean_inc_ref(v_e_692_);
v_p_693_ = lean_ctor_get(v_t_671_, 2);
lean_inc_ref(v_p_693_);
lean_dec_ref_known(v_t_671_, 3);
v___x_694_ = lean_apply_3(v_k_672_, v_c_691_, v_e_692_, v_p_693_);
return v___x_694_;
}
default: 
{
lean_object* v_c_695_; lean_object* v___x_696_; 
v_c_695_ = lean_ctor_get(v_t_671_, 0);
lean_inc_ref(v_c_695_);
lean_dec_ref(v_t_671_);
v___x_696_ = lean_apply_1(v_k_672_, v_c_695_);
return v___x_696_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim(lean_object* v_motive__11_697_, lean_object* v_ctorIdx_698_, lean_object* v_t_699_, lean_object* v_h_700_, lean_object* v_k_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_699_, v_k_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___boxed(lean_object* v_motive__11_703_, lean_object* v_ctorIdx_704_, lean_object* v_t_705_, lean_object* v_h_706_, lean_object* v_k_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim(v_motive__11_703_, v_ctorIdx_704_, v_t_705_, v_h_706_, v_k_707_);
lean_dec(v_ctorIdx_704_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core0_elim___redArg(lean_object* v_t_709_, lean_object* v_core0_710_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_709_, v_core0_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core0_elim(lean_object* v_motive__11_712_, lean_object* v_t_713_, lean_object* v_h_714_, lean_object* v_core0_715_){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_713_, v_core0_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core_elim___redArg(lean_object* v_t_717_, lean_object* v_core_718_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_717_, v_core_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core_elim(lean_object* v_motive__11_720_, lean_object* v_t_721_, lean_object* v_h_722_, lean_object* v_core_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_721_, v_core_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_coreToInt_elim___redArg(lean_object* v_t_725_, lean_object* v_coreToInt_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_725_, v_coreToInt_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_coreToInt_elim(lean_object* v_motive__11_728_, lean_object* v_t_729_, lean_object* v_h_730_, lean_object* v_coreToInt_731_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_729_, v_coreToInt_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_norm_elim___redArg(lean_object* v_t_733_, lean_object* v_norm_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_733_, v_norm_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_norm_elim(lean_object* v_motive__11_736_, lean_object* v_t_737_, lean_object* v_h_738_, lean_object* v_norm_739_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_737_, v_norm_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_divCoeffs_elim___redArg(lean_object* v_t_741_, lean_object* v_divCoeffs_742_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_741_, v_divCoeffs_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_divCoeffs_elim(lean_object* v_motive__11_744_, lean_object* v_t_745_, lean_object* v_h_746_, lean_object* v_divCoeffs_747_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_745_, v_divCoeffs_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_neg_elim___redArg(lean_object* v_t_749_, lean_object* v_neg_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_749_, v_neg_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_neg_elim(lean_object* v_motive__11_752_, lean_object* v_t_753_, lean_object* v_h_754_, lean_object* v_neg_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_753_, v_neg_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_subst_elim___redArg(lean_object* v_t_757_, lean_object* v_subst_758_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_757_, v_subst_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_subst_elim(lean_object* v_motive__11_760_, lean_object* v_t_761_, lean_object* v_h_762_, lean_object* v_subst_763_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_761_, v_subst_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_reorder_elim___redArg(lean_object* v_t_765_, lean_object* v_reorder_766_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_765_, v_reorder_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_reorder_elim(lean_object* v_motive__11_768_, lean_object* v_t_769_, lean_object* v_h_770_, lean_object* v_reorder_771_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_769_, v_reorder_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_commRingNorm_elim___redArg(lean_object* v_t_773_, lean_object* v_commRingNorm_774_){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_773_, v_commRingNorm_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_commRingNorm_elim(lean_object* v_motive__11_776_, lean_object* v_t_777_, lean_object* v_h_778_, lean_object* v_commRingNorm_779_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_777_, v_commRingNorm_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorIdx___impl(lean_object* v_x_781_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = lean_obj_tag_nat(v_x_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorIdx___impl___boxed(lean_object* v_x_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorIdx___impl(v_x_783_);
lean_dec_ref(v_x_783_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(lean_object* v_t_785_, lean_object* v_k_786_){
_start:
{
if (lean_obj_tag(v_t_785_) == 4)
{
lean_object* v_c_u2081_787_; lean_object* v_c_u2082_788_; lean_object* v_c_u2083_789_; lean_object* v___x_790_; 
v_c_u2081_787_ = lean_ctor_get(v_t_785_, 0);
lean_inc_ref(v_c_u2081_787_);
v_c_u2082_788_ = lean_ctor_get(v_t_785_, 1);
lean_inc_ref(v_c_u2082_788_);
v_c_u2083_789_ = lean_ctor_get(v_t_785_, 2);
lean_inc_ref(v_c_u2083_789_);
lean_dec_ref_known(v_t_785_, 3);
v___x_790_ = lean_apply_3(v_k_786_, v_c_u2081_787_, v_c_u2082_788_, v_c_u2083_789_);
return v___x_790_;
}
else
{
lean_object* v_c_791_; lean_object* v___x_792_; 
v_c_791_ = lean_ctor_get(v_t_785_, 0);
lean_inc_ref(v_c_791_);
lean_dec_ref(v_t_785_);
v___x_792_ = lean_apply_1(v_k_786_, v_c_791_);
return v___x_792_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim(lean_object* v_motive__12_793_, lean_object* v_ctorIdx_794_, lean_object* v_t_795_, lean_object* v_h_796_, lean_object* v_k_797_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_795_, v_k_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___boxed(lean_object* v_motive__12_799_, lean_object* v_ctorIdx_800_, lean_object* v_t_801_, lean_object* v_h_802_, lean_object* v_k_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim(v_motive__12_799_, v_ctorIdx_800_, v_t_801_, v_h_802_, v_k_803_);
lean_dec(v_ctorIdx_800_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_dvd_elim___redArg(lean_object* v_t_805_, lean_object* v_dvd_806_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_805_, v_dvd_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_dvd_elim(lean_object* v_motive__12_808_, lean_object* v_t_809_, lean_object* v_h_810_, lean_object* v_dvd_811_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_809_, v_dvd_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_le_elim___redArg(lean_object* v_t_813_, lean_object* v_le_814_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_813_, v_le_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_le_elim(lean_object* v_motive__12_816_, lean_object* v_t_817_, lean_object* v_h_818_, lean_object* v_le_819_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_817_, v_le_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_eq_elim___redArg(lean_object* v_t_821_, lean_object* v_eq_822_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_821_, v_eq_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_eq_elim(lean_object* v_motive__12_824_, lean_object* v_t_825_, lean_object* v_h_826_, lean_object* v_eq_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_825_, v_eq_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_diseq_elim___redArg(lean_object* v_t_829_, lean_object* v_diseq_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_829_, v_diseq_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_diseq_elim(lean_object* v_motive__12_832_, lean_object* v_t_833_, lean_object* v_h_834_, lean_object* v_diseq_835_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_833_, v_diseq_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_cooper_elim___redArg(lean_object* v_t_837_, lean_object* v_cooper_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_837_, v_cooper_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_cooper_elim(lean_object* v_motive__12_840_, lean_object* v_t_841_, lean_object* v_h_842_, lean_object* v_cooper_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_841_, v_cooper_843_);
return v___x_844_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0(void){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0);
v___x_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
return v___x_846_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3(void){
_start:
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_850_ = lean_box(0);
v___x_851_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__2));
v___x_852_ = l_Lean_Expr_const___override(v___x_851_, v___x_850_);
return v___x_852_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4(void){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_853_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3);
v___x_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_854_, 0, v___x_853_);
return v___x_854_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5(void){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_855_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4);
v___x_856_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0);
v___x_857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_857_, 0, v___x_856_);
lean_ctor_set(v___x_857_, 1, v___x_855_);
return v___x_857_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr(void){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5);
return v___x_858_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0(void){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3);
v___x_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_860_, 0, v___x_859_);
return v___x_860_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1(void){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_861_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0);
v___x_862_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0);
v___x_863_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0);
v___x_864_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
lean_ctor_set(v___x_864_, 1, v___x_862_);
lean_ctor_set(v___x_864_, 2, v___x_861_);
return v___x_864_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr(void){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1);
return v___x_865_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0(void){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; uint8_t v___x_868_; lean_object* v___x_869_; 
v___x_866_ = lean_box(0);
v___x_867_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5);
v___x_868_ = 0;
v___x_869_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_869_, 0, v___x_867_);
lean_ctor_set(v___x_869_, 1, v___x_867_);
lean_ctor_set(v___x_869_, 2, v___x_866_);
lean_ctor_set_uint8(v___x_869_, sizeof(void*)*3, v___x_868_);
return v___x_869_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred(void){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0);
return v___x_870_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1(void){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_873_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__0));
v___x_874_ = lean_unsigned_to_nat(0u);
v___x_875_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0);
v___x_876_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
lean_ctor_set(v___x_876_, 1, v___x_874_);
lean_ctor_set(v___x_876_, 2, v___x_873_);
return v___x_876_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit(void){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1);
return v___x_877_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_878_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0);
v___x_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg(){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__1);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___boxed(lean_object* v___dummy_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg();
return v_res_884_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg();
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0(lean_object* v_00_u03b2_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0);
return v___x_887_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_888_ = lean_unsigned_to_nat(32u);
v___x_889_ = lean_mk_empty_array_with_capacity(v___x_888_);
v___x_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
return v___x_890_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1(void){
_start:
{
size_t v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_891_ = ((size_t)5ULL);
v___x_892_ = lean_unsigned_to_nat(0u);
v___x_893_ = lean_unsigned_to_nat(32u);
v___x_894_ = lean_mk_empty_array_with_capacity(v___x_893_);
v___x_895_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0);
v___x_896_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_896_, 0, v___x_895_);
lean_ctor_set(v___x_896_, 1, v___x_894_);
lean_ctor_set(v___x_896_, 2, v___x_892_);
lean_ctor_set(v___x_896_, 3, v___x_892_);
lean_ctor_set_usize(v___x_896_, 4, v___x_891_);
return v___x_896_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2(void){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_897_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0);
v___x_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_898_, 0, v___x_897_);
return v___x_898_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; uint8_t v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_899_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0);
v___x_900_ = lean_box(0);
v___x_901_ = 0;
v___x_902_ = lean_unsigned_to_nat(0u);
v___x_903_ = lean_box(0);
v___x_904_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2);
v___x_905_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1);
v___x_906_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v___x_906_, 0, v___x_905_);
lean_ctor_set(v___x_906_, 1, v___x_904_);
lean_ctor_set(v___x_906_, 2, v___x_905_);
lean_ctor_set(v___x_906_, 3, v___x_904_);
lean_ctor_set(v___x_906_, 4, v___x_904_);
lean_ctor_set(v___x_906_, 5, v___x_905_);
lean_ctor_set(v___x_906_, 6, v___x_905_);
lean_ctor_set(v___x_906_, 7, v___x_905_);
lean_ctor_set(v___x_906_, 8, v___x_905_);
lean_ctor_set(v___x_906_, 9, v___x_905_);
lean_ctor_set(v___x_906_, 10, v___x_903_);
lean_ctor_set(v___x_906_, 11, v___x_905_);
lean_ctor_set(v___x_906_, 12, v___x_905_);
lean_ctor_set(v___x_906_, 13, v___x_902_);
lean_ctor_set(v___x_906_, 14, v___x_902_);
lean_ctor_set(v___x_906_, 15, v___x_900_);
lean_ctor_set(v___x_906_, 16, v___x_904_);
lean_ctor_set(v___x_906_, 17, v___x_899_);
lean_ctor_set(v___x_906_, 18, v___x_904_);
lean_ctor_set_uint8(v___x_906_, sizeof(void*)*19, v___x_901_);
lean_ctor_set_uint8(v___x_906_, sizeof(void*)*19 + 1, v___x_901_);
return v___x_906_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default(void){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3);
return v___x_907_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState(void){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default;
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(lean_object* v___x_909_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_911_, 0, v___x_909_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2____boxed(lean_object* v___x_912_, lean_object* v___y_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(v___x_912_);
return v_res_914_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_915_; lean_object* v___f_916_; 
v___x_915_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3);
v___f_916_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_916_, 0, v___x_915_);
return v___f_916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_918_; lean_object* v___x_919_; 
v___f_918_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_);
v___x_919_ = l_Lean_Meta_Grind_registerSolverExtension___redArg(v___f_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2____boxed(lean_object* v_a_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_();
return v_res_921_;
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
