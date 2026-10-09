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
uint64_t l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(lean_object* v_x_3_){
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
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3_ = stack[0].m_obj;
uint64_t v_res_45_;
v_res_45_ = l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(v_x_3_);
stack->m_num = v_res_45_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___boxed(lean_object* v_x_46_){
_start:
{
uint64_t v_res_47_; lean_object* v_r_48_; 
v_res_47_ = l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(v_x_46_);
lean_dec_ref(v_x_46_);
v_r_48_ = lean_box_uint64(v_res_47_);
return v_r_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorIdx___impl(lean_object* v_x_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = lean_obj_tag_nat(v_x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorIdx___impl___boxed(lean_object* v_x_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorIdx___impl(v_x_53_);
lean_dec_ref(v_x_53_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(lean_object* v_t_55_, lean_object* v_k_56_){
_start:
{
switch(lean_obj_tag(v_t_55_))
{
case 0:
{
lean_object* v_a_57_; lean_object* v_zero_58_; lean_object* v___x_59_; 
v_a_57_ = lean_ctor_get(v_t_55_, 0);
lean_inc_ref(v_a_57_);
v_zero_58_ = lean_ctor_get(v_t_55_, 1);
lean_inc_ref(v_zero_58_);
lean_dec_ref_known(v_t_55_, 2);
v___x_59_ = lean_apply_2(v_k_56_, v_a_57_, v_zero_58_);
return v___x_59_;
}
case 1:
{
lean_object* v_a_60_; lean_object* v_b_61_; lean_object* v_p_u2081_62_; lean_object* v_p_u2082_63_; lean_object* v___x_64_; 
v_a_60_ = lean_ctor_get(v_t_55_, 0);
lean_inc_ref(v_a_60_);
v_b_61_ = lean_ctor_get(v_t_55_, 1);
lean_inc_ref(v_b_61_);
v_p_u2081_62_ = lean_ctor_get(v_t_55_, 2);
lean_inc_ref(v_p_u2081_62_);
v_p_u2082_63_ = lean_ctor_get(v_t_55_, 3);
lean_inc_ref(v_p_u2082_63_);
lean_dec_ref_known(v_t_55_, 4);
v___x_64_ = lean_apply_4(v_k_56_, v_a_60_, v_b_61_, v_p_u2081_62_, v_p_u2082_63_);
return v___x_64_;
}
case 2:
{
lean_object* v_a_65_; lean_object* v_b_66_; lean_object* v_toIntThm_67_; lean_object* v_lhs_68_; lean_object* v_rhs_69_; lean_object* v___x_70_; 
v_a_65_ = lean_ctor_get(v_t_55_, 0);
lean_inc_ref(v_a_65_);
v_b_66_ = lean_ctor_get(v_t_55_, 1);
lean_inc_ref(v_b_66_);
v_toIntThm_67_ = lean_ctor_get(v_t_55_, 2);
lean_inc_ref(v_toIntThm_67_);
v_lhs_68_ = lean_ctor_get(v_t_55_, 3);
lean_inc_ref(v_lhs_68_);
v_rhs_69_ = lean_ctor_get(v_t_55_, 4);
lean_inc_ref(v_rhs_69_);
lean_dec_ref_known(v_t_55_, 5);
v___x_70_ = lean_apply_5(v_k_56_, v_a_65_, v_b_66_, v_toIntThm_67_, v_lhs_68_, v_rhs_69_);
return v___x_70_;
}
case 3:
{
lean_object* v_e_71_; lean_object* v_e_x27_72_; lean_object* v___x_73_; 
v_e_71_ = lean_ctor_get(v_t_55_, 0);
lean_inc_ref(v_e_71_);
v_e_x27_72_ = lean_ctor_get(v_t_55_, 1);
lean_inc_ref(v_e_x27_72_);
lean_dec_ref_known(v_t_55_, 2);
v___x_73_ = lean_apply_2(v_k_56_, v_e_71_, v_e_x27_72_);
return v___x_73_;
}
case 4:
{
lean_object* v_h_74_; lean_object* v_x_75_; lean_object* v_e_x27_76_; lean_object* v___x_77_; 
v_h_74_ = lean_ctor_get(v_t_55_, 0);
lean_inc_ref(v_h_74_);
v_x_75_ = lean_ctor_get(v_t_55_, 1);
lean_inc(v_x_75_);
v_e_x27_76_ = lean_ctor_get(v_t_55_, 2);
lean_inc_ref(v_e_x27_76_);
lean_dec_ref_known(v_t_55_, 3);
v___x_77_ = lean_apply_3(v_k_56_, v_h_74_, v_x_75_, v_e_x27_76_);
return v___x_77_;
}
case 7:
{
lean_object* v_x_78_; lean_object* v_c_u2081_79_; lean_object* v_c_u2082_80_; lean_object* v___x_81_; 
v_x_78_ = lean_ctor_get(v_t_55_, 0);
lean_inc(v_x_78_);
v_c_u2081_79_ = lean_ctor_get(v_t_55_, 1);
lean_inc_ref(v_c_u2081_79_);
v_c_u2082_80_ = lean_ctor_get(v_t_55_, 2);
lean_inc_ref(v_c_u2082_80_);
lean_dec_ref_known(v_t_55_, 3);
v___x_81_ = lean_apply_3(v_k_56_, v_x_78_, v_c_u2081_79_, v_c_u2082_80_);
return v___x_81_;
}
case 8:
{
lean_object* v_c_u2081_82_; lean_object* v_c_u2082_83_; lean_object* v___x_84_; 
v_c_u2081_82_ = lean_ctor_get(v_t_55_, 0);
lean_inc_ref(v_c_u2081_82_);
v_c_u2082_83_ = lean_ctor_get(v_t_55_, 1);
lean_inc_ref(v_c_u2082_83_);
lean_dec_ref_known(v_t_55_, 2);
v___x_84_ = lean_apply_2(v_k_56_, v_c_u2081_82_, v_c_u2082_83_);
return v___x_84_;
}
case 11:
{
lean_object* v_c_85_; lean_object* v_e_86_; lean_object* v_p_87_; lean_object* v___x_88_; 
v_c_85_ = lean_ctor_get(v_t_55_, 0);
lean_inc_ref(v_c_85_);
v_e_86_ = lean_ctor_get(v_t_55_, 1);
lean_inc_ref(v_e_86_);
v_p_87_ = lean_ctor_get(v_t_55_, 2);
lean_inc_ref(v_p_87_);
lean_dec_ref_known(v_t_55_, 3);
v___x_88_ = lean_apply_3(v_k_56_, v_c_85_, v_e_86_, v_p_87_);
return v___x_88_;
}
case 12:
{
lean_object* v_e_89_; lean_object* v_e_x27_90_; lean_object* v_p_91_; lean_object* v_re_92_; lean_object* v_rp_93_; lean_object* v_p_x27_94_; lean_object* v___x_95_; 
v_e_89_ = lean_ctor_get(v_t_55_, 0);
lean_inc_ref(v_e_89_);
v_e_x27_90_ = lean_ctor_get(v_t_55_, 1);
lean_inc_ref(v_e_x27_90_);
v_p_91_ = lean_ctor_get(v_t_55_, 2);
lean_inc_ref(v_p_91_);
v_re_92_ = lean_ctor_get(v_t_55_, 3);
lean_inc_ref(v_re_92_);
v_rp_93_ = lean_ctor_get(v_t_55_, 4);
lean_inc_ref(v_rp_93_);
v_p_x27_94_ = lean_ctor_get(v_t_55_, 5);
lean_inc_ref(v_p_x27_94_);
lean_dec_ref_known(v_t_55_, 6);
v___x_95_ = lean_apply_6(v_k_56_, v_e_89_, v_e_x27_90_, v_p_91_, v_re_92_, v_rp_93_, v_p_x27_94_);
return v___x_95_;
}
case 13:
{
lean_object* v_h_96_; lean_object* v_x_97_; lean_object* v_e_x27_98_; lean_object* v_p_99_; lean_object* v_re_100_; lean_object* v_rp_101_; lean_object* v_p_x27_102_; lean_object* v___x_103_; 
v_h_96_ = lean_ctor_get(v_t_55_, 0);
lean_inc_ref(v_h_96_);
v_x_97_ = lean_ctor_get(v_t_55_, 1);
lean_inc(v_x_97_);
v_e_x27_98_ = lean_ctor_get(v_t_55_, 2);
lean_inc_ref(v_e_x27_98_);
v_p_99_ = lean_ctor_get(v_t_55_, 3);
lean_inc_ref(v_p_99_);
v_re_100_ = lean_ctor_get(v_t_55_, 4);
lean_inc_ref(v_re_100_);
v_rp_101_ = lean_ctor_get(v_t_55_, 5);
lean_inc_ref(v_rp_101_);
v_p_x27_102_ = lean_ctor_get(v_t_55_, 6);
lean_inc_ref(v_p_x27_102_);
lean_dec_ref_known(v_t_55_, 7);
v___x_103_ = lean_apply_7(v_k_56_, v_h_96_, v_x_97_, v_e_x27_98_, v_p_99_, v_re_100_, v_rp_101_, v_p_x27_102_);
return v___x_103_;
}
case 14:
{
lean_object* v_a_x3f_104_; lean_object* v_cs_105_; lean_object* v___x_106_; 
v_a_x3f_104_ = lean_ctor_get(v_t_55_, 0);
lean_inc(v_a_x3f_104_);
v_cs_105_ = lean_ctor_get(v_t_55_, 1);
lean_inc_ref(v_cs_105_);
lean_dec_ref_known(v_t_55_, 2);
v___x_106_ = lean_apply_2(v_k_56_, v_a_x3f_104_, v_cs_105_);
return v___x_106_;
}
case 15:
{
lean_object* v_k_107_; lean_object* v_y_x3f_108_; lean_object* v_c_109_; lean_object* v___x_110_; 
v_k_107_ = lean_ctor_get(v_t_55_, 0);
lean_inc(v_k_107_);
v_y_x3f_108_ = lean_ctor_get(v_t_55_, 1);
lean_inc(v_y_x3f_108_);
v_c_109_ = lean_ctor_get(v_t_55_, 2);
lean_inc_ref(v_c_109_);
lean_dec_ref_known(v_t_55_, 3);
v___x_110_ = lean_apply_3(v_k_56_, v_k_107_, v_y_x3f_108_, v_c_109_);
return v___x_110_;
}
case 16:
{
lean_object* v_k_111_; lean_object* v_y_x3f_112_; lean_object* v_c_113_; lean_object* v___x_114_; 
v_k_111_ = lean_ctor_get(v_t_55_, 0);
lean_inc(v_k_111_);
v_y_x3f_112_ = lean_ctor_get(v_t_55_, 1);
lean_inc(v_y_x3f_112_);
v_c_113_ = lean_ctor_get(v_t_55_, 2);
lean_inc_ref(v_c_113_);
lean_dec_ref_known(v_t_55_, 3);
v___x_114_ = lean_apply_3(v_k_56_, v_k_111_, v_y_x3f_112_, v_c_113_);
return v___x_114_;
}
case 17:
{
lean_object* v_ka_115_; lean_object* v_ca_x3f_116_; lean_object* v_kb_117_; lean_object* v_cb_x3f_118_; lean_object* v___x_119_; 
v_ka_115_ = lean_ctor_get(v_t_55_, 0);
lean_inc(v_ka_115_);
v_ca_x3f_116_ = lean_ctor_get(v_t_55_, 1);
lean_inc(v_ca_x3f_116_);
v_kb_117_ = lean_ctor_get(v_t_55_, 2);
lean_inc(v_kb_117_);
v_cb_x3f_118_ = lean_ctor_get(v_t_55_, 3);
lean_inc(v_cb_x3f_118_);
lean_dec_ref_known(v_t_55_, 4);
v___x_119_ = lean_apply_4(v_k_56_, v_ka_115_, v_ca_x3f_116_, v_kb_117_, v_cb_x3f_118_);
return v___x_119_;
}
default: 
{
lean_object* v_c_120_; lean_object* v___x_121_; 
v_c_120_ = lean_ctor_get(v_t_55_, 0);
lean_inc_ref(v_c_120_);
lean_dec_ref(v_t_55_);
v___x_121_ = lean_apply_1(v_k_56_, v_c_120_);
return v___x_121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim(lean_object* v_motive__2_122_, lean_object* v_ctorIdx_123_, lean_object* v_t_124_, lean_object* v_h_125_, lean_object* v_k_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_124_, v_k_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___boxed(lean_object* v_motive__2_128_, lean_object* v_ctorIdx_129_, lean_object* v_t_130_, lean_object* v_h_131_, lean_object* v_k_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim(v_motive__2_128_, v_ctorIdx_129_, v_t_130_, v_h_131_, v_k_132_);
lean_dec(v_ctorIdx_129_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core0_elim___redArg(lean_object* v_t_134_, lean_object* v_core0_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_134_, v_core0_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core0_elim(lean_object* v_motive__2_137_, lean_object* v_t_138_, lean_object* v_h_139_, lean_object* v_core0_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_138_, v_core0_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core_elim___redArg(lean_object* v_t_142_, lean_object* v_core_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_142_, v_core_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core_elim(lean_object* v_motive__2_145_, lean_object* v_t_146_, lean_object* v_h_147_, lean_object* v_core_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_146_, v_core_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_coreToInt_elim___redArg(lean_object* v_t_150_, lean_object* v_coreToInt_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_150_, v_coreToInt_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_coreToInt_elim(lean_object* v_motive__2_153_, lean_object* v_t_154_, lean_object* v_h_155_, lean_object* v_coreToInt_156_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_154_, v_coreToInt_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defn_elim___redArg(lean_object* v_t_158_, lean_object* v_defn_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_158_, v_defn_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defn_elim(lean_object* v_motive__2_161_, lean_object* v_t_162_, lean_object* v_h_163_, lean_object* v_defn_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_162_, v_defn_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnNat_elim___redArg(lean_object* v_t_166_, lean_object* v_defnNat_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_166_, v_defnNat_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnNat_elim(lean_object* v_motive__2_169_, lean_object* v_t_170_, lean_object* v_h_171_, lean_object* v_defnNat_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_170_, v_defnNat_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_norm_elim___redArg(lean_object* v_t_174_, lean_object* v_norm_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_174_, v_norm_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_norm_elim(lean_object* v_motive__2_177_, lean_object* v_t_178_, lean_object* v_h_179_, lean_object* v_norm_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_178_, v_norm_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_divCoeffs_elim___redArg(lean_object* v_t_182_, lean_object* v_divCoeffs_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_182_, v_divCoeffs_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_divCoeffs_elim(lean_object* v_motive__2_185_, lean_object* v_t_186_, lean_object* v_h_187_, lean_object* v_divCoeffs_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_186_, v_divCoeffs_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_subst_elim___redArg(lean_object* v_t_190_, lean_object* v_subst_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_190_, v_subst_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_subst_elim(lean_object* v_motive__2_193_, lean_object* v_t_194_, lean_object* v_h_195_, lean_object* v_subst_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_194_, v_subst_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofLeGe_elim___redArg(lean_object* v_t_198_, lean_object* v_ofLeGe_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_198_, v_ofLeGe_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofLeGe_elim(lean_object* v_motive__2_201_, lean_object* v_t_202_, lean_object* v_h_203_, lean_object* v_ofLeGe_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_202_, v_ofLeGe_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofZeroDvd_elim___redArg(lean_object* v_t_206_, lean_object* v_ofZeroDvd_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_206_, v_ofZeroDvd_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofZeroDvd_elim(lean_object* v_motive__2_209_, lean_object* v_t_210_, lean_object* v_h_211_, lean_object* v_ofZeroDvd_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_210_, v_ofZeroDvd_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_reorder_elim___redArg(lean_object* v_t_214_, lean_object* v_reorder_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_214_, v_reorder_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_reorder_elim(lean_object* v_motive__2_217_, lean_object* v_t_218_, lean_object* v_h_219_, lean_object* v_reorder_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_218_, v_reorder_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_commRingNorm_elim___redArg(lean_object* v_t_222_, lean_object* v_commRingNorm_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_222_, v_commRingNorm_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_commRingNorm_elim(lean_object* v_motive__2_225_, lean_object* v_t_226_, lean_object* v_h_227_, lean_object* v_commRingNorm_228_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_226_, v_commRingNorm_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnCommRing_elim___redArg(lean_object* v_t_230_, lean_object* v_defnCommRing_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_230_, v_defnCommRing_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnCommRing_elim(lean_object* v_motive__2_233_, lean_object* v_t_234_, lean_object* v_h_235_, lean_object* v_defnCommRing_236_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_234_, v_defnCommRing_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnNatCommRing_elim___redArg(lean_object* v_t_238_, lean_object* v_defnNatCommRing_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_238_, v_defnNatCommRing_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnNatCommRing_elim(lean_object* v_motive__2_241_, lean_object* v_t_242_, lean_object* v_h_243_, lean_object* v_defnNatCommRing_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_242_, v_defnNatCommRing_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mul_elim___redArg(lean_object* v_t_246_, lean_object* v_mul_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_246_, v_mul_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mul_elim(lean_object* v_motive__2_249_, lean_object* v_t_250_, lean_object* v_h_251_, lean_object* v_mul_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_250_, v_mul_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_div_elim___redArg(lean_object* v_t_254_, lean_object* v_div_255_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_254_, v_div_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_div_elim(lean_object* v_motive__2_257_, lean_object* v_t_258_, lean_object* v_h_259_, lean_object* v_div_260_){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_258_, v_div_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mod_elim___redArg(lean_object* v_t_262_, lean_object* v_mod_263_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_262_, v_mod_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mod_elim(lean_object* v_motive__2_265_, lean_object* v_t_266_, lean_object* v_h_267_, lean_object* v_mod_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_266_, v_mod_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_pow_elim___redArg(lean_object* v_t_270_, lean_object* v_pow_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_270_, v_pow_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_pow_elim(lean_object* v_motive__2_273_, lean_object* v_t_274_, lean_object* v_h_275_, lean_object* v_pow_276_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_274_, v_pow_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorIdx___impl(lean_object* v_x_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = lean_obj_tag_nat(v_x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorIdx___impl___boxed(lean_object* v_x_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorIdx___impl(v_x_280_);
lean_dec_ref(v_x_280_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(lean_object* v_t_282_, lean_object* v_k_283_){
_start:
{
if (lean_obj_tag(v_t_282_) == 0)
{
lean_object* v_h_284_; lean_object* v___x_285_; 
v_h_284_ = lean_ctor_get(v_t_282_, 0);
lean_inc(v_h_284_);
lean_dec_ref_known(v_t_282_, 1);
v___x_285_ = lean_apply_1(v_k_283_, v_h_284_);
return v___x_285_;
}
else
{
lean_object* v_hs_286_; lean_object* v_decVars_287_; lean_object* v___x_288_; 
v_hs_286_ = lean_ctor_get(v_t_282_, 0);
lean_inc_ref(v_hs_286_);
v_decVars_287_ = lean_ctor_get(v_t_282_, 1);
lean_inc_ref(v_decVars_287_);
lean_dec_ref_known(v_t_282_, 2);
v___x_288_ = lean_apply_2(v_k_283_, v_hs_286_, v_decVars_287_);
return v___x_288_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim(lean_object* v_motive__6_289_, lean_object* v_ctorIdx_290_, lean_object* v_t_291_, lean_object* v_h_292_, lean_object* v_k_293_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_291_, v_k_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___boxed(lean_object* v_motive__6_295_, lean_object* v_ctorIdx_296_, lean_object* v_t_297_, lean_object* v_h_298_, lean_object* v_k_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim(v_motive__6_295_, v_ctorIdx_296_, v_t_297_, v_h_298_, v_k_299_);
lean_dec(v_ctorIdx_296_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_dec_elim___redArg(lean_object* v_t_301_, lean_object* v_dec_302_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_301_, v_dec_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_dec_elim(lean_object* v_motive__6_304_, lean_object* v_t_305_, lean_object* v_h_306_, lean_object* v_dec_307_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_305_, v_dec_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_last_elim___redArg(lean_object* v_t_309_, lean_object* v_last_310_){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_309_, v_last_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_last_elim(lean_object* v_motive__6_312_, lean_object* v_t_313_, lean_object* v_h_314_, lean_object* v_last_315_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_313_, v_last_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorIdx___impl(lean_object* v_x_317_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = lean_obj_tag_nat(v_x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorIdx___impl___boxed(lean_object* v_x_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorIdx___impl(v_x_319_);
lean_dec_ref(v_x_319_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(lean_object* v_t_321_, lean_object* v_k_322_){
_start:
{
switch(lean_obj_tag(v_t_321_))
{
case 1:
{
lean_object* v_e_323_; lean_object* v_thm_324_; lean_object* v_d_325_; lean_object* v_a_326_; lean_object* v___x_327_; 
v_e_323_ = lean_ctor_get(v_t_321_, 0);
lean_inc_ref(v_e_323_);
v_thm_324_ = lean_ctor_get(v_t_321_, 1);
lean_inc_ref(v_thm_324_);
v_d_325_ = lean_ctor_get(v_t_321_, 2);
lean_inc(v_d_325_);
v_a_326_ = lean_ctor_get(v_t_321_, 3);
lean_inc_ref(v_a_326_);
lean_dec_ref_known(v_t_321_, 4);
v___x_327_ = lean_apply_4(v_k_322_, v_e_323_, v_thm_324_, v_d_325_, v_a_326_);
return v___x_327_;
}
case 4:
{
lean_object* v_c_u2081_328_; lean_object* v_c_u2082_329_; lean_object* v___x_330_; 
v_c_u2081_328_ = lean_ctor_get(v_t_321_, 0);
lean_inc_ref(v_c_u2081_328_);
v_c_u2082_329_ = lean_ctor_get(v_t_321_, 1);
lean_inc_ref(v_c_u2082_329_);
lean_dec_ref_known(v_t_321_, 2);
v___x_330_ = lean_apply_2(v_k_322_, v_c_u2081_328_, v_c_u2082_329_);
return v___x_330_;
}
case 5:
{
lean_object* v_c_u2081_331_; lean_object* v_c_u2082_332_; lean_object* v___x_333_; 
v_c_u2081_331_ = lean_ctor_get(v_t_321_, 0);
lean_inc_ref(v_c_u2081_331_);
v_c_u2082_332_ = lean_ctor_get(v_t_321_, 1);
lean_inc_ref(v_c_u2082_332_);
lean_dec_ref_known(v_t_321_, 2);
v___x_333_ = lean_apply_2(v_k_322_, v_c_u2081_331_, v_c_u2082_332_);
return v___x_333_;
}
case 7:
{
lean_object* v_x_334_; lean_object* v_c_335_; lean_object* v___x_336_; 
v_x_334_ = lean_ctor_get(v_t_321_, 0);
lean_inc(v_x_334_);
v_c_335_ = lean_ctor_get(v_t_321_, 1);
lean_inc_ref(v_c_335_);
lean_dec_ref_known(v_t_321_, 2);
v___x_336_ = lean_apply_2(v_k_322_, v_x_334_, v_c_335_);
return v___x_336_;
}
case 8:
{
lean_object* v_x_337_; lean_object* v_c_u2081_338_; lean_object* v_c_u2082_339_; lean_object* v___x_340_; 
v_x_337_ = lean_ctor_get(v_t_321_, 0);
lean_inc(v_x_337_);
v_c_u2081_338_ = lean_ctor_get(v_t_321_, 1);
lean_inc_ref(v_c_u2081_338_);
v_c_u2082_339_ = lean_ctor_get(v_t_321_, 2);
lean_inc_ref(v_c_u2082_339_);
lean_dec_ref_known(v_t_321_, 3);
v___x_340_ = lean_apply_3(v_k_322_, v_x_337_, v_c_u2081_338_, v_c_u2082_339_);
return v___x_340_;
}
case 12:
{
lean_object* v_c_341_; lean_object* v_e_342_; lean_object* v_p_343_; lean_object* v___x_344_; 
v_c_341_ = lean_ctor_get(v_t_321_, 0);
lean_inc_ref(v_c_341_);
v_e_342_ = lean_ctor_get(v_t_321_, 1);
lean_inc_ref(v_e_342_);
v_p_343_ = lean_ctor_get(v_t_321_, 2);
lean_inc_ref(v_p_343_);
lean_dec_ref_known(v_t_321_, 3);
v___x_344_ = lean_apply_3(v_k_322_, v_c_341_, v_e_342_, v_p_343_);
return v___x_344_;
}
default: 
{
lean_object* v_e_345_; lean_object* v___x_346_; 
v_e_345_ = lean_ctor_get(v_t_321_, 0);
lean_inc_ref(v_e_345_);
lean_dec_ref(v_t_321_);
v___x_346_ = lean_apply_1(v_k_322_, v_e_345_);
return v___x_346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim(lean_object* v_motive__7_347_, lean_object* v_ctorIdx_348_, lean_object* v_t_349_, lean_object* v_h_350_, lean_object* v_k_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_349_, v_k_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___boxed(lean_object* v_motive__7_353_, lean_object* v_ctorIdx_354_, lean_object* v_t_355_, lean_object* v_h_356_, lean_object* v_k_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim(v_motive__7_353_, v_ctorIdx_354_, v_t_355_, v_h_356_, v_k_357_);
lean_dec(v_ctorIdx_354_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_core_elim___redArg(lean_object* v_t_359_, lean_object* v_core_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_359_, v_core_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_core_elim(lean_object* v_motive__7_362_, lean_object* v_t_363_, lean_object* v_h_364_, lean_object* v_core_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_363_, v_core_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_coreOfNat_elim___redArg(lean_object* v_t_367_, lean_object* v_coreOfNat_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_367_, v_coreOfNat_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_coreOfNat_elim(lean_object* v_motive__7_370_, lean_object* v_t_371_, lean_object* v_h_372_, lean_object* v_coreOfNat_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_371_, v_coreOfNat_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_norm_elim___redArg(lean_object* v_t_375_, lean_object* v_norm_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_375_, v_norm_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_norm_elim(lean_object* v_motive__7_378_, lean_object* v_t_379_, lean_object* v_h_380_, lean_object* v_norm_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_379_, v_norm_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_divCoeffs_elim___redArg(lean_object* v_t_383_, lean_object* v_divCoeffs_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_383_, v_divCoeffs_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_divCoeffs_elim(lean_object* v_motive__7_386_, lean_object* v_t_387_, lean_object* v_h_388_, lean_object* v_divCoeffs_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_387_, v_divCoeffs_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveCombine_elim___redArg(lean_object* v_t_391_, lean_object* v_solveCombine_392_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_391_, v_solveCombine_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveCombine_elim(lean_object* v_motive__7_394_, lean_object* v_t_395_, lean_object* v_h_396_, lean_object* v_solveCombine_397_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_395_, v_solveCombine_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveElim_elim___redArg(lean_object* v_t_399_, lean_object* v_solveElim_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_399_, v_solveElim_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveElim_elim(lean_object* v_motive__7_402_, lean_object* v_t_403_, lean_object* v_h_404_, lean_object* v_solveElim_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_403_, v_solveElim_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_elim_elim___redArg(lean_object* v_t_407_, lean_object* v_elim_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_407_, v_elim_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_elim_elim(lean_object* v_motive__7_410_, lean_object* v_t_411_, lean_object* v_h_412_, lean_object* v_elim_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_411_, v_elim_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ofEq_elim___redArg(lean_object* v_t_415_, lean_object* v_ofEq_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_415_, v_ofEq_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ofEq_elim(lean_object* v_motive__7_418_, lean_object* v_t_419_, lean_object* v_h_420_, lean_object* v_ofEq_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_419_, v_ofEq_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_subst_elim___redArg(lean_object* v_t_423_, lean_object* v_subst_424_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_423_, v_subst_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_subst_elim(lean_object* v_motive__7_426_, lean_object* v_t_427_, lean_object* v_h_428_, lean_object* v_subst_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_427_, v_subst_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2081_elim___redArg(lean_object* v_t_431_, lean_object* v_cooper_u2081_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_431_, v_cooper_u2081_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2081_elim(lean_object* v_motive__7_434_, lean_object* v_t_435_, lean_object* v_h_436_, lean_object* v_cooper_u2081_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_435_, v_cooper_u2081_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2082_elim___redArg(lean_object* v_t_439_, lean_object* v_cooper_u2082_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_439_, v_cooper_u2082_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2082_elim(lean_object* v_motive__7_442_, lean_object* v_t_443_, lean_object* v_h_444_, lean_object* v_cooper_u2082_445_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_443_, v_cooper_u2082_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_reorder_elim___redArg(lean_object* v_t_447_, lean_object* v_reorder_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_447_, v_reorder_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_reorder_elim(lean_object* v_motive__7_450_, lean_object* v_t_451_, lean_object* v_h_452_, lean_object* v_reorder_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_451_, v_reorder_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_commRingNorm_elim___redArg(lean_object* v_t_455_, lean_object* v_commRingNorm_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_455_, v_commRingNorm_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_commRingNorm_elim(lean_object* v_motive__7_458_, lean_object* v_t_459_, lean_object* v_h_460_, lean_object* v_commRingNorm_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_459_, v_commRingNorm_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorIdx___impl(lean_object* v_x_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = lean_obj_tag_nat(v_x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorIdx___impl___boxed(lean_object* v_x_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorIdx___impl(v_x_465_);
lean_dec_ref(v_x_465_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(lean_object* v_t_467_, lean_object* v_k_468_){
_start:
{
switch(lean_obj_tag(v_t_467_))
{
case 1:
{
lean_object* v_e_469_; lean_object* v_p_470_; lean_object* v___x_471_; 
v_e_469_ = lean_ctor_get(v_t_467_, 0);
lean_inc_ref(v_e_469_);
v_p_470_ = lean_ctor_get(v_t_467_, 1);
lean_inc_ref(v_p_470_);
lean_dec_ref_known(v_t_467_, 2);
v___x_471_ = lean_apply_2(v_k_468_, v_e_469_, v_p_470_);
return v___x_471_;
}
case 2:
{
lean_object* v_e_472_; uint8_t v_pos_473_; lean_object* v_toIntThm_474_; lean_object* v_lhs_475_; lean_object* v_rhs_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v_e_472_ = lean_ctor_get(v_t_467_, 0);
lean_inc_ref(v_e_472_);
v_pos_473_ = lean_ctor_get_uint8(v_t_467_, sizeof(void*)*4);
v_toIntThm_474_ = lean_ctor_get(v_t_467_, 1);
lean_inc_ref(v_toIntThm_474_);
v_lhs_475_ = lean_ctor_get(v_t_467_, 2);
lean_inc_ref(v_lhs_475_);
v_rhs_476_ = lean_ctor_get(v_t_467_, 3);
lean_inc_ref(v_rhs_476_);
lean_dec_ref_known(v_t_467_, 4);
v___x_477_ = lean_box(v_pos_473_);
v___x_478_ = lean_apply_5(v_k_468_, v_e_472_, v___x_477_, v_toIntThm_474_, v_lhs_475_, v_rhs_476_);
return v___x_478_;
}
case 5:
{
lean_object* v_h_479_; lean_object* v___x_480_; 
v_h_479_ = lean_ctor_get(v_t_467_, 0);
lean_inc(v_h_479_);
lean_dec_ref_known(v_t_467_, 1);
v___x_480_ = lean_apply_1(v_k_468_, v_h_479_);
return v___x_480_;
}
case 8:
{
lean_object* v_c_u2081_481_; lean_object* v_c_u2082_482_; lean_object* v___x_483_; 
v_c_u2081_481_ = lean_ctor_get(v_t_467_, 0);
lean_inc_ref(v_c_u2081_481_);
v_c_u2082_482_ = lean_ctor_get(v_t_467_, 1);
lean_inc_ref(v_c_u2082_482_);
lean_dec_ref_known(v_t_467_, 2);
v___x_483_ = lean_apply_2(v_k_468_, v_c_u2081_481_, v_c_u2082_482_);
return v___x_483_;
}
case 9:
{
lean_object* v_c_u2081_484_; lean_object* v_c_u2082_485_; lean_object* v_k_486_; lean_object* v___x_487_; 
v_c_u2081_484_ = lean_ctor_get(v_t_467_, 0);
lean_inc_ref(v_c_u2081_484_);
v_c_u2082_485_ = lean_ctor_get(v_t_467_, 1);
lean_inc_ref(v_c_u2082_485_);
v_k_486_ = lean_ctor_get(v_t_467_, 2);
lean_inc(v_k_486_);
lean_dec_ref_known(v_t_467_, 3);
v___x_487_ = lean_apply_3(v_k_468_, v_c_u2081_484_, v_c_u2082_485_, v_k_486_);
return v___x_487_;
}
case 10:
{
lean_object* v_x_488_; lean_object* v_c_u2081_489_; lean_object* v_c_u2082_490_; lean_object* v___x_491_; 
v_x_488_ = lean_ctor_get(v_t_467_, 0);
lean_inc(v_x_488_);
v_c_u2081_489_ = lean_ctor_get(v_t_467_, 1);
lean_inc_ref(v_c_u2081_489_);
v_c_u2082_490_ = lean_ctor_get(v_t_467_, 2);
lean_inc_ref(v_c_u2082_490_);
lean_dec_ref_known(v_t_467_, 3);
v___x_491_ = lean_apply_3(v_k_468_, v_x_488_, v_c_u2081_489_, v_c_u2082_490_);
return v___x_491_;
}
case 11:
{
lean_object* v_c_u2081_492_; lean_object* v_c_u2082_493_; lean_object* v___x_494_; 
v_c_u2081_492_ = lean_ctor_get(v_t_467_, 0);
lean_inc_ref(v_c_u2081_492_);
v_c_u2082_493_ = lean_ctor_get(v_t_467_, 1);
lean_inc_ref(v_c_u2082_493_);
lean_dec_ref_known(v_t_467_, 2);
v___x_494_ = lean_apply_2(v_k_468_, v_c_u2081_492_, v_c_u2082_493_);
return v___x_494_;
}
case 12:
{
lean_object* v_c_u2081_495_; lean_object* v_decVar_496_; lean_object* v_h_497_; lean_object* v_decVars_498_; lean_object* v___x_499_; 
v_c_u2081_495_ = lean_ctor_get(v_t_467_, 0);
lean_inc_ref(v_c_u2081_495_);
v_decVar_496_ = lean_ctor_get(v_t_467_, 1);
lean_inc(v_decVar_496_);
v_h_497_ = lean_ctor_get(v_t_467_, 2);
lean_inc_ref(v_h_497_);
v_decVars_498_ = lean_ctor_get(v_t_467_, 3);
lean_inc_ref(v_decVars_498_);
lean_dec_ref_known(v_t_467_, 4);
v___x_499_ = lean_apply_4(v_k_468_, v_c_u2081_495_, v_decVar_496_, v_h_497_, v_decVars_498_);
return v___x_499_;
}
case 14:
{
lean_object* v_c_u2081_500_; lean_object* v_c_u2082_501_; lean_object* v___x_502_; 
v_c_u2081_500_ = lean_ctor_get(v_t_467_, 0);
lean_inc_ref(v_c_u2081_500_);
v_c_u2082_501_ = lean_ctor_get(v_t_467_, 1);
lean_inc_ref(v_c_u2082_501_);
lean_dec_ref_known(v_t_467_, 2);
v___x_502_ = lean_apply_2(v_k_468_, v_c_u2081_500_, v_c_u2082_501_);
return v___x_502_;
}
case 15:
{
lean_object* v_c_u2081_503_; lean_object* v_c_u2082_504_; lean_object* v___x_505_; 
v_c_u2081_503_ = lean_ctor_get(v_t_467_, 0);
lean_inc_ref(v_c_u2081_503_);
v_c_u2082_504_ = lean_ctor_get(v_t_467_, 1);
lean_inc_ref(v_c_u2082_504_);
lean_dec_ref_known(v_t_467_, 2);
v___x_505_ = lean_apply_2(v_k_468_, v_c_u2081_503_, v_c_u2082_504_);
return v___x_505_;
}
case 17:
{
lean_object* v_c_506_; lean_object* v_e_507_; lean_object* v_p_508_; lean_object* v___x_509_; 
v_c_506_ = lean_ctor_get(v_t_467_, 0);
lean_inc_ref(v_c_506_);
v_e_507_ = lean_ctor_get(v_t_467_, 1);
lean_inc_ref(v_e_507_);
v_p_508_ = lean_ctor_get(v_t_467_, 2);
lean_inc_ref(v_p_508_);
lean_dec_ref_known(v_t_467_, 3);
v___x_509_ = lean_apply_3(v_k_468_, v_c_506_, v_e_507_, v_p_508_);
return v___x_509_;
}
default: 
{
lean_object* v_e_510_; lean_object* v___x_511_; 
v_e_510_ = lean_ctor_get(v_t_467_, 0);
lean_inc_ref(v_e_510_);
lean_dec_ref(v_t_467_);
v___x_511_ = lean_apply_1(v_k_468_, v_e_510_);
return v___x_511_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim(lean_object* v_motive__9_512_, lean_object* v_ctorIdx_513_, lean_object* v_t_514_, lean_object* v_h_515_, lean_object* v_k_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_514_, v_k_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___boxed(lean_object* v_motive__9_518_, lean_object* v_ctorIdx_519_, lean_object* v_t_520_, lean_object* v_h_521_, lean_object* v_k_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim(v_motive__9_518_, v_ctorIdx_519_, v_t_520_, v_h_521_, v_k_522_);
lean_dec(v_ctorIdx_519_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_core_elim___redArg(lean_object* v_t_524_, lean_object* v_core_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_524_, v_core_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_core_elim(lean_object* v_motive__9_527_, lean_object* v_t_528_, lean_object* v_h_529_, lean_object* v_core_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_528_, v_core_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreNeg_elim___redArg(lean_object* v_t_532_, lean_object* v_coreNeg_533_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_532_, v_coreNeg_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreNeg_elim(lean_object* v_motive__9_535_, lean_object* v_t_536_, lean_object* v_h_537_, lean_object* v_coreNeg_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_536_, v_coreNeg_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreToInt_elim___redArg(lean_object* v_t_540_, lean_object* v_coreToInt_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_540_, v_coreToInt_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreToInt_elim(lean_object* v_motive__9_543_, lean_object* v_t_544_, lean_object* v_h_545_, lean_object* v_coreToInt_546_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_544_, v_coreToInt_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofNatNonneg_elim___redArg(lean_object* v_t_548_, lean_object* v_ofNatNonneg_549_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_548_, v_ofNatNonneg_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofNatNonneg_elim(lean_object* v_motive__9_551_, lean_object* v_t_552_, lean_object* v_h_553_, lean_object* v_ofNatNonneg_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_552_, v_ofNatNonneg_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_bound_elim___redArg(lean_object* v_t_556_, lean_object* v_bound_557_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_556_, v_bound_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_bound_elim(lean_object* v_motive__9_559_, lean_object* v_t_560_, lean_object* v_h_561_, lean_object* v_bound_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_560_, v_bound_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dec_elim___redArg(lean_object* v_t_564_, lean_object* v_dec_565_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_564_, v_dec_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dec_elim(lean_object* v_motive__9_567_, lean_object* v_t_568_, lean_object* v_h_569_, lean_object* v_dec_570_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_568_, v_dec_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_norm_elim___redArg(lean_object* v_t_572_, lean_object* v_norm_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_572_, v_norm_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_norm_elim(lean_object* v_motive__9_575_, lean_object* v_t_576_, lean_object* v_h_577_, lean_object* v_norm_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_576_, v_norm_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_divCoeffs_elim___redArg(lean_object* v_t_580_, lean_object* v_divCoeffs_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_580_, v_divCoeffs_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_divCoeffs_elim(lean_object* v_motive__9_583_, lean_object* v_t_584_, lean_object* v_h_585_, lean_object* v_divCoeffs_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_584_, v_divCoeffs_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combine_elim___redArg(lean_object* v_t_588_, lean_object* v_combine_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_588_, v_combine_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combine_elim(lean_object* v_motive__9_591_, lean_object* v_t_592_, lean_object* v_h_593_, lean_object* v_combine_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_592_, v_combine_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combineDivCoeffs_elim___redArg(lean_object* v_t_596_, lean_object* v_combineDivCoeffs_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_596_, v_combineDivCoeffs_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combineDivCoeffs_elim(lean_object* v_motive__9_599_, lean_object* v_t_600_, lean_object* v_h_601_, lean_object* v_combineDivCoeffs_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_600_, v_combineDivCoeffs_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_subst_elim___redArg(lean_object* v_t_604_, lean_object* v_subst_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_604_, v_subst_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_subst_elim(lean_object* v_motive__9_607_, lean_object* v_t_608_, lean_object* v_h_609_, lean_object* v_subst_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_608_, v_subst_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofLeDiseq_elim___redArg(lean_object* v_t_612_, lean_object* v_ofLeDiseq_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_612_, v_ofLeDiseq_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofLeDiseq_elim(lean_object* v_motive__9_615_, lean_object* v_t_616_, lean_object* v_h_617_, lean_object* v_ofLeDiseq_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_616_, v_ofLeDiseq_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofDiseqSplit_elim___redArg(lean_object* v_t_620_, lean_object* v_ofDiseqSplit_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_620_, v_ofDiseqSplit_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofDiseqSplit_elim(lean_object* v_motive__9_623_, lean_object* v_t_624_, lean_object* v_h_625_, lean_object* v_ofDiseqSplit_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_624_, v_ofDiseqSplit_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_cooper_elim___redArg(lean_object* v_t_628_, lean_object* v_cooper_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_628_, v_cooper_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_cooper_elim(lean_object* v_motive__9_631_, lean_object* v_t_632_, lean_object* v_h_633_, lean_object* v_cooper_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_632_, v_cooper_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dvdTight_elim___redArg(lean_object* v_t_636_, lean_object* v_dvdTight_637_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_636_, v_dvdTight_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dvdTight_elim(lean_object* v_motive__9_639_, lean_object* v_t_640_, lean_object* v_h_641_, lean_object* v_dvdTight_642_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_640_, v_dvdTight_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_negDvdTight_elim___redArg(lean_object* v_t_644_, lean_object* v_negDvdTight_645_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_644_, v_negDvdTight_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_negDvdTight_elim(lean_object* v_motive__9_647_, lean_object* v_t_648_, lean_object* v_h_649_, lean_object* v_negDvdTight_650_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_648_, v_negDvdTight_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_reorder_elim___redArg(lean_object* v_t_652_, lean_object* v_reorder_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_652_, v_reorder_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_reorder_elim(lean_object* v_motive__9_655_, lean_object* v_t_656_, lean_object* v_h_657_, lean_object* v_reorder_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_656_, v_reorder_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_commRingNorm_elim___redArg(lean_object* v_t_660_, lean_object* v_commRingNorm_661_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_660_, v_commRingNorm_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_commRingNorm_elim(lean_object* v_motive__9_663_, lean_object* v_t_664_, lean_object* v_h_665_, lean_object* v_commRingNorm_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_664_, v_commRingNorm_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorIdx___impl(lean_object* v_x_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = lean_obj_tag_nat(v_x_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorIdx___impl___boxed(lean_object* v_x_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorIdx___impl(v_x_670_);
lean_dec_ref(v_x_670_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(lean_object* v_t_672_, lean_object* v_k_673_){
_start:
{
switch(lean_obj_tag(v_t_672_))
{
case 0:
{
lean_object* v_a_674_; lean_object* v_zero_675_; lean_object* v___x_676_; 
v_a_674_ = lean_ctor_get(v_t_672_, 0);
lean_inc_ref(v_a_674_);
v_zero_675_ = lean_ctor_get(v_t_672_, 1);
lean_inc_ref(v_zero_675_);
lean_dec_ref_known(v_t_672_, 2);
v___x_676_ = lean_apply_2(v_k_673_, v_a_674_, v_zero_675_);
return v___x_676_;
}
case 1:
{
lean_object* v_a_677_; lean_object* v_b_678_; lean_object* v_p_u2081_679_; lean_object* v_p_u2082_680_; lean_object* v___x_681_; 
v_a_677_ = lean_ctor_get(v_t_672_, 0);
lean_inc_ref(v_a_677_);
v_b_678_ = lean_ctor_get(v_t_672_, 1);
lean_inc_ref(v_b_678_);
v_p_u2081_679_ = lean_ctor_get(v_t_672_, 2);
lean_inc_ref(v_p_u2081_679_);
v_p_u2082_680_ = lean_ctor_get(v_t_672_, 3);
lean_inc_ref(v_p_u2082_680_);
lean_dec_ref_known(v_t_672_, 4);
v___x_681_ = lean_apply_4(v_k_673_, v_a_677_, v_b_678_, v_p_u2081_679_, v_p_u2082_680_);
return v___x_681_;
}
case 2:
{
lean_object* v_a_682_; lean_object* v_b_683_; lean_object* v_toIntThm_684_; lean_object* v_lhs_685_; lean_object* v_rhs_686_; lean_object* v___x_687_; 
v_a_682_ = lean_ctor_get(v_t_672_, 0);
lean_inc_ref(v_a_682_);
v_b_683_ = lean_ctor_get(v_t_672_, 1);
lean_inc_ref(v_b_683_);
v_toIntThm_684_ = lean_ctor_get(v_t_672_, 2);
lean_inc_ref(v_toIntThm_684_);
v_lhs_685_ = lean_ctor_get(v_t_672_, 3);
lean_inc_ref(v_lhs_685_);
v_rhs_686_ = lean_ctor_get(v_t_672_, 4);
lean_inc_ref(v_rhs_686_);
lean_dec_ref_known(v_t_672_, 5);
v___x_687_ = lean_apply_5(v_k_673_, v_a_682_, v_b_683_, v_toIntThm_684_, v_lhs_685_, v_rhs_686_);
return v___x_687_;
}
case 6:
{
lean_object* v_x_688_; lean_object* v_c_u2081_689_; lean_object* v_c_u2082_690_; lean_object* v___x_691_; 
v_x_688_ = lean_ctor_get(v_t_672_, 0);
lean_inc(v_x_688_);
v_c_u2081_689_ = lean_ctor_get(v_t_672_, 1);
lean_inc_ref(v_c_u2081_689_);
v_c_u2082_690_ = lean_ctor_get(v_t_672_, 2);
lean_inc_ref(v_c_u2082_690_);
lean_dec_ref_known(v_t_672_, 3);
v___x_691_ = lean_apply_3(v_k_673_, v_x_688_, v_c_u2081_689_, v_c_u2082_690_);
return v___x_691_;
}
case 8:
{
lean_object* v_c_692_; lean_object* v_e_693_; lean_object* v_p_694_; lean_object* v___x_695_; 
v_c_692_ = lean_ctor_get(v_t_672_, 0);
lean_inc_ref(v_c_692_);
v_e_693_ = lean_ctor_get(v_t_672_, 1);
lean_inc_ref(v_e_693_);
v_p_694_ = lean_ctor_get(v_t_672_, 2);
lean_inc_ref(v_p_694_);
lean_dec_ref_known(v_t_672_, 3);
v___x_695_ = lean_apply_3(v_k_673_, v_c_692_, v_e_693_, v_p_694_);
return v___x_695_;
}
default: 
{
lean_object* v_c_696_; lean_object* v___x_697_; 
v_c_696_ = lean_ctor_get(v_t_672_, 0);
lean_inc_ref(v_c_696_);
lean_dec_ref(v_t_672_);
v___x_697_ = lean_apply_1(v_k_673_, v_c_696_);
return v___x_697_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim(lean_object* v_motive__11_698_, lean_object* v_ctorIdx_699_, lean_object* v_t_700_, lean_object* v_h_701_, lean_object* v_k_702_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_700_, v_k_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___boxed(lean_object* v_motive__11_704_, lean_object* v_ctorIdx_705_, lean_object* v_t_706_, lean_object* v_h_707_, lean_object* v_k_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim(v_motive__11_704_, v_ctorIdx_705_, v_t_706_, v_h_707_, v_k_708_);
lean_dec(v_ctorIdx_705_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core0_elim___redArg(lean_object* v_t_710_, lean_object* v_core0_711_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_710_, v_core0_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core0_elim(lean_object* v_motive__11_713_, lean_object* v_t_714_, lean_object* v_h_715_, lean_object* v_core0_716_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_714_, v_core0_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core_elim___redArg(lean_object* v_t_718_, lean_object* v_core_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_718_, v_core_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core_elim(lean_object* v_motive__11_721_, lean_object* v_t_722_, lean_object* v_h_723_, lean_object* v_core_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_722_, v_core_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_coreToInt_elim___redArg(lean_object* v_t_726_, lean_object* v_coreToInt_727_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_726_, v_coreToInt_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_coreToInt_elim(lean_object* v_motive__11_729_, lean_object* v_t_730_, lean_object* v_h_731_, lean_object* v_coreToInt_732_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_730_, v_coreToInt_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_norm_elim___redArg(lean_object* v_t_734_, lean_object* v_norm_735_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_734_, v_norm_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_norm_elim(lean_object* v_motive__11_737_, lean_object* v_t_738_, lean_object* v_h_739_, lean_object* v_norm_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_738_, v_norm_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_divCoeffs_elim___redArg(lean_object* v_t_742_, lean_object* v_divCoeffs_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_742_, v_divCoeffs_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_divCoeffs_elim(lean_object* v_motive__11_745_, lean_object* v_t_746_, lean_object* v_h_747_, lean_object* v_divCoeffs_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_746_, v_divCoeffs_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_neg_elim___redArg(lean_object* v_t_750_, lean_object* v_neg_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_750_, v_neg_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_neg_elim(lean_object* v_motive__11_753_, lean_object* v_t_754_, lean_object* v_h_755_, lean_object* v_neg_756_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_754_, v_neg_756_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_subst_elim___redArg(lean_object* v_t_758_, lean_object* v_subst_759_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_758_, v_subst_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_subst_elim(lean_object* v_motive__11_761_, lean_object* v_t_762_, lean_object* v_h_763_, lean_object* v_subst_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_762_, v_subst_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_reorder_elim___redArg(lean_object* v_t_766_, lean_object* v_reorder_767_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_766_, v_reorder_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_reorder_elim(lean_object* v_motive__11_769_, lean_object* v_t_770_, lean_object* v_h_771_, lean_object* v_reorder_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_770_, v_reorder_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_commRingNorm_elim___redArg(lean_object* v_t_774_, lean_object* v_commRingNorm_775_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_774_, v_commRingNorm_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_commRingNorm_elim(lean_object* v_motive__11_777_, lean_object* v_t_778_, lean_object* v_h_779_, lean_object* v_commRingNorm_780_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_778_, v_commRingNorm_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorIdx___impl(lean_object* v_x_782_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = lean_obj_tag_nat(v_x_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorIdx___impl___boxed(lean_object* v_x_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorIdx___impl(v_x_784_);
lean_dec_ref(v_x_784_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(lean_object* v_t_786_, lean_object* v_k_787_){
_start:
{
if (lean_obj_tag(v_t_786_) == 4)
{
lean_object* v_c_u2081_788_; lean_object* v_c_u2082_789_; lean_object* v_c_u2083_790_; lean_object* v___x_791_; 
v_c_u2081_788_ = lean_ctor_get(v_t_786_, 0);
lean_inc_ref(v_c_u2081_788_);
v_c_u2082_789_ = lean_ctor_get(v_t_786_, 1);
lean_inc_ref(v_c_u2082_789_);
v_c_u2083_790_ = lean_ctor_get(v_t_786_, 2);
lean_inc_ref(v_c_u2083_790_);
lean_dec_ref_known(v_t_786_, 3);
v___x_791_ = lean_apply_3(v_k_787_, v_c_u2081_788_, v_c_u2082_789_, v_c_u2083_790_);
return v___x_791_;
}
else
{
lean_object* v_c_792_; lean_object* v___x_793_; 
v_c_792_ = lean_ctor_get(v_t_786_, 0);
lean_inc_ref(v_c_792_);
lean_dec_ref(v_t_786_);
v___x_793_ = lean_apply_1(v_k_787_, v_c_792_);
return v___x_793_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim(lean_object* v_motive__12_794_, lean_object* v_ctorIdx_795_, lean_object* v_t_796_, lean_object* v_h_797_, lean_object* v_k_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_796_, v_k_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___boxed(lean_object* v_motive__12_800_, lean_object* v_ctorIdx_801_, lean_object* v_t_802_, lean_object* v_h_803_, lean_object* v_k_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim(v_motive__12_800_, v_ctorIdx_801_, v_t_802_, v_h_803_, v_k_804_);
lean_dec(v_ctorIdx_801_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_dvd_elim___redArg(lean_object* v_t_806_, lean_object* v_dvd_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_806_, v_dvd_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_dvd_elim(lean_object* v_motive__12_809_, lean_object* v_t_810_, lean_object* v_h_811_, lean_object* v_dvd_812_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_810_, v_dvd_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_le_elim___redArg(lean_object* v_t_814_, lean_object* v_le_815_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_814_, v_le_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_le_elim(lean_object* v_motive__12_817_, lean_object* v_t_818_, lean_object* v_h_819_, lean_object* v_le_820_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_818_, v_le_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_eq_elim___redArg(lean_object* v_t_822_, lean_object* v_eq_823_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_822_, v_eq_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_eq_elim(lean_object* v_motive__12_825_, lean_object* v_t_826_, lean_object* v_h_827_, lean_object* v_eq_828_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_826_, v_eq_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_diseq_elim___redArg(lean_object* v_t_830_, lean_object* v_diseq_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_830_, v_diseq_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_diseq_elim(lean_object* v_motive__12_833_, lean_object* v_t_834_, lean_object* v_h_835_, lean_object* v_diseq_836_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_834_, v_diseq_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_cooper_elim___redArg(lean_object* v_t_838_, lean_object* v_cooper_839_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_838_, v_cooper_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_cooper_elim(lean_object* v_motive__12_841_, lean_object* v_t_842_, lean_object* v_h_843_, lean_object* v_cooper_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_842_, v_cooper_844_);
return v___x_845_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0(void){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_846_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0);
v___x_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
return v___x_847_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3(void){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_851_ = lean_box(0);
v___x_852_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__2));
v___x_853_ = l_Lean_Expr_const___override(v___x_852_, v___x_851_);
return v___x_853_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3);
v___x_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_855_, 0, v___x_854_);
return v___x_855_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5(void){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_856_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4);
v___x_857_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0);
v___x_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
lean_ctor_set(v___x_858_, 1, v___x_856_);
return v___x_858_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr(void){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5);
return v___x_859_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0(void){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_860_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3);
v___x_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_861_, 0, v___x_860_);
return v___x_861_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1(void){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_862_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0);
v___x_863_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0);
v___x_864_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0);
v___x_865_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
lean_ctor_set(v___x_865_, 1, v___x_863_);
lean_ctor_set(v___x_865_, 2, v___x_862_);
return v___x_865_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr(void){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1);
return v___x_866_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0(void){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; uint8_t v___x_869_; lean_object* v___x_870_; 
v___x_867_ = lean_box(0);
v___x_868_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5);
v___x_869_ = 0;
v___x_870_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_870_, 0, v___x_868_);
lean_ctor_set(v___x_870_, 1, v___x_868_);
lean_ctor_set(v___x_870_, 2, v___x_867_);
lean_ctor_set_uint8(v___x_870_, sizeof(void*)*3, v___x_869_);
return v___x_870_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred(void){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0);
return v___x_871_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1(void){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_874_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__0));
v___x_875_ = lean_unsigned_to_nat(0u);
v___x_876_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0);
v___x_877_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_877_, 0, v___x_876_);
lean_ctor_set(v___x_877_, 1, v___x_875_);
lean_ctor_set(v___x_877_, 2, v___x_874_);
return v___x_877_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit(void){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1);
return v___x_878_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_879_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0);
v___x_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
return v___x_881_;
}
}
lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg(){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__1);
return v___x_883_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_884_;
v_res_884_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg();
stack->m_obj
 = v_res_884_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___boxed(lean_object* v___dummy_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg();
return v_res_886_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg();
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0(lean_object* v_00_u03b2_888_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0);
return v___x_889_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0(void){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_890_ = lean_unsigned_to_nat(32u);
v___x_891_ = lean_mk_empty_array_with_capacity(v___x_890_);
v___x_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
return v___x_892_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1(void){
_start:
{
size_t v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_893_ = ((size_t)5ULL);
v___x_894_ = lean_unsigned_to_nat(0u);
v___x_895_ = lean_unsigned_to_nat(32u);
v___x_896_ = lean_mk_empty_array_with_capacity(v___x_895_);
v___x_897_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0);
v___x_898_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_898_, 0, v___x_897_);
lean_ctor_set(v___x_898_, 1, v___x_896_);
lean_ctor_set(v___x_898_, 2, v___x_894_);
lean_ctor_set(v___x_898_, 3, v___x_894_);
lean_ctor_set_usize(v___x_898_, 4, v___x_893_);
return v___x_898_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0);
v___x_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
return v___x_900_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; uint8_t v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_901_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0);
v___x_902_ = lean_box(0);
v___x_903_ = 0;
v___x_904_ = lean_unsigned_to_nat(0u);
v___x_905_ = lean_box(0);
v___x_906_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2);
v___x_907_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1);
v___x_908_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v___x_908_, 0, v___x_907_);
lean_ctor_set(v___x_908_, 1, v___x_906_);
lean_ctor_set(v___x_908_, 2, v___x_907_);
lean_ctor_set(v___x_908_, 3, v___x_906_);
lean_ctor_set(v___x_908_, 4, v___x_906_);
lean_ctor_set(v___x_908_, 5, v___x_907_);
lean_ctor_set(v___x_908_, 6, v___x_907_);
lean_ctor_set(v___x_908_, 7, v___x_907_);
lean_ctor_set(v___x_908_, 8, v___x_907_);
lean_ctor_set(v___x_908_, 9, v___x_907_);
lean_ctor_set(v___x_908_, 10, v___x_905_);
lean_ctor_set(v___x_908_, 11, v___x_907_);
lean_ctor_set(v___x_908_, 12, v___x_907_);
lean_ctor_set(v___x_908_, 13, v___x_904_);
lean_ctor_set(v___x_908_, 14, v___x_904_);
lean_ctor_set(v___x_908_, 15, v___x_902_);
lean_ctor_set(v___x_908_, 16, v___x_906_);
lean_ctor_set(v___x_908_, 17, v___x_901_);
lean_ctor_set(v___x_908_, 18, v___x_906_);
lean_ctor_set_uint8(v___x_908_, sizeof(void*)*19, v___x_903_);
lean_ctor_set_uint8(v___x_908_, sizeof(void*)*19 + 1, v___x_903_);
return v___x_908_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default(void){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3);
return v___x_909_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState(void){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default;
return v___x_910_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(lean_object* v___x_911_){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_913_, 0, v___x_911_);
return v___x_913_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_911_ = stack[0].m_obj;
lean_object* v_res_914_;
v_res_914_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(v___x_911_);
stack->m_obj
 = v_res_914_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2____boxed(lean_object* v___x_915_, lean_object* v___y_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(v___x_915_);
return v_res_917_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_918_; lean_object* v___f_919_; 
v___x_918_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3);
v___f_919_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_919_, 0, v___x_918_);
return v___f_919_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_921_; lean_object* v___x_922_; 
v___f_921_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_);
v___x_922_ = l_Lean_Meta_Grind_registerSolverExtension___redArg(v___f_921_);
return v___x_922_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_923_;
v_res_923_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_();
stack->m_obj
 = v_res_923_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2____boxed(lean_object* v_a_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_();
return v_res_925_;
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
