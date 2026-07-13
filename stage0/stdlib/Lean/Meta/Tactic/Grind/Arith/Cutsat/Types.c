// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.Types
// Imports: public import Init.Data.Int.Linear public import Lean.Meta.Tactic.Grind.Arith.CommRing.Types public import Lean.Meta.Tactic.Grind.Arith.Cutsat.ToIntInfo
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_dec_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_dec_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_last_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_last_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorIdx___boxed(lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__4;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorIdx(lean_object* v_x_50_){
_start:
{
switch(lean_obj_tag(v_x_50_))
{
case 0:
{
lean_object* v___x_51_; 
v___x_51_ = lean_unsigned_to_nat(0u);
return v___x_51_;
}
case 1:
{
lean_object* v___x_52_; 
v___x_52_ = lean_unsigned_to_nat(1u);
return v___x_52_;
}
case 2:
{
lean_object* v___x_53_; 
v___x_53_ = lean_unsigned_to_nat(2u);
return v___x_53_;
}
case 3:
{
lean_object* v___x_54_; 
v___x_54_ = lean_unsigned_to_nat(3u);
return v___x_54_;
}
case 4:
{
lean_object* v___x_55_; 
v___x_55_ = lean_unsigned_to_nat(4u);
return v___x_55_;
}
case 5:
{
lean_object* v___x_56_; 
v___x_56_ = lean_unsigned_to_nat(5u);
return v___x_56_;
}
case 6:
{
lean_object* v___x_57_; 
v___x_57_ = lean_unsigned_to_nat(6u);
return v___x_57_;
}
case 7:
{
lean_object* v___x_58_; 
v___x_58_ = lean_unsigned_to_nat(7u);
return v___x_58_;
}
case 8:
{
lean_object* v___x_59_; 
v___x_59_ = lean_unsigned_to_nat(8u);
return v___x_59_;
}
case 9:
{
lean_object* v___x_60_; 
v___x_60_ = lean_unsigned_to_nat(9u);
return v___x_60_;
}
case 10:
{
lean_object* v___x_61_; 
v___x_61_ = lean_unsigned_to_nat(10u);
return v___x_61_;
}
case 11:
{
lean_object* v___x_62_; 
v___x_62_ = lean_unsigned_to_nat(11u);
return v___x_62_;
}
case 12:
{
lean_object* v___x_63_; 
v___x_63_ = lean_unsigned_to_nat(12u);
return v___x_63_;
}
case 13:
{
lean_object* v___x_64_; 
v___x_64_ = lean_unsigned_to_nat(13u);
return v___x_64_;
}
case 14:
{
lean_object* v___x_65_; 
v___x_65_ = lean_unsigned_to_nat(14u);
return v___x_65_;
}
case 15:
{
lean_object* v___x_66_; 
v___x_66_ = lean_unsigned_to_nat(15u);
return v___x_66_;
}
case 16:
{
lean_object* v___x_67_; 
v___x_67_ = lean_unsigned_to_nat(16u);
return v___x_67_;
}
default: 
{
lean_object* v___x_68_; 
v___x_68_ = lean_unsigned_to_nat(17u);
return v___x_68_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorIdx___boxed(lean_object* v_x_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorIdx(v_x_69_);
lean_dec_ref(v_x_69_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(lean_object* v_t_71_, lean_object* v_k_72_){
_start:
{
switch(lean_obj_tag(v_t_71_))
{
case 0:
{
lean_object* v_a_73_; lean_object* v_zero_74_; lean_object* v___x_75_; 
v_a_73_ = lean_ctor_get(v_t_71_, 0);
lean_inc_ref(v_a_73_);
v_zero_74_ = lean_ctor_get(v_t_71_, 1);
lean_inc_ref(v_zero_74_);
lean_dec_ref_known(v_t_71_, 2);
v___x_75_ = lean_apply_2(v_k_72_, v_a_73_, v_zero_74_);
return v___x_75_;
}
case 1:
{
lean_object* v_a_76_; lean_object* v_b_77_; lean_object* v_p_u2081_78_; lean_object* v_p_u2082_79_; lean_object* v___x_80_; 
v_a_76_ = lean_ctor_get(v_t_71_, 0);
lean_inc_ref(v_a_76_);
v_b_77_ = lean_ctor_get(v_t_71_, 1);
lean_inc_ref(v_b_77_);
v_p_u2081_78_ = lean_ctor_get(v_t_71_, 2);
lean_inc_ref(v_p_u2081_78_);
v_p_u2082_79_ = lean_ctor_get(v_t_71_, 3);
lean_inc_ref(v_p_u2082_79_);
lean_dec_ref_known(v_t_71_, 4);
v___x_80_ = lean_apply_4(v_k_72_, v_a_76_, v_b_77_, v_p_u2081_78_, v_p_u2082_79_);
return v___x_80_;
}
case 2:
{
lean_object* v_a_81_; lean_object* v_b_82_; lean_object* v_toIntThm_83_; lean_object* v_lhs_84_; lean_object* v_rhs_85_; lean_object* v___x_86_; 
v_a_81_ = lean_ctor_get(v_t_71_, 0);
lean_inc_ref(v_a_81_);
v_b_82_ = lean_ctor_get(v_t_71_, 1);
lean_inc_ref(v_b_82_);
v_toIntThm_83_ = lean_ctor_get(v_t_71_, 2);
lean_inc_ref(v_toIntThm_83_);
v_lhs_84_ = lean_ctor_get(v_t_71_, 3);
lean_inc_ref(v_lhs_84_);
v_rhs_85_ = lean_ctor_get(v_t_71_, 4);
lean_inc_ref(v_rhs_85_);
lean_dec_ref_known(v_t_71_, 5);
v___x_86_ = lean_apply_5(v_k_72_, v_a_81_, v_b_82_, v_toIntThm_83_, v_lhs_84_, v_rhs_85_);
return v___x_86_;
}
case 3:
{
lean_object* v_e_87_; lean_object* v_p_88_; lean_object* v___x_89_; 
v_e_87_ = lean_ctor_get(v_t_71_, 0);
lean_inc_ref(v_e_87_);
v_p_88_ = lean_ctor_get(v_t_71_, 1);
lean_inc_ref(v_p_88_);
lean_dec_ref_known(v_t_71_, 2);
v___x_89_ = lean_apply_2(v_k_72_, v_e_87_, v_p_88_);
return v___x_89_;
}
case 4:
{
lean_object* v_h_90_; lean_object* v_x_91_; lean_object* v_e_x27_92_; lean_object* v___x_93_; 
v_h_90_ = lean_ctor_get(v_t_71_, 0);
lean_inc_ref(v_h_90_);
v_x_91_ = lean_ctor_get(v_t_71_, 1);
lean_inc(v_x_91_);
v_e_x27_92_ = lean_ctor_get(v_t_71_, 2);
lean_inc_ref(v_e_x27_92_);
lean_dec_ref_known(v_t_71_, 3);
v___x_93_ = lean_apply_3(v_k_72_, v_h_90_, v_x_91_, v_e_x27_92_);
return v___x_93_;
}
case 7:
{
lean_object* v_x_94_; lean_object* v_c_u2081_95_; lean_object* v_c_u2082_96_; lean_object* v___x_97_; 
v_x_94_ = lean_ctor_get(v_t_71_, 0);
lean_inc(v_x_94_);
v_c_u2081_95_ = lean_ctor_get(v_t_71_, 1);
lean_inc_ref(v_c_u2081_95_);
v_c_u2082_96_ = lean_ctor_get(v_t_71_, 2);
lean_inc_ref(v_c_u2082_96_);
lean_dec_ref_known(v_t_71_, 3);
v___x_97_ = lean_apply_3(v_k_72_, v_x_94_, v_c_u2081_95_, v_c_u2082_96_);
return v___x_97_;
}
case 8:
{
lean_object* v_c_u2081_98_; lean_object* v_c_u2082_99_; lean_object* v___x_100_; 
v_c_u2081_98_ = lean_ctor_get(v_t_71_, 0);
lean_inc_ref(v_c_u2081_98_);
v_c_u2082_99_ = lean_ctor_get(v_t_71_, 1);
lean_inc_ref(v_c_u2082_99_);
lean_dec_ref_known(v_t_71_, 2);
v___x_100_ = lean_apply_2(v_k_72_, v_c_u2081_98_, v_c_u2082_99_);
return v___x_100_;
}
case 11:
{
lean_object* v_c_101_; lean_object* v_e_102_; lean_object* v_p_103_; lean_object* v___x_104_; 
v_c_101_ = lean_ctor_get(v_t_71_, 0);
lean_inc_ref(v_c_101_);
v_e_102_ = lean_ctor_get(v_t_71_, 1);
lean_inc_ref(v_e_102_);
v_p_103_ = lean_ctor_get(v_t_71_, 2);
lean_inc_ref(v_p_103_);
lean_dec_ref_known(v_t_71_, 3);
v___x_104_ = lean_apply_3(v_k_72_, v_c_101_, v_e_102_, v_p_103_);
return v___x_104_;
}
case 12:
{
lean_object* v_e_105_; lean_object* v_p_106_; lean_object* v_re_107_; lean_object* v_rp_108_; lean_object* v_p_x27_109_; lean_object* v___x_110_; 
v_e_105_ = lean_ctor_get(v_t_71_, 0);
lean_inc_ref(v_e_105_);
v_p_106_ = lean_ctor_get(v_t_71_, 1);
lean_inc_ref(v_p_106_);
v_re_107_ = lean_ctor_get(v_t_71_, 2);
lean_inc_ref(v_re_107_);
v_rp_108_ = lean_ctor_get(v_t_71_, 3);
lean_inc_ref(v_rp_108_);
v_p_x27_109_ = lean_ctor_get(v_t_71_, 4);
lean_inc_ref(v_p_x27_109_);
lean_dec_ref_known(v_t_71_, 5);
v___x_110_ = lean_apply_5(v_k_72_, v_e_105_, v_p_106_, v_re_107_, v_rp_108_, v_p_x27_109_);
return v___x_110_;
}
case 13:
{
lean_object* v_h_111_; lean_object* v_x_112_; lean_object* v_e_x27_113_; lean_object* v_p_114_; lean_object* v_re_115_; lean_object* v_rp_116_; lean_object* v_p_x27_117_; lean_object* v___x_118_; 
v_h_111_ = lean_ctor_get(v_t_71_, 0);
lean_inc_ref(v_h_111_);
v_x_112_ = lean_ctor_get(v_t_71_, 1);
lean_inc(v_x_112_);
v_e_x27_113_ = lean_ctor_get(v_t_71_, 2);
lean_inc_ref(v_e_x27_113_);
v_p_114_ = lean_ctor_get(v_t_71_, 3);
lean_inc_ref(v_p_114_);
v_re_115_ = lean_ctor_get(v_t_71_, 4);
lean_inc_ref(v_re_115_);
v_rp_116_ = lean_ctor_get(v_t_71_, 5);
lean_inc_ref(v_rp_116_);
v_p_x27_117_ = lean_ctor_get(v_t_71_, 6);
lean_inc_ref(v_p_x27_117_);
lean_dec_ref_known(v_t_71_, 7);
v___x_118_ = lean_apply_7(v_k_72_, v_h_111_, v_x_112_, v_e_x27_113_, v_p_114_, v_re_115_, v_rp_116_, v_p_x27_117_);
return v___x_118_;
}
case 14:
{
lean_object* v_a_x3f_119_; lean_object* v_cs_120_; lean_object* v___x_121_; 
v_a_x3f_119_ = lean_ctor_get(v_t_71_, 0);
lean_inc(v_a_x3f_119_);
v_cs_120_ = lean_ctor_get(v_t_71_, 1);
lean_inc_ref(v_cs_120_);
lean_dec_ref_known(v_t_71_, 2);
v___x_121_ = lean_apply_2(v_k_72_, v_a_x3f_119_, v_cs_120_);
return v___x_121_;
}
case 15:
{
lean_object* v_k_122_; lean_object* v_y_x3f_123_; lean_object* v_c_124_; lean_object* v___x_125_; 
v_k_122_ = lean_ctor_get(v_t_71_, 0);
lean_inc(v_k_122_);
v_y_x3f_123_ = lean_ctor_get(v_t_71_, 1);
lean_inc(v_y_x3f_123_);
v_c_124_ = lean_ctor_get(v_t_71_, 2);
lean_inc_ref(v_c_124_);
lean_dec_ref_known(v_t_71_, 3);
v___x_125_ = lean_apply_3(v_k_72_, v_k_122_, v_y_x3f_123_, v_c_124_);
return v___x_125_;
}
case 16:
{
lean_object* v_k_126_; lean_object* v_y_x3f_127_; lean_object* v_c_128_; lean_object* v___x_129_; 
v_k_126_ = lean_ctor_get(v_t_71_, 0);
lean_inc(v_k_126_);
v_y_x3f_127_ = lean_ctor_get(v_t_71_, 1);
lean_inc(v_y_x3f_127_);
v_c_128_ = lean_ctor_get(v_t_71_, 2);
lean_inc_ref(v_c_128_);
lean_dec_ref_known(v_t_71_, 3);
v___x_129_ = lean_apply_3(v_k_72_, v_k_126_, v_y_x3f_127_, v_c_128_);
return v___x_129_;
}
case 17:
{
lean_object* v_ka_130_; lean_object* v_ca_x3f_131_; lean_object* v_kb_132_; lean_object* v_cb_x3f_133_; lean_object* v___x_134_; 
v_ka_130_ = lean_ctor_get(v_t_71_, 0);
lean_inc(v_ka_130_);
v_ca_x3f_131_ = lean_ctor_get(v_t_71_, 1);
lean_inc(v_ca_x3f_131_);
v_kb_132_ = lean_ctor_get(v_t_71_, 2);
lean_inc(v_kb_132_);
v_cb_x3f_133_ = lean_ctor_get(v_t_71_, 3);
lean_inc(v_cb_x3f_133_);
lean_dec_ref_known(v_t_71_, 4);
v___x_134_ = lean_apply_4(v_k_72_, v_ka_130_, v_ca_x3f_131_, v_kb_132_, v_cb_x3f_133_);
return v___x_134_;
}
default: 
{
lean_object* v_c_135_; lean_object* v___x_136_; 
v_c_135_ = lean_ctor_get(v_t_71_, 0);
lean_inc_ref(v_c_135_);
lean_dec_ref(v_t_71_);
v___x_136_ = lean_apply_1(v_k_72_, v_c_135_);
return v___x_136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim(lean_object* v_motive__2_137_, lean_object* v_ctorIdx_138_, lean_object* v_t_139_, lean_object* v_h_140_, lean_object* v_k_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_139_, v_k_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___boxed(lean_object* v_motive__2_143_, lean_object* v_ctorIdx_144_, lean_object* v_t_145_, lean_object* v_h_146_, lean_object* v_k_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim(v_motive__2_143_, v_ctorIdx_144_, v_t_145_, v_h_146_, v_k_147_);
lean_dec(v_ctorIdx_144_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core0_elim___redArg(lean_object* v_t_149_, lean_object* v_core0_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_149_, v_core0_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core0_elim(lean_object* v_motive__2_152_, lean_object* v_t_153_, lean_object* v_h_154_, lean_object* v_core0_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_153_, v_core0_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core_elim___redArg(lean_object* v_t_157_, lean_object* v_core_158_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_157_, v_core_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core_elim(lean_object* v_motive__2_160_, lean_object* v_t_161_, lean_object* v_h_162_, lean_object* v_core_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_161_, v_core_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_coreToInt_elim___redArg(lean_object* v_t_165_, lean_object* v_coreToInt_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_165_, v_coreToInt_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_coreToInt_elim(lean_object* v_motive__2_168_, lean_object* v_t_169_, lean_object* v_h_170_, lean_object* v_coreToInt_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_169_, v_coreToInt_171_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnNat_elim___redArg(lean_object* v_t_181_, lean_object* v_defnNat_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_181_, v_defnNat_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnNat_elim(lean_object* v_motive__2_184_, lean_object* v_t_185_, lean_object* v_h_186_, lean_object* v_defnNat_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_185_, v_defnNat_187_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_reorder_elim___redArg(lean_object* v_t_229_, lean_object* v_reorder_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_229_, v_reorder_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_reorder_elim(lean_object* v_motive__2_232_, lean_object* v_t_233_, lean_object* v_h_234_, lean_object* v_reorder_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_233_, v_reorder_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_commRingNorm_elim___redArg(lean_object* v_t_237_, lean_object* v_commRingNorm_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_237_, v_commRingNorm_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_commRingNorm_elim(lean_object* v_motive__2_240_, lean_object* v_t_241_, lean_object* v_h_242_, lean_object* v_commRingNorm_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_241_, v_commRingNorm_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnCommRing_elim___redArg(lean_object* v_t_245_, lean_object* v_defnCommRing_246_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_245_, v_defnCommRing_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnCommRing_elim(lean_object* v_motive__2_248_, lean_object* v_t_249_, lean_object* v_h_250_, lean_object* v_defnCommRing_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_249_, v_defnCommRing_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnNatCommRing_elim___redArg(lean_object* v_t_253_, lean_object* v_defnNatCommRing_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_253_, v_defnNatCommRing_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnNatCommRing_elim(lean_object* v_motive__2_256_, lean_object* v_t_257_, lean_object* v_h_258_, lean_object* v_defnNatCommRing_259_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_257_, v_defnNatCommRing_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mul_elim___redArg(lean_object* v_t_261_, lean_object* v_mul_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_261_, v_mul_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mul_elim(lean_object* v_motive__2_264_, lean_object* v_t_265_, lean_object* v_h_266_, lean_object* v_mul_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_265_, v_mul_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_div_elim___redArg(lean_object* v_t_269_, lean_object* v_div_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_269_, v_div_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_div_elim(lean_object* v_motive__2_272_, lean_object* v_t_273_, lean_object* v_h_274_, lean_object* v_div_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_273_, v_div_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mod_elim___redArg(lean_object* v_t_277_, lean_object* v_mod_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_277_, v_mod_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mod_elim(lean_object* v_motive__2_280_, lean_object* v_t_281_, lean_object* v_h_282_, lean_object* v_mod_283_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_281_, v_mod_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_pow_elim___redArg(lean_object* v_t_285_, lean_object* v_pow_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_285_, v_pow_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_pow_elim(lean_object* v_motive__2_288_, lean_object* v_t_289_, lean_object* v_h_290_, lean_object* v_pow_291_){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_289_, v_pow_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorIdx(lean_object* v_x_293_){
_start:
{
if (lean_obj_tag(v_x_293_) == 0)
{
lean_object* v___x_294_; 
v___x_294_ = lean_unsigned_to_nat(0u);
return v___x_294_;
}
else
{
lean_object* v___x_295_; 
v___x_295_ = lean_unsigned_to_nat(1u);
return v___x_295_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorIdx___boxed(lean_object* v_x_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorIdx(v_x_296_);
lean_dec_ref(v_x_296_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(lean_object* v_t_298_, lean_object* v_k_299_){
_start:
{
if (lean_obj_tag(v_t_298_) == 0)
{
lean_object* v_h_300_; lean_object* v___x_301_; 
v_h_300_ = lean_ctor_get(v_t_298_, 0);
lean_inc(v_h_300_);
lean_dec_ref_known(v_t_298_, 1);
v___x_301_ = lean_apply_1(v_k_299_, v_h_300_);
return v___x_301_;
}
else
{
lean_object* v_hs_302_; lean_object* v_decVars_303_; lean_object* v___x_304_; 
v_hs_302_ = lean_ctor_get(v_t_298_, 0);
lean_inc_ref(v_hs_302_);
v_decVars_303_ = lean_ctor_get(v_t_298_, 1);
lean_inc_ref(v_decVars_303_);
lean_dec_ref_known(v_t_298_, 2);
v___x_304_ = lean_apply_2(v_k_299_, v_hs_302_, v_decVars_303_);
return v___x_304_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim(lean_object* v_motive__6_305_, lean_object* v_ctorIdx_306_, lean_object* v_t_307_, lean_object* v_h_308_, lean_object* v_k_309_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_307_, v_k_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___boxed(lean_object* v_motive__6_311_, lean_object* v_ctorIdx_312_, lean_object* v_t_313_, lean_object* v_h_314_, lean_object* v_k_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim(v_motive__6_311_, v_ctorIdx_312_, v_t_313_, v_h_314_, v_k_315_);
lean_dec(v_ctorIdx_312_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_dec_elim___redArg(lean_object* v_t_317_, lean_object* v_dec_318_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_317_, v_dec_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_dec_elim(lean_object* v_motive__6_320_, lean_object* v_t_321_, lean_object* v_h_322_, lean_object* v_dec_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_321_, v_dec_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_last_elim___redArg(lean_object* v_t_325_, lean_object* v_last_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_325_, v_last_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_last_elim(lean_object* v_motive__6_328_, lean_object* v_t_329_, lean_object* v_h_330_, lean_object* v_last_331_){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_329_, v_last_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorIdx(lean_object* v_x_333_){
_start:
{
switch(lean_obj_tag(v_x_333_))
{
case 0:
{
lean_object* v___x_334_; 
v___x_334_ = lean_unsigned_to_nat(0u);
return v___x_334_;
}
case 1:
{
lean_object* v___x_335_; 
v___x_335_ = lean_unsigned_to_nat(1u);
return v___x_335_;
}
case 2:
{
lean_object* v___x_336_; 
v___x_336_ = lean_unsigned_to_nat(2u);
return v___x_336_;
}
case 3:
{
lean_object* v___x_337_; 
v___x_337_ = lean_unsigned_to_nat(3u);
return v___x_337_;
}
case 4:
{
lean_object* v___x_338_; 
v___x_338_ = lean_unsigned_to_nat(4u);
return v___x_338_;
}
case 5:
{
lean_object* v___x_339_; 
v___x_339_ = lean_unsigned_to_nat(5u);
return v___x_339_;
}
case 6:
{
lean_object* v___x_340_; 
v___x_340_ = lean_unsigned_to_nat(6u);
return v___x_340_;
}
case 7:
{
lean_object* v___x_341_; 
v___x_341_ = lean_unsigned_to_nat(7u);
return v___x_341_;
}
case 8:
{
lean_object* v___x_342_; 
v___x_342_ = lean_unsigned_to_nat(8u);
return v___x_342_;
}
case 9:
{
lean_object* v___x_343_; 
v___x_343_ = lean_unsigned_to_nat(9u);
return v___x_343_;
}
case 10:
{
lean_object* v___x_344_; 
v___x_344_ = lean_unsigned_to_nat(10u);
return v___x_344_;
}
case 11:
{
lean_object* v___x_345_; 
v___x_345_ = lean_unsigned_to_nat(11u);
return v___x_345_;
}
default: 
{
lean_object* v___x_346_; 
v___x_346_ = lean_unsigned_to_nat(12u);
return v___x_346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorIdx___boxed(lean_object* v_x_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorIdx(v_x_347_);
lean_dec_ref(v_x_347_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(lean_object* v_t_349_, lean_object* v_k_350_){
_start:
{
switch(lean_obj_tag(v_t_349_))
{
case 1:
{
lean_object* v_e_351_; lean_object* v_thm_352_; lean_object* v_d_353_; lean_object* v_a_354_; lean_object* v___x_355_; 
v_e_351_ = lean_ctor_get(v_t_349_, 0);
lean_inc_ref(v_e_351_);
v_thm_352_ = lean_ctor_get(v_t_349_, 1);
lean_inc_ref(v_thm_352_);
v_d_353_ = lean_ctor_get(v_t_349_, 2);
lean_inc(v_d_353_);
v_a_354_ = lean_ctor_get(v_t_349_, 3);
lean_inc_ref(v_a_354_);
lean_dec_ref_known(v_t_349_, 4);
v___x_355_ = lean_apply_4(v_k_350_, v_e_351_, v_thm_352_, v_d_353_, v_a_354_);
return v___x_355_;
}
case 4:
{
lean_object* v_c_u2081_356_; lean_object* v_c_u2082_357_; lean_object* v___x_358_; 
v_c_u2081_356_ = lean_ctor_get(v_t_349_, 0);
lean_inc_ref(v_c_u2081_356_);
v_c_u2082_357_ = lean_ctor_get(v_t_349_, 1);
lean_inc_ref(v_c_u2082_357_);
lean_dec_ref_known(v_t_349_, 2);
v___x_358_ = lean_apply_2(v_k_350_, v_c_u2081_356_, v_c_u2082_357_);
return v___x_358_;
}
case 5:
{
lean_object* v_c_u2081_359_; lean_object* v_c_u2082_360_; lean_object* v___x_361_; 
v_c_u2081_359_ = lean_ctor_get(v_t_349_, 0);
lean_inc_ref(v_c_u2081_359_);
v_c_u2082_360_ = lean_ctor_get(v_t_349_, 1);
lean_inc_ref(v_c_u2082_360_);
lean_dec_ref_known(v_t_349_, 2);
v___x_361_ = lean_apply_2(v_k_350_, v_c_u2081_359_, v_c_u2082_360_);
return v___x_361_;
}
case 7:
{
lean_object* v_x_362_; lean_object* v_c_363_; lean_object* v___x_364_; 
v_x_362_ = lean_ctor_get(v_t_349_, 0);
lean_inc(v_x_362_);
v_c_363_ = lean_ctor_get(v_t_349_, 1);
lean_inc_ref(v_c_363_);
lean_dec_ref_known(v_t_349_, 2);
v___x_364_ = lean_apply_2(v_k_350_, v_x_362_, v_c_363_);
return v___x_364_;
}
case 8:
{
lean_object* v_x_365_; lean_object* v_c_u2081_366_; lean_object* v_c_u2082_367_; lean_object* v___x_368_; 
v_x_365_ = lean_ctor_get(v_t_349_, 0);
lean_inc(v_x_365_);
v_c_u2081_366_ = lean_ctor_get(v_t_349_, 1);
lean_inc_ref(v_c_u2081_366_);
v_c_u2082_367_ = lean_ctor_get(v_t_349_, 2);
lean_inc_ref(v_c_u2082_367_);
lean_dec_ref_known(v_t_349_, 3);
v___x_368_ = lean_apply_3(v_k_350_, v_x_365_, v_c_u2081_366_, v_c_u2082_367_);
return v___x_368_;
}
case 12:
{
lean_object* v_c_369_; lean_object* v_e_370_; lean_object* v_p_371_; lean_object* v___x_372_; 
v_c_369_ = lean_ctor_get(v_t_349_, 0);
lean_inc_ref(v_c_369_);
v_e_370_ = lean_ctor_get(v_t_349_, 1);
lean_inc_ref(v_e_370_);
v_p_371_ = lean_ctor_get(v_t_349_, 2);
lean_inc_ref(v_p_371_);
lean_dec_ref_known(v_t_349_, 3);
v___x_372_ = lean_apply_3(v_k_350_, v_c_369_, v_e_370_, v_p_371_);
return v___x_372_;
}
default: 
{
lean_object* v_e_373_; lean_object* v___x_374_; 
v_e_373_ = lean_ctor_get(v_t_349_, 0);
lean_inc_ref(v_e_373_);
lean_dec_ref(v_t_349_);
v___x_374_ = lean_apply_1(v_k_350_, v_e_373_);
return v___x_374_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim(lean_object* v_motive__7_375_, lean_object* v_ctorIdx_376_, lean_object* v_t_377_, lean_object* v_h_378_, lean_object* v_k_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_377_, v_k_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___boxed(lean_object* v_motive__7_381_, lean_object* v_ctorIdx_382_, lean_object* v_t_383_, lean_object* v_h_384_, lean_object* v_k_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim(v_motive__7_381_, v_ctorIdx_382_, v_t_383_, v_h_384_, v_k_385_);
lean_dec(v_ctorIdx_382_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_core_elim___redArg(lean_object* v_t_387_, lean_object* v_core_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_387_, v_core_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_core_elim(lean_object* v_motive__7_390_, lean_object* v_t_391_, lean_object* v_h_392_, lean_object* v_core_393_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_391_, v_core_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_coreOfNat_elim___redArg(lean_object* v_t_395_, lean_object* v_coreOfNat_396_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_395_, v_coreOfNat_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_coreOfNat_elim(lean_object* v_motive__7_398_, lean_object* v_t_399_, lean_object* v_h_400_, lean_object* v_coreOfNat_401_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_399_, v_coreOfNat_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_norm_elim___redArg(lean_object* v_t_403_, lean_object* v_norm_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_403_, v_norm_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_norm_elim(lean_object* v_motive__7_406_, lean_object* v_t_407_, lean_object* v_h_408_, lean_object* v_norm_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_407_, v_norm_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_divCoeffs_elim___redArg(lean_object* v_t_411_, lean_object* v_divCoeffs_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_411_, v_divCoeffs_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_divCoeffs_elim(lean_object* v_motive__7_414_, lean_object* v_t_415_, lean_object* v_h_416_, lean_object* v_divCoeffs_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_415_, v_divCoeffs_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveCombine_elim___redArg(lean_object* v_t_419_, lean_object* v_solveCombine_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_419_, v_solveCombine_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveCombine_elim(lean_object* v_motive__7_422_, lean_object* v_t_423_, lean_object* v_h_424_, lean_object* v_solveCombine_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_423_, v_solveCombine_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveElim_elim___redArg(lean_object* v_t_427_, lean_object* v_solveElim_428_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_427_, v_solveElim_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveElim_elim(lean_object* v_motive__7_430_, lean_object* v_t_431_, lean_object* v_h_432_, lean_object* v_solveElim_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_431_, v_solveElim_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_elim_elim___redArg(lean_object* v_t_435_, lean_object* v_elim_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_435_, v_elim_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_elim_elim(lean_object* v_motive__7_438_, lean_object* v_t_439_, lean_object* v_h_440_, lean_object* v_elim_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_439_, v_elim_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ofEq_elim___redArg(lean_object* v_t_443_, lean_object* v_ofEq_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_443_, v_ofEq_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ofEq_elim(lean_object* v_motive__7_446_, lean_object* v_t_447_, lean_object* v_h_448_, lean_object* v_ofEq_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_447_, v_ofEq_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_subst_elim___redArg(lean_object* v_t_451_, lean_object* v_subst_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_451_, v_subst_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_subst_elim(lean_object* v_motive__7_454_, lean_object* v_t_455_, lean_object* v_h_456_, lean_object* v_subst_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_455_, v_subst_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2081_elim___redArg(lean_object* v_t_459_, lean_object* v_cooper_u2081_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_459_, v_cooper_u2081_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2081_elim(lean_object* v_motive__7_462_, lean_object* v_t_463_, lean_object* v_h_464_, lean_object* v_cooper_u2081_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_463_, v_cooper_u2081_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2082_elim___redArg(lean_object* v_t_467_, lean_object* v_cooper_u2082_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_467_, v_cooper_u2082_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2082_elim(lean_object* v_motive__7_470_, lean_object* v_t_471_, lean_object* v_h_472_, lean_object* v_cooper_u2082_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_471_, v_cooper_u2082_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_reorder_elim___redArg(lean_object* v_t_475_, lean_object* v_reorder_476_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_475_, v_reorder_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_reorder_elim(lean_object* v_motive__7_478_, lean_object* v_t_479_, lean_object* v_h_480_, lean_object* v_reorder_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_479_, v_reorder_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_commRingNorm_elim___redArg(lean_object* v_t_483_, lean_object* v_commRingNorm_484_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_483_, v_commRingNorm_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_commRingNorm_elim(lean_object* v_motive__7_486_, lean_object* v_t_487_, lean_object* v_h_488_, lean_object* v_commRingNorm_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_487_, v_commRingNorm_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorIdx(lean_object* v_x_491_){
_start:
{
switch(lean_obj_tag(v_x_491_))
{
case 0:
{
lean_object* v___x_492_; 
v___x_492_ = lean_unsigned_to_nat(0u);
return v___x_492_;
}
case 1:
{
lean_object* v___x_493_; 
v___x_493_ = lean_unsigned_to_nat(1u);
return v___x_493_;
}
case 2:
{
lean_object* v___x_494_; 
v___x_494_ = lean_unsigned_to_nat(2u);
return v___x_494_;
}
case 3:
{
lean_object* v___x_495_; 
v___x_495_ = lean_unsigned_to_nat(3u);
return v___x_495_;
}
case 4:
{
lean_object* v___x_496_; 
v___x_496_ = lean_unsigned_to_nat(4u);
return v___x_496_;
}
case 5:
{
lean_object* v___x_497_; 
v___x_497_ = lean_unsigned_to_nat(5u);
return v___x_497_;
}
case 6:
{
lean_object* v___x_498_; 
v___x_498_ = lean_unsigned_to_nat(6u);
return v___x_498_;
}
case 7:
{
lean_object* v___x_499_; 
v___x_499_ = lean_unsigned_to_nat(7u);
return v___x_499_;
}
case 8:
{
lean_object* v___x_500_; 
v___x_500_ = lean_unsigned_to_nat(8u);
return v___x_500_;
}
case 9:
{
lean_object* v___x_501_; 
v___x_501_ = lean_unsigned_to_nat(9u);
return v___x_501_;
}
case 10:
{
lean_object* v___x_502_; 
v___x_502_ = lean_unsigned_to_nat(10u);
return v___x_502_;
}
case 11:
{
lean_object* v___x_503_; 
v___x_503_ = lean_unsigned_to_nat(11u);
return v___x_503_;
}
case 12:
{
lean_object* v___x_504_; 
v___x_504_ = lean_unsigned_to_nat(12u);
return v___x_504_;
}
case 13:
{
lean_object* v___x_505_; 
v___x_505_ = lean_unsigned_to_nat(13u);
return v___x_505_;
}
case 14:
{
lean_object* v___x_506_; 
v___x_506_ = lean_unsigned_to_nat(14u);
return v___x_506_;
}
case 15:
{
lean_object* v___x_507_; 
v___x_507_ = lean_unsigned_to_nat(15u);
return v___x_507_;
}
case 16:
{
lean_object* v___x_508_; 
v___x_508_ = lean_unsigned_to_nat(16u);
return v___x_508_;
}
default: 
{
lean_object* v___x_509_; 
v___x_509_ = lean_unsigned_to_nat(17u);
return v___x_509_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorIdx___boxed(lean_object* v_x_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorIdx(v_x_510_);
lean_dec_ref(v_x_510_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(lean_object* v_t_512_, lean_object* v_k_513_){
_start:
{
switch(lean_obj_tag(v_t_512_))
{
case 1:
{
lean_object* v_e_514_; lean_object* v_p_515_; lean_object* v___x_516_; 
v_e_514_ = lean_ctor_get(v_t_512_, 0);
lean_inc_ref(v_e_514_);
v_p_515_ = lean_ctor_get(v_t_512_, 1);
lean_inc_ref(v_p_515_);
lean_dec_ref_known(v_t_512_, 2);
v___x_516_ = lean_apply_2(v_k_513_, v_e_514_, v_p_515_);
return v___x_516_;
}
case 2:
{
lean_object* v_e_517_; uint8_t v_pos_518_; lean_object* v_toIntThm_519_; lean_object* v_lhs_520_; lean_object* v_rhs_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v_e_517_ = lean_ctor_get(v_t_512_, 0);
lean_inc_ref(v_e_517_);
v_pos_518_ = lean_ctor_get_uint8(v_t_512_, sizeof(void*)*4);
v_toIntThm_519_ = lean_ctor_get(v_t_512_, 1);
lean_inc_ref(v_toIntThm_519_);
v_lhs_520_ = lean_ctor_get(v_t_512_, 2);
lean_inc_ref(v_lhs_520_);
v_rhs_521_ = lean_ctor_get(v_t_512_, 3);
lean_inc_ref(v_rhs_521_);
lean_dec_ref_known(v_t_512_, 4);
v___x_522_ = lean_box(v_pos_518_);
v___x_523_ = lean_apply_5(v_k_513_, v_e_517_, v___x_522_, v_toIntThm_519_, v_lhs_520_, v_rhs_521_);
return v___x_523_;
}
case 5:
{
lean_object* v_h_524_; lean_object* v___x_525_; 
v_h_524_ = lean_ctor_get(v_t_512_, 0);
lean_inc(v_h_524_);
lean_dec_ref_known(v_t_512_, 1);
v___x_525_ = lean_apply_1(v_k_513_, v_h_524_);
return v___x_525_;
}
case 8:
{
lean_object* v_c_u2081_526_; lean_object* v_c_u2082_527_; lean_object* v___x_528_; 
v_c_u2081_526_ = lean_ctor_get(v_t_512_, 0);
lean_inc_ref(v_c_u2081_526_);
v_c_u2082_527_ = lean_ctor_get(v_t_512_, 1);
lean_inc_ref(v_c_u2082_527_);
lean_dec_ref_known(v_t_512_, 2);
v___x_528_ = lean_apply_2(v_k_513_, v_c_u2081_526_, v_c_u2082_527_);
return v___x_528_;
}
case 9:
{
lean_object* v_c_u2081_529_; lean_object* v_c_u2082_530_; lean_object* v_k_531_; lean_object* v___x_532_; 
v_c_u2081_529_ = lean_ctor_get(v_t_512_, 0);
lean_inc_ref(v_c_u2081_529_);
v_c_u2082_530_ = lean_ctor_get(v_t_512_, 1);
lean_inc_ref(v_c_u2082_530_);
v_k_531_ = lean_ctor_get(v_t_512_, 2);
lean_inc(v_k_531_);
lean_dec_ref_known(v_t_512_, 3);
v___x_532_ = lean_apply_3(v_k_513_, v_c_u2081_529_, v_c_u2082_530_, v_k_531_);
return v___x_532_;
}
case 10:
{
lean_object* v_x_533_; lean_object* v_c_u2081_534_; lean_object* v_c_u2082_535_; lean_object* v___x_536_; 
v_x_533_ = lean_ctor_get(v_t_512_, 0);
lean_inc(v_x_533_);
v_c_u2081_534_ = lean_ctor_get(v_t_512_, 1);
lean_inc_ref(v_c_u2081_534_);
v_c_u2082_535_ = lean_ctor_get(v_t_512_, 2);
lean_inc_ref(v_c_u2082_535_);
lean_dec_ref_known(v_t_512_, 3);
v___x_536_ = lean_apply_3(v_k_513_, v_x_533_, v_c_u2081_534_, v_c_u2082_535_);
return v___x_536_;
}
case 11:
{
lean_object* v_c_u2081_537_; lean_object* v_c_u2082_538_; lean_object* v___x_539_; 
v_c_u2081_537_ = lean_ctor_get(v_t_512_, 0);
lean_inc_ref(v_c_u2081_537_);
v_c_u2082_538_ = lean_ctor_get(v_t_512_, 1);
lean_inc_ref(v_c_u2082_538_);
lean_dec_ref_known(v_t_512_, 2);
v___x_539_ = lean_apply_2(v_k_513_, v_c_u2081_537_, v_c_u2082_538_);
return v___x_539_;
}
case 12:
{
lean_object* v_c_u2081_540_; lean_object* v_decVar_541_; lean_object* v_h_542_; lean_object* v_decVars_543_; lean_object* v___x_544_; 
v_c_u2081_540_ = lean_ctor_get(v_t_512_, 0);
lean_inc_ref(v_c_u2081_540_);
v_decVar_541_ = lean_ctor_get(v_t_512_, 1);
lean_inc(v_decVar_541_);
v_h_542_ = lean_ctor_get(v_t_512_, 2);
lean_inc_ref(v_h_542_);
v_decVars_543_ = lean_ctor_get(v_t_512_, 3);
lean_inc_ref(v_decVars_543_);
lean_dec_ref_known(v_t_512_, 4);
v___x_544_ = lean_apply_4(v_k_513_, v_c_u2081_540_, v_decVar_541_, v_h_542_, v_decVars_543_);
return v___x_544_;
}
case 14:
{
lean_object* v_c_u2081_545_; lean_object* v_c_u2082_546_; lean_object* v___x_547_; 
v_c_u2081_545_ = lean_ctor_get(v_t_512_, 0);
lean_inc_ref(v_c_u2081_545_);
v_c_u2082_546_ = lean_ctor_get(v_t_512_, 1);
lean_inc_ref(v_c_u2082_546_);
lean_dec_ref_known(v_t_512_, 2);
v___x_547_ = lean_apply_2(v_k_513_, v_c_u2081_545_, v_c_u2082_546_);
return v___x_547_;
}
case 15:
{
lean_object* v_c_u2081_548_; lean_object* v_c_u2082_549_; lean_object* v___x_550_; 
v_c_u2081_548_ = lean_ctor_get(v_t_512_, 0);
lean_inc_ref(v_c_u2081_548_);
v_c_u2082_549_ = lean_ctor_get(v_t_512_, 1);
lean_inc_ref(v_c_u2082_549_);
lean_dec_ref_known(v_t_512_, 2);
v___x_550_ = lean_apply_2(v_k_513_, v_c_u2081_548_, v_c_u2082_549_);
return v___x_550_;
}
case 17:
{
lean_object* v_c_551_; lean_object* v_e_552_; lean_object* v_p_553_; lean_object* v___x_554_; 
v_c_551_ = lean_ctor_get(v_t_512_, 0);
lean_inc_ref(v_c_551_);
v_e_552_ = lean_ctor_get(v_t_512_, 1);
lean_inc_ref(v_e_552_);
v_p_553_ = lean_ctor_get(v_t_512_, 2);
lean_inc_ref(v_p_553_);
lean_dec_ref_known(v_t_512_, 3);
v___x_554_ = lean_apply_3(v_k_513_, v_c_551_, v_e_552_, v_p_553_);
return v___x_554_;
}
default: 
{
lean_object* v_e_555_; lean_object* v___x_556_; 
v_e_555_ = lean_ctor_get(v_t_512_, 0);
lean_inc_ref(v_e_555_);
lean_dec_ref(v_t_512_);
v___x_556_ = lean_apply_1(v_k_513_, v_e_555_);
return v___x_556_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim(lean_object* v_motive__9_557_, lean_object* v_ctorIdx_558_, lean_object* v_t_559_, lean_object* v_h_560_, lean_object* v_k_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_559_, v_k_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___boxed(lean_object* v_motive__9_563_, lean_object* v_ctorIdx_564_, lean_object* v_t_565_, lean_object* v_h_566_, lean_object* v_k_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim(v_motive__9_563_, v_ctorIdx_564_, v_t_565_, v_h_566_, v_k_567_);
lean_dec(v_ctorIdx_564_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_core_elim___redArg(lean_object* v_t_569_, lean_object* v_core_570_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_569_, v_core_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_core_elim(lean_object* v_motive__9_572_, lean_object* v_t_573_, lean_object* v_h_574_, lean_object* v_core_575_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_573_, v_core_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreNeg_elim___redArg(lean_object* v_t_577_, lean_object* v_coreNeg_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_577_, v_coreNeg_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreNeg_elim(lean_object* v_motive__9_580_, lean_object* v_t_581_, lean_object* v_h_582_, lean_object* v_coreNeg_583_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_581_, v_coreNeg_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreToInt_elim___redArg(lean_object* v_t_585_, lean_object* v_coreToInt_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_585_, v_coreToInt_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreToInt_elim(lean_object* v_motive__9_588_, lean_object* v_t_589_, lean_object* v_h_590_, lean_object* v_coreToInt_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_589_, v_coreToInt_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofNatNonneg_elim___redArg(lean_object* v_t_593_, lean_object* v_ofNatNonneg_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_593_, v_ofNatNonneg_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofNatNonneg_elim(lean_object* v_motive__9_596_, lean_object* v_t_597_, lean_object* v_h_598_, lean_object* v_ofNatNonneg_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_597_, v_ofNatNonneg_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_bound_elim___redArg(lean_object* v_t_601_, lean_object* v_bound_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_601_, v_bound_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_bound_elim(lean_object* v_motive__9_604_, lean_object* v_t_605_, lean_object* v_h_606_, lean_object* v_bound_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_605_, v_bound_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dec_elim___redArg(lean_object* v_t_609_, lean_object* v_dec_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_609_, v_dec_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dec_elim(lean_object* v_motive__9_612_, lean_object* v_t_613_, lean_object* v_h_614_, lean_object* v_dec_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_613_, v_dec_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_norm_elim___redArg(lean_object* v_t_617_, lean_object* v_norm_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_617_, v_norm_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_norm_elim(lean_object* v_motive__9_620_, lean_object* v_t_621_, lean_object* v_h_622_, lean_object* v_norm_623_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_621_, v_norm_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_divCoeffs_elim___redArg(lean_object* v_t_625_, lean_object* v_divCoeffs_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_625_, v_divCoeffs_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_divCoeffs_elim(lean_object* v_motive__9_628_, lean_object* v_t_629_, lean_object* v_h_630_, lean_object* v_divCoeffs_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_629_, v_divCoeffs_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combine_elim___redArg(lean_object* v_t_633_, lean_object* v_combine_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_633_, v_combine_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combine_elim(lean_object* v_motive__9_636_, lean_object* v_t_637_, lean_object* v_h_638_, lean_object* v_combine_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_637_, v_combine_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combineDivCoeffs_elim___redArg(lean_object* v_t_641_, lean_object* v_combineDivCoeffs_642_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_641_, v_combineDivCoeffs_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combineDivCoeffs_elim(lean_object* v_motive__9_644_, lean_object* v_t_645_, lean_object* v_h_646_, lean_object* v_combineDivCoeffs_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_645_, v_combineDivCoeffs_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_subst_elim___redArg(lean_object* v_t_649_, lean_object* v_subst_650_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_649_, v_subst_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_subst_elim(lean_object* v_motive__9_652_, lean_object* v_t_653_, lean_object* v_h_654_, lean_object* v_subst_655_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_653_, v_subst_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofLeDiseq_elim___redArg(lean_object* v_t_657_, lean_object* v_ofLeDiseq_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_657_, v_ofLeDiseq_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofLeDiseq_elim(lean_object* v_motive__9_660_, lean_object* v_t_661_, lean_object* v_h_662_, lean_object* v_ofLeDiseq_663_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_661_, v_ofLeDiseq_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofDiseqSplit_elim___redArg(lean_object* v_t_665_, lean_object* v_ofDiseqSplit_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_665_, v_ofDiseqSplit_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofDiseqSplit_elim(lean_object* v_motive__9_668_, lean_object* v_t_669_, lean_object* v_h_670_, lean_object* v_ofDiseqSplit_671_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_669_, v_ofDiseqSplit_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_cooper_elim___redArg(lean_object* v_t_673_, lean_object* v_cooper_674_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_673_, v_cooper_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_cooper_elim(lean_object* v_motive__9_676_, lean_object* v_t_677_, lean_object* v_h_678_, lean_object* v_cooper_679_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_677_, v_cooper_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dvdTight_elim___redArg(lean_object* v_t_681_, lean_object* v_dvdTight_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_681_, v_dvdTight_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dvdTight_elim(lean_object* v_motive__9_684_, lean_object* v_t_685_, lean_object* v_h_686_, lean_object* v_dvdTight_687_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_685_, v_dvdTight_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_negDvdTight_elim___redArg(lean_object* v_t_689_, lean_object* v_negDvdTight_690_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_689_, v_negDvdTight_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_negDvdTight_elim(lean_object* v_motive__9_692_, lean_object* v_t_693_, lean_object* v_h_694_, lean_object* v_negDvdTight_695_){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_693_, v_negDvdTight_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_reorder_elim___redArg(lean_object* v_t_697_, lean_object* v_reorder_698_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_697_, v_reorder_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_reorder_elim(lean_object* v_motive__9_700_, lean_object* v_t_701_, lean_object* v_h_702_, lean_object* v_reorder_703_){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_701_, v_reorder_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_commRingNorm_elim___redArg(lean_object* v_t_705_, lean_object* v_commRingNorm_706_){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_705_, v_commRingNorm_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_commRingNorm_elim(lean_object* v_motive__9_708_, lean_object* v_t_709_, lean_object* v_h_710_, lean_object* v_commRingNorm_711_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_709_, v_commRingNorm_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorIdx(lean_object* v_x_713_){
_start:
{
switch(lean_obj_tag(v_x_713_))
{
case 0:
{
lean_object* v___x_714_; 
v___x_714_ = lean_unsigned_to_nat(0u);
return v___x_714_;
}
case 1:
{
lean_object* v___x_715_; 
v___x_715_ = lean_unsigned_to_nat(1u);
return v___x_715_;
}
case 2:
{
lean_object* v___x_716_; 
v___x_716_ = lean_unsigned_to_nat(2u);
return v___x_716_;
}
case 3:
{
lean_object* v___x_717_; 
v___x_717_ = lean_unsigned_to_nat(3u);
return v___x_717_;
}
case 4:
{
lean_object* v___x_718_; 
v___x_718_ = lean_unsigned_to_nat(4u);
return v___x_718_;
}
case 5:
{
lean_object* v___x_719_; 
v___x_719_ = lean_unsigned_to_nat(5u);
return v___x_719_;
}
case 6:
{
lean_object* v___x_720_; 
v___x_720_ = lean_unsigned_to_nat(6u);
return v___x_720_;
}
case 7:
{
lean_object* v___x_721_; 
v___x_721_ = lean_unsigned_to_nat(7u);
return v___x_721_;
}
default: 
{
lean_object* v___x_722_; 
v___x_722_ = lean_unsigned_to_nat(8u);
return v___x_722_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorIdx___boxed(lean_object* v_x_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorIdx(v_x_723_);
lean_dec_ref(v_x_723_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(lean_object* v_t_725_, lean_object* v_k_726_){
_start:
{
switch(lean_obj_tag(v_t_725_))
{
case 0:
{
lean_object* v_a_727_; lean_object* v_zero_728_; lean_object* v___x_729_; 
v_a_727_ = lean_ctor_get(v_t_725_, 0);
lean_inc_ref(v_a_727_);
v_zero_728_ = lean_ctor_get(v_t_725_, 1);
lean_inc_ref(v_zero_728_);
lean_dec_ref_known(v_t_725_, 2);
v___x_729_ = lean_apply_2(v_k_726_, v_a_727_, v_zero_728_);
return v___x_729_;
}
case 1:
{
lean_object* v_a_730_; lean_object* v_b_731_; lean_object* v_p_u2081_732_; lean_object* v_p_u2082_733_; lean_object* v___x_734_; 
v_a_730_ = lean_ctor_get(v_t_725_, 0);
lean_inc_ref(v_a_730_);
v_b_731_ = lean_ctor_get(v_t_725_, 1);
lean_inc_ref(v_b_731_);
v_p_u2081_732_ = lean_ctor_get(v_t_725_, 2);
lean_inc_ref(v_p_u2081_732_);
v_p_u2082_733_ = lean_ctor_get(v_t_725_, 3);
lean_inc_ref(v_p_u2082_733_);
lean_dec_ref_known(v_t_725_, 4);
v___x_734_ = lean_apply_4(v_k_726_, v_a_730_, v_b_731_, v_p_u2081_732_, v_p_u2082_733_);
return v___x_734_;
}
case 2:
{
lean_object* v_a_735_; lean_object* v_b_736_; lean_object* v_toIntThm_737_; lean_object* v_lhs_738_; lean_object* v_rhs_739_; lean_object* v___x_740_; 
v_a_735_ = lean_ctor_get(v_t_725_, 0);
lean_inc_ref(v_a_735_);
v_b_736_ = lean_ctor_get(v_t_725_, 1);
lean_inc_ref(v_b_736_);
v_toIntThm_737_ = lean_ctor_get(v_t_725_, 2);
lean_inc_ref(v_toIntThm_737_);
v_lhs_738_ = lean_ctor_get(v_t_725_, 3);
lean_inc_ref(v_lhs_738_);
v_rhs_739_ = lean_ctor_get(v_t_725_, 4);
lean_inc_ref(v_rhs_739_);
lean_dec_ref_known(v_t_725_, 5);
v___x_740_ = lean_apply_5(v_k_726_, v_a_735_, v_b_736_, v_toIntThm_737_, v_lhs_738_, v_rhs_739_);
return v___x_740_;
}
case 6:
{
lean_object* v_x_741_; lean_object* v_c_u2081_742_; lean_object* v_c_u2082_743_; lean_object* v___x_744_; 
v_x_741_ = lean_ctor_get(v_t_725_, 0);
lean_inc(v_x_741_);
v_c_u2081_742_ = lean_ctor_get(v_t_725_, 1);
lean_inc_ref(v_c_u2081_742_);
v_c_u2082_743_ = lean_ctor_get(v_t_725_, 2);
lean_inc_ref(v_c_u2082_743_);
lean_dec_ref_known(v_t_725_, 3);
v___x_744_ = lean_apply_3(v_k_726_, v_x_741_, v_c_u2081_742_, v_c_u2082_743_);
return v___x_744_;
}
case 8:
{
lean_object* v_c_745_; lean_object* v_e_746_; lean_object* v_p_747_; lean_object* v___x_748_; 
v_c_745_ = lean_ctor_get(v_t_725_, 0);
lean_inc_ref(v_c_745_);
v_e_746_ = lean_ctor_get(v_t_725_, 1);
lean_inc_ref(v_e_746_);
v_p_747_ = lean_ctor_get(v_t_725_, 2);
lean_inc_ref(v_p_747_);
lean_dec_ref_known(v_t_725_, 3);
v___x_748_ = lean_apply_3(v_k_726_, v_c_745_, v_e_746_, v_p_747_);
return v___x_748_;
}
default: 
{
lean_object* v_c_749_; lean_object* v___x_750_; 
v_c_749_ = lean_ctor_get(v_t_725_, 0);
lean_inc_ref(v_c_749_);
lean_dec_ref(v_t_725_);
v___x_750_ = lean_apply_1(v_k_726_, v_c_749_);
return v___x_750_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim(lean_object* v_motive__11_751_, lean_object* v_ctorIdx_752_, lean_object* v_t_753_, lean_object* v_h_754_, lean_object* v_k_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_753_, v_k_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___boxed(lean_object* v_motive__11_757_, lean_object* v_ctorIdx_758_, lean_object* v_t_759_, lean_object* v_h_760_, lean_object* v_k_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim(v_motive__11_757_, v_ctorIdx_758_, v_t_759_, v_h_760_, v_k_761_);
lean_dec(v_ctorIdx_758_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core0_elim___redArg(lean_object* v_t_763_, lean_object* v_core0_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_763_, v_core0_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core0_elim(lean_object* v_motive__11_766_, lean_object* v_t_767_, lean_object* v_h_768_, lean_object* v_core0_769_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_767_, v_core0_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core_elim___redArg(lean_object* v_t_771_, lean_object* v_core_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_771_, v_core_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core_elim(lean_object* v_motive__11_774_, lean_object* v_t_775_, lean_object* v_h_776_, lean_object* v_core_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_775_, v_core_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_coreToInt_elim___redArg(lean_object* v_t_779_, lean_object* v_coreToInt_780_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_779_, v_coreToInt_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_coreToInt_elim(lean_object* v_motive__11_782_, lean_object* v_t_783_, lean_object* v_h_784_, lean_object* v_coreToInt_785_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_783_, v_coreToInt_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_norm_elim___redArg(lean_object* v_t_787_, lean_object* v_norm_788_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_787_, v_norm_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_norm_elim(lean_object* v_motive__11_790_, lean_object* v_t_791_, lean_object* v_h_792_, lean_object* v_norm_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_791_, v_norm_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_divCoeffs_elim___redArg(lean_object* v_t_795_, lean_object* v_divCoeffs_796_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_795_, v_divCoeffs_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_divCoeffs_elim(lean_object* v_motive__11_798_, lean_object* v_t_799_, lean_object* v_h_800_, lean_object* v_divCoeffs_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_799_, v_divCoeffs_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_neg_elim___redArg(lean_object* v_t_803_, lean_object* v_neg_804_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_803_, v_neg_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_neg_elim(lean_object* v_motive__11_806_, lean_object* v_t_807_, lean_object* v_h_808_, lean_object* v_neg_809_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_807_, v_neg_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_subst_elim___redArg(lean_object* v_t_811_, lean_object* v_subst_812_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_811_, v_subst_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_subst_elim(lean_object* v_motive__11_814_, lean_object* v_t_815_, lean_object* v_h_816_, lean_object* v_subst_817_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_815_, v_subst_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_reorder_elim___redArg(lean_object* v_t_819_, lean_object* v_reorder_820_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_819_, v_reorder_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_reorder_elim(lean_object* v_motive__11_822_, lean_object* v_t_823_, lean_object* v_h_824_, lean_object* v_reorder_825_){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_823_, v_reorder_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_commRingNorm_elim___redArg(lean_object* v_t_827_, lean_object* v_commRingNorm_828_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_827_, v_commRingNorm_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_commRingNorm_elim(lean_object* v_motive__11_830_, lean_object* v_t_831_, lean_object* v_h_832_, lean_object* v_commRingNorm_833_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_831_, v_commRingNorm_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorIdx(lean_object* v_x_835_){
_start:
{
switch(lean_obj_tag(v_x_835_))
{
case 0:
{
lean_object* v___x_836_; 
v___x_836_ = lean_unsigned_to_nat(0u);
return v___x_836_;
}
case 1:
{
lean_object* v___x_837_; 
v___x_837_ = lean_unsigned_to_nat(1u);
return v___x_837_;
}
case 2:
{
lean_object* v___x_838_; 
v___x_838_ = lean_unsigned_to_nat(2u);
return v___x_838_;
}
case 3:
{
lean_object* v___x_839_; 
v___x_839_ = lean_unsigned_to_nat(3u);
return v___x_839_;
}
default: 
{
lean_object* v___x_840_; 
v___x_840_ = lean_unsigned_to_nat(4u);
return v___x_840_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorIdx___boxed(lean_object* v_x_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorIdx(v_x_841_);
lean_dec_ref(v_x_841_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(lean_object* v_t_843_, lean_object* v_k_844_){
_start:
{
if (lean_obj_tag(v_t_843_) == 4)
{
lean_object* v_c_u2081_845_; lean_object* v_c_u2082_846_; lean_object* v_c_u2083_847_; lean_object* v___x_848_; 
v_c_u2081_845_ = lean_ctor_get(v_t_843_, 0);
lean_inc_ref(v_c_u2081_845_);
v_c_u2082_846_ = lean_ctor_get(v_t_843_, 1);
lean_inc_ref(v_c_u2082_846_);
v_c_u2083_847_ = lean_ctor_get(v_t_843_, 2);
lean_inc_ref(v_c_u2083_847_);
lean_dec_ref_known(v_t_843_, 3);
v___x_848_ = lean_apply_3(v_k_844_, v_c_u2081_845_, v_c_u2082_846_, v_c_u2083_847_);
return v___x_848_;
}
else
{
lean_object* v_c_849_; lean_object* v___x_850_; 
v_c_849_ = lean_ctor_get(v_t_843_, 0);
lean_inc_ref(v_c_849_);
lean_dec_ref(v_t_843_);
v___x_850_ = lean_apply_1(v_k_844_, v_c_849_);
return v___x_850_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim(lean_object* v_motive__12_851_, lean_object* v_ctorIdx_852_, lean_object* v_t_853_, lean_object* v_h_854_, lean_object* v_k_855_){
_start:
{
lean_object* v___x_856_; 
v___x_856_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_853_, v_k_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___boxed(lean_object* v_motive__12_857_, lean_object* v_ctorIdx_858_, lean_object* v_t_859_, lean_object* v_h_860_, lean_object* v_k_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim(v_motive__12_857_, v_ctorIdx_858_, v_t_859_, v_h_860_, v_k_861_);
lean_dec(v_ctorIdx_858_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_dvd_elim___redArg(lean_object* v_t_863_, lean_object* v_dvd_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_863_, v_dvd_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_dvd_elim(lean_object* v_motive__12_866_, lean_object* v_t_867_, lean_object* v_h_868_, lean_object* v_dvd_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_867_, v_dvd_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_le_elim___redArg(lean_object* v_t_871_, lean_object* v_le_872_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_871_, v_le_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_le_elim(lean_object* v_motive__12_874_, lean_object* v_t_875_, lean_object* v_h_876_, lean_object* v_le_877_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_875_, v_le_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_eq_elim___redArg(lean_object* v_t_879_, lean_object* v_eq_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_879_, v_eq_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_eq_elim(lean_object* v_motive__12_882_, lean_object* v_t_883_, lean_object* v_h_884_, lean_object* v_eq_885_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_883_, v_eq_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_diseq_elim___redArg(lean_object* v_t_887_, lean_object* v_diseq_888_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_887_, v_diseq_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_diseq_elim(lean_object* v_motive__12_890_, lean_object* v_t_891_, lean_object* v_h_892_, lean_object* v_diseq_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_891_, v_diseq_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_cooper_elim___redArg(lean_object* v_t_895_, lean_object* v_cooper_896_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_895_, v_cooper_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_cooper_elim(lean_object* v_motive__12_898_, lean_object* v_t_899_, lean_object* v_h_900_, lean_object* v_cooper_901_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_899_, v_cooper_901_);
return v___x_902_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0(void){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0);
v___x_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
return v___x_904_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3(void){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_908_ = lean_box(0);
v___x_909_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__2));
v___x_910_ = l_Lean_Expr_const___override(v___x_909_, v___x_908_);
return v___x_910_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4(void){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3);
v___x_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
return v___x_912_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5(void){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_913_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4);
v___x_914_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0);
v___x_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
lean_ctor_set(v___x_915_, 1, v___x_913_);
return v___x_915_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr(void){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5);
return v___x_916_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0(void){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_917_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3);
v___x_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
return v___x_918_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1(void){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_919_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0);
v___x_920_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0);
v___x_921_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0);
v___x_922_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_922_, 0, v___x_921_);
lean_ctor_set(v___x_922_, 1, v___x_920_);
lean_ctor_set(v___x_922_, 2, v___x_919_);
return v___x_922_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr(void){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1);
return v___x_923_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0(void){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; uint8_t v___x_926_; lean_object* v___x_927_; 
v___x_924_ = lean_box(0);
v___x_925_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5);
v___x_926_ = 0;
v___x_927_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_927_, 0, v___x_925_);
lean_ctor_set(v___x_927_, 1, v___x_925_);
lean_ctor_set(v___x_927_, 2, v___x_924_);
lean_ctor_set_uint8(v___x_927_, sizeof(void*)*3, v___x_926_);
return v___x_927_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred(void){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0);
return v___x_928_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1(void){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_931_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__0));
v___x_932_ = lean_unsigned_to_nat(0u);
v___x_933_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0);
v___x_934_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
lean_ctor_set(v___x_934_, 1, v___x_932_);
lean_ctor_set(v___x_934_, 2, v___x_931_);
return v___x_934_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit(void){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1);
return v___x_935_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_936_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__1(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_937_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0);
v___x_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0(lean_object* v_00_u03b2_939_){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__1);
return v___x_940_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0(void){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_941_ = lean_unsigned_to_nat(32u);
v___x_942_ = lean_mk_empty_array_with_capacity(v___x_941_);
v___x_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
return v___x_943_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1(void){
_start:
{
size_t v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_944_ = ((size_t)5ULL);
v___x_945_ = lean_unsigned_to_nat(0u);
v___x_946_ = lean_unsigned_to_nat(32u);
v___x_947_ = lean_mk_empty_array_with_capacity(v___x_946_);
v___x_948_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0);
v___x_949_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_949_, 0, v___x_948_);
lean_ctor_set(v___x_949_, 1, v___x_947_);
lean_ctor_set(v___x_949_, 2, v___x_945_);
lean_ctor_set(v___x_949_, 3, v___x_945_);
lean_ctor_set_usize(v___x_949_, 4, v___x_944_);
return v___x_949_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2(void){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_950_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3(void){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2);
v___x_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
return v___x_952_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__4(void){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0(lean_box(0));
return v___x_953_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5(void){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; uint8_t v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_954_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__4);
v___x_955_ = lean_box(0);
v___x_956_ = 0;
v___x_957_ = lean_unsigned_to_nat(0u);
v___x_958_ = lean_box(0);
v___x_959_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3);
v___x_960_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1);
v___x_961_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v___x_961_, 0, v___x_960_);
lean_ctor_set(v___x_961_, 1, v___x_959_);
lean_ctor_set(v___x_961_, 2, v___x_960_);
lean_ctor_set(v___x_961_, 3, v___x_959_);
lean_ctor_set(v___x_961_, 4, v___x_959_);
lean_ctor_set(v___x_961_, 5, v___x_959_);
lean_ctor_set(v___x_961_, 6, v___x_960_);
lean_ctor_set(v___x_961_, 7, v___x_960_);
lean_ctor_set(v___x_961_, 8, v___x_960_);
lean_ctor_set(v___x_961_, 9, v___x_960_);
lean_ctor_set(v___x_961_, 10, v___x_960_);
lean_ctor_set(v___x_961_, 11, v___x_958_);
lean_ctor_set(v___x_961_, 12, v___x_960_);
lean_ctor_set(v___x_961_, 13, v___x_960_);
lean_ctor_set(v___x_961_, 14, v___x_957_);
lean_ctor_set(v___x_961_, 15, v___x_955_);
lean_ctor_set(v___x_961_, 16, v___x_959_);
lean_ctor_set(v___x_961_, 17, v___x_954_);
lean_ctor_set(v___x_961_, 18, v___x_959_);
lean_ctor_set(v___x_961_, 19, v___x_960_);
lean_ctor_set(v___x_961_, 20, v___x_959_);
lean_ctor_set(v___x_961_, 21, v___x_959_);
lean_ctor_set(v___x_961_, 22, v___x_959_);
lean_ctor_set_uint8(v___x_961_, sizeof(void*)*23, v___x_956_);
lean_ctor_set_uint8(v___x_961_, sizeof(void*)*23 + 1, v___x_956_);
return v___x_961_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default(void){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5);
return v___x_962_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState(void){
_start:
{
lean_object* v___x_963_; 
v___x_963_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default;
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(lean_object* v___x_964_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_966_, 0, v___x_964_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2____boxed(lean_object* v___x_967_, lean_object* v___y_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(v___x_967_);
return v_res_969_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_970_; lean_object* v___f_971_; 
v___x_970_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5);
v___f_971_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_971_, 0, v___x_970_);
return v___f_971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_973_; lean_object* v___x_974_; 
v___f_973_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_);
v___x_974_ = l_Lean_Meta_Grind_registerSolverExtension___redArg(v___f_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2____boxed(lean_object* v_a_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_();
return v_res_976_;
}
}
lean_object* runtime_initialize_Init_Data_Int_Linear(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToIntInfo(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Int_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToIntInfo(builtin);
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
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToIntInfo(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Int_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToIntInfo(builtin);
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
