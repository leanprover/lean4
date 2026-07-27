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
lean_object* v_e_87_; lean_object* v_e_x27_88_; lean_object* v___x_89_; 
v_e_87_ = lean_ctor_get(v_t_71_, 0);
lean_inc_ref(v_e_87_);
v_e_x27_88_ = lean_ctor_get(v_t_71_, 1);
lean_inc_ref(v_e_x27_88_);
lean_dec_ref_known(v_t_71_, 2);
v___x_89_ = lean_apply_2(v_k_72_, v_e_87_, v_e_x27_88_);
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
lean_object* v_e_105_; lean_object* v_e_x27_106_; lean_object* v_p_107_; lean_object* v_re_108_; lean_object* v_rp_109_; lean_object* v_p_x27_110_; lean_object* v___x_111_; 
v_e_105_ = lean_ctor_get(v_t_71_, 0);
lean_inc_ref(v_e_105_);
v_e_x27_106_ = lean_ctor_get(v_t_71_, 1);
lean_inc_ref(v_e_x27_106_);
v_p_107_ = lean_ctor_get(v_t_71_, 2);
lean_inc_ref(v_p_107_);
v_re_108_ = lean_ctor_get(v_t_71_, 3);
lean_inc_ref(v_re_108_);
v_rp_109_ = lean_ctor_get(v_t_71_, 4);
lean_inc_ref(v_rp_109_);
v_p_x27_110_ = lean_ctor_get(v_t_71_, 5);
lean_inc_ref(v_p_x27_110_);
lean_dec_ref_known(v_t_71_, 6);
v___x_111_ = lean_apply_6(v_k_72_, v_e_105_, v_e_x27_106_, v_p_107_, v_re_108_, v_rp_109_, v_p_x27_110_);
return v___x_111_;
}
case 13:
{
lean_object* v_h_112_; lean_object* v_x_113_; lean_object* v_e_x27_114_; lean_object* v_p_115_; lean_object* v_re_116_; lean_object* v_rp_117_; lean_object* v_p_x27_118_; lean_object* v___x_119_; 
v_h_112_ = lean_ctor_get(v_t_71_, 0);
lean_inc_ref(v_h_112_);
v_x_113_ = lean_ctor_get(v_t_71_, 1);
lean_inc(v_x_113_);
v_e_x27_114_ = lean_ctor_get(v_t_71_, 2);
lean_inc_ref(v_e_x27_114_);
v_p_115_ = lean_ctor_get(v_t_71_, 3);
lean_inc_ref(v_p_115_);
v_re_116_ = lean_ctor_get(v_t_71_, 4);
lean_inc_ref(v_re_116_);
v_rp_117_ = lean_ctor_get(v_t_71_, 5);
lean_inc_ref(v_rp_117_);
v_p_x27_118_ = lean_ctor_get(v_t_71_, 6);
lean_inc_ref(v_p_x27_118_);
lean_dec_ref_known(v_t_71_, 7);
v___x_119_ = lean_apply_7(v_k_72_, v_h_112_, v_x_113_, v_e_x27_114_, v_p_115_, v_re_116_, v_rp_117_, v_p_x27_118_);
return v___x_119_;
}
case 14:
{
lean_object* v_a_x3f_120_; lean_object* v_cs_121_; lean_object* v___x_122_; 
v_a_x3f_120_ = lean_ctor_get(v_t_71_, 0);
lean_inc(v_a_x3f_120_);
v_cs_121_ = lean_ctor_get(v_t_71_, 1);
lean_inc_ref(v_cs_121_);
lean_dec_ref_known(v_t_71_, 2);
v___x_122_ = lean_apply_2(v_k_72_, v_a_x3f_120_, v_cs_121_);
return v___x_122_;
}
case 15:
{
lean_object* v_k_123_; lean_object* v_y_x3f_124_; lean_object* v_c_125_; lean_object* v___x_126_; 
v_k_123_ = lean_ctor_get(v_t_71_, 0);
lean_inc(v_k_123_);
v_y_x3f_124_ = lean_ctor_get(v_t_71_, 1);
lean_inc(v_y_x3f_124_);
v_c_125_ = lean_ctor_get(v_t_71_, 2);
lean_inc_ref(v_c_125_);
lean_dec_ref_known(v_t_71_, 3);
v___x_126_ = lean_apply_3(v_k_72_, v_k_123_, v_y_x3f_124_, v_c_125_);
return v___x_126_;
}
case 16:
{
lean_object* v_k_127_; lean_object* v_y_x3f_128_; lean_object* v_c_129_; lean_object* v___x_130_; 
v_k_127_ = lean_ctor_get(v_t_71_, 0);
lean_inc(v_k_127_);
v_y_x3f_128_ = lean_ctor_get(v_t_71_, 1);
lean_inc(v_y_x3f_128_);
v_c_129_ = lean_ctor_get(v_t_71_, 2);
lean_inc_ref(v_c_129_);
lean_dec_ref_known(v_t_71_, 3);
v___x_130_ = lean_apply_3(v_k_72_, v_k_127_, v_y_x3f_128_, v_c_129_);
return v___x_130_;
}
case 17:
{
lean_object* v_ka_131_; lean_object* v_ca_x3f_132_; lean_object* v_kb_133_; lean_object* v_cb_x3f_134_; lean_object* v___x_135_; 
v_ka_131_ = lean_ctor_get(v_t_71_, 0);
lean_inc(v_ka_131_);
v_ca_x3f_132_ = lean_ctor_get(v_t_71_, 1);
lean_inc(v_ca_x3f_132_);
v_kb_133_ = lean_ctor_get(v_t_71_, 2);
lean_inc(v_kb_133_);
v_cb_x3f_134_ = lean_ctor_get(v_t_71_, 3);
lean_inc(v_cb_x3f_134_);
lean_dec_ref_known(v_t_71_, 4);
v___x_135_ = lean_apply_4(v_k_72_, v_ka_131_, v_ca_x3f_132_, v_kb_133_, v_cb_x3f_134_);
return v___x_135_;
}
default: 
{
lean_object* v_c_136_; lean_object* v___x_137_; 
v_c_136_ = lean_ctor_get(v_t_71_, 0);
lean_inc_ref(v_c_136_);
lean_dec_ref(v_t_71_);
v___x_137_ = lean_apply_1(v_k_72_, v_c_136_);
return v___x_137_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim(lean_object* v_motive__2_138_, lean_object* v_ctorIdx_139_, lean_object* v_t_140_, lean_object* v_h_141_, lean_object* v_k_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_140_, v_k_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___boxed(lean_object* v_motive__2_144_, lean_object* v_ctorIdx_145_, lean_object* v_t_146_, lean_object* v_h_147_, lean_object* v_k_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim(v_motive__2_144_, v_ctorIdx_145_, v_t_146_, v_h_147_, v_k_148_);
lean_dec(v_ctorIdx_145_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core0_elim___redArg(lean_object* v_t_150_, lean_object* v_core0_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_150_, v_core0_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core0_elim(lean_object* v_motive__2_153_, lean_object* v_t_154_, lean_object* v_h_155_, lean_object* v_core0_156_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_154_, v_core0_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core_elim___redArg(lean_object* v_t_158_, lean_object* v_core_159_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_158_, v_core_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core_elim(lean_object* v_motive__2_161_, lean_object* v_t_162_, lean_object* v_h_163_, lean_object* v_core_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_162_, v_core_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_coreToInt_elim___redArg(lean_object* v_t_166_, lean_object* v_coreToInt_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_166_, v_coreToInt_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_coreToInt_elim(lean_object* v_motive__2_169_, lean_object* v_t_170_, lean_object* v_h_171_, lean_object* v_coreToInt_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_170_, v_coreToInt_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defn_elim___redArg(lean_object* v_t_174_, lean_object* v_defn_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_174_, v_defn_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defn_elim(lean_object* v_motive__2_177_, lean_object* v_t_178_, lean_object* v_h_179_, lean_object* v_defn_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_178_, v_defn_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnNat_elim___redArg(lean_object* v_t_182_, lean_object* v_defnNat_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_182_, v_defnNat_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnNat_elim(lean_object* v_motive__2_185_, lean_object* v_t_186_, lean_object* v_h_187_, lean_object* v_defnNat_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_186_, v_defnNat_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_norm_elim___redArg(lean_object* v_t_190_, lean_object* v_norm_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_190_, v_norm_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_norm_elim(lean_object* v_motive__2_193_, lean_object* v_t_194_, lean_object* v_h_195_, lean_object* v_norm_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_194_, v_norm_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_divCoeffs_elim___redArg(lean_object* v_t_198_, lean_object* v_divCoeffs_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_198_, v_divCoeffs_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_divCoeffs_elim(lean_object* v_motive__2_201_, lean_object* v_t_202_, lean_object* v_h_203_, lean_object* v_divCoeffs_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_202_, v_divCoeffs_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_subst_elim___redArg(lean_object* v_t_206_, lean_object* v_subst_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_206_, v_subst_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_subst_elim(lean_object* v_motive__2_209_, lean_object* v_t_210_, lean_object* v_h_211_, lean_object* v_subst_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_210_, v_subst_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofLeGe_elim___redArg(lean_object* v_t_214_, lean_object* v_ofLeGe_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_214_, v_ofLeGe_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofLeGe_elim(lean_object* v_motive__2_217_, lean_object* v_t_218_, lean_object* v_h_219_, lean_object* v_ofLeGe_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_218_, v_ofLeGe_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofZeroDvd_elim___redArg(lean_object* v_t_222_, lean_object* v_ofZeroDvd_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_222_, v_ofZeroDvd_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofZeroDvd_elim(lean_object* v_motive__2_225_, lean_object* v_t_226_, lean_object* v_h_227_, lean_object* v_ofZeroDvd_228_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_226_, v_ofZeroDvd_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_reorder_elim___redArg(lean_object* v_t_230_, lean_object* v_reorder_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_230_, v_reorder_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_reorder_elim(lean_object* v_motive__2_233_, lean_object* v_t_234_, lean_object* v_h_235_, lean_object* v_reorder_236_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_234_, v_reorder_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_commRingNorm_elim___redArg(lean_object* v_t_238_, lean_object* v_commRingNorm_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_238_, v_commRingNorm_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_commRingNorm_elim(lean_object* v_motive__2_241_, lean_object* v_t_242_, lean_object* v_h_243_, lean_object* v_commRingNorm_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_242_, v_commRingNorm_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnCommRing_elim___redArg(lean_object* v_t_246_, lean_object* v_defnCommRing_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_246_, v_defnCommRing_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnCommRing_elim(lean_object* v_motive__2_249_, lean_object* v_t_250_, lean_object* v_h_251_, lean_object* v_defnCommRing_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_250_, v_defnCommRing_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnNatCommRing_elim___redArg(lean_object* v_t_254_, lean_object* v_defnNatCommRing_255_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_254_, v_defnNatCommRing_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnNatCommRing_elim(lean_object* v_motive__2_257_, lean_object* v_t_258_, lean_object* v_h_259_, lean_object* v_defnNatCommRing_260_){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_258_, v_defnNatCommRing_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mul_elim___redArg(lean_object* v_t_262_, lean_object* v_mul_263_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_262_, v_mul_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mul_elim(lean_object* v_motive__2_265_, lean_object* v_t_266_, lean_object* v_h_267_, lean_object* v_mul_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_266_, v_mul_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_div_elim___redArg(lean_object* v_t_270_, lean_object* v_div_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_270_, v_div_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_div_elim(lean_object* v_motive__2_273_, lean_object* v_t_274_, lean_object* v_h_275_, lean_object* v_div_276_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_274_, v_div_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mod_elim___redArg(lean_object* v_t_278_, lean_object* v_mod_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_278_, v_mod_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mod_elim(lean_object* v_motive__2_281_, lean_object* v_t_282_, lean_object* v_h_283_, lean_object* v_mod_284_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_282_, v_mod_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_pow_elim___redArg(lean_object* v_t_286_, lean_object* v_pow_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_286_, v_pow_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_pow_elim(lean_object* v_motive__2_289_, lean_object* v_t_290_, lean_object* v_h_291_, lean_object* v_pow_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_290_, v_pow_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorIdx(lean_object* v_x_294_){
_start:
{
if (lean_obj_tag(v_x_294_) == 0)
{
lean_object* v___x_295_; 
v___x_295_ = lean_unsigned_to_nat(0u);
return v___x_295_;
}
else
{
lean_object* v___x_296_; 
v___x_296_ = lean_unsigned_to_nat(1u);
return v___x_296_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorIdx___boxed(lean_object* v_x_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorIdx(v_x_297_);
lean_dec_ref(v_x_297_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(lean_object* v_t_299_, lean_object* v_k_300_){
_start:
{
if (lean_obj_tag(v_t_299_) == 0)
{
lean_object* v_h_301_; lean_object* v___x_302_; 
v_h_301_ = lean_ctor_get(v_t_299_, 0);
lean_inc(v_h_301_);
lean_dec_ref_known(v_t_299_, 1);
v___x_302_ = lean_apply_1(v_k_300_, v_h_301_);
return v___x_302_;
}
else
{
lean_object* v_hs_303_; lean_object* v_decVars_304_; lean_object* v___x_305_; 
v_hs_303_ = lean_ctor_get(v_t_299_, 0);
lean_inc_ref(v_hs_303_);
v_decVars_304_ = lean_ctor_get(v_t_299_, 1);
lean_inc_ref(v_decVars_304_);
lean_dec_ref_known(v_t_299_, 2);
v___x_305_ = lean_apply_2(v_k_300_, v_hs_303_, v_decVars_304_);
return v___x_305_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim(lean_object* v_motive__6_306_, lean_object* v_ctorIdx_307_, lean_object* v_t_308_, lean_object* v_h_309_, lean_object* v_k_310_){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_308_, v_k_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___boxed(lean_object* v_motive__6_312_, lean_object* v_ctorIdx_313_, lean_object* v_t_314_, lean_object* v_h_315_, lean_object* v_k_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim(v_motive__6_312_, v_ctorIdx_313_, v_t_314_, v_h_315_, v_k_316_);
lean_dec(v_ctorIdx_313_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_dec_elim___redArg(lean_object* v_t_318_, lean_object* v_dec_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_318_, v_dec_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_dec_elim(lean_object* v_motive__6_321_, lean_object* v_t_322_, lean_object* v_h_323_, lean_object* v_dec_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_322_, v_dec_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_last_elim___redArg(lean_object* v_t_326_, lean_object* v_last_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_326_, v_last_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_last_elim(lean_object* v_motive__6_329_, lean_object* v_t_330_, lean_object* v_h_331_, lean_object* v_last_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_330_, v_last_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorIdx(lean_object* v_x_334_){
_start:
{
switch(lean_obj_tag(v_x_334_))
{
case 0:
{
lean_object* v___x_335_; 
v___x_335_ = lean_unsigned_to_nat(0u);
return v___x_335_;
}
case 1:
{
lean_object* v___x_336_; 
v___x_336_ = lean_unsigned_to_nat(1u);
return v___x_336_;
}
case 2:
{
lean_object* v___x_337_; 
v___x_337_ = lean_unsigned_to_nat(2u);
return v___x_337_;
}
case 3:
{
lean_object* v___x_338_; 
v___x_338_ = lean_unsigned_to_nat(3u);
return v___x_338_;
}
case 4:
{
lean_object* v___x_339_; 
v___x_339_ = lean_unsigned_to_nat(4u);
return v___x_339_;
}
case 5:
{
lean_object* v___x_340_; 
v___x_340_ = lean_unsigned_to_nat(5u);
return v___x_340_;
}
case 6:
{
lean_object* v___x_341_; 
v___x_341_ = lean_unsigned_to_nat(6u);
return v___x_341_;
}
case 7:
{
lean_object* v___x_342_; 
v___x_342_ = lean_unsigned_to_nat(7u);
return v___x_342_;
}
case 8:
{
lean_object* v___x_343_; 
v___x_343_ = lean_unsigned_to_nat(8u);
return v___x_343_;
}
case 9:
{
lean_object* v___x_344_; 
v___x_344_ = lean_unsigned_to_nat(9u);
return v___x_344_;
}
case 10:
{
lean_object* v___x_345_; 
v___x_345_ = lean_unsigned_to_nat(10u);
return v___x_345_;
}
case 11:
{
lean_object* v___x_346_; 
v___x_346_ = lean_unsigned_to_nat(11u);
return v___x_346_;
}
default: 
{
lean_object* v___x_347_; 
v___x_347_ = lean_unsigned_to_nat(12u);
return v___x_347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorIdx___boxed(lean_object* v_x_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorIdx(v_x_348_);
lean_dec_ref(v_x_348_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(lean_object* v_t_350_, lean_object* v_k_351_){
_start:
{
switch(lean_obj_tag(v_t_350_))
{
case 1:
{
lean_object* v_e_352_; lean_object* v_thm_353_; lean_object* v_d_354_; lean_object* v_a_355_; lean_object* v___x_356_; 
v_e_352_ = lean_ctor_get(v_t_350_, 0);
lean_inc_ref(v_e_352_);
v_thm_353_ = lean_ctor_get(v_t_350_, 1);
lean_inc_ref(v_thm_353_);
v_d_354_ = lean_ctor_get(v_t_350_, 2);
lean_inc(v_d_354_);
v_a_355_ = lean_ctor_get(v_t_350_, 3);
lean_inc_ref(v_a_355_);
lean_dec_ref_known(v_t_350_, 4);
v___x_356_ = lean_apply_4(v_k_351_, v_e_352_, v_thm_353_, v_d_354_, v_a_355_);
return v___x_356_;
}
case 4:
{
lean_object* v_c_u2081_357_; lean_object* v_c_u2082_358_; lean_object* v___x_359_; 
v_c_u2081_357_ = lean_ctor_get(v_t_350_, 0);
lean_inc_ref(v_c_u2081_357_);
v_c_u2082_358_ = lean_ctor_get(v_t_350_, 1);
lean_inc_ref(v_c_u2082_358_);
lean_dec_ref_known(v_t_350_, 2);
v___x_359_ = lean_apply_2(v_k_351_, v_c_u2081_357_, v_c_u2082_358_);
return v___x_359_;
}
case 5:
{
lean_object* v_c_u2081_360_; lean_object* v_c_u2082_361_; lean_object* v___x_362_; 
v_c_u2081_360_ = lean_ctor_get(v_t_350_, 0);
lean_inc_ref(v_c_u2081_360_);
v_c_u2082_361_ = lean_ctor_get(v_t_350_, 1);
lean_inc_ref(v_c_u2082_361_);
lean_dec_ref_known(v_t_350_, 2);
v___x_362_ = lean_apply_2(v_k_351_, v_c_u2081_360_, v_c_u2082_361_);
return v___x_362_;
}
case 7:
{
lean_object* v_x_363_; lean_object* v_c_364_; lean_object* v___x_365_; 
v_x_363_ = lean_ctor_get(v_t_350_, 0);
lean_inc(v_x_363_);
v_c_364_ = lean_ctor_get(v_t_350_, 1);
lean_inc_ref(v_c_364_);
lean_dec_ref_known(v_t_350_, 2);
v___x_365_ = lean_apply_2(v_k_351_, v_x_363_, v_c_364_);
return v___x_365_;
}
case 8:
{
lean_object* v_x_366_; lean_object* v_c_u2081_367_; lean_object* v_c_u2082_368_; lean_object* v___x_369_; 
v_x_366_ = lean_ctor_get(v_t_350_, 0);
lean_inc(v_x_366_);
v_c_u2081_367_ = lean_ctor_get(v_t_350_, 1);
lean_inc_ref(v_c_u2081_367_);
v_c_u2082_368_ = lean_ctor_get(v_t_350_, 2);
lean_inc_ref(v_c_u2082_368_);
lean_dec_ref_known(v_t_350_, 3);
v___x_369_ = lean_apply_3(v_k_351_, v_x_366_, v_c_u2081_367_, v_c_u2082_368_);
return v___x_369_;
}
case 12:
{
lean_object* v_c_370_; lean_object* v_e_371_; lean_object* v_p_372_; lean_object* v___x_373_; 
v_c_370_ = lean_ctor_get(v_t_350_, 0);
lean_inc_ref(v_c_370_);
v_e_371_ = lean_ctor_get(v_t_350_, 1);
lean_inc_ref(v_e_371_);
v_p_372_ = lean_ctor_get(v_t_350_, 2);
lean_inc_ref(v_p_372_);
lean_dec_ref_known(v_t_350_, 3);
v___x_373_ = lean_apply_3(v_k_351_, v_c_370_, v_e_371_, v_p_372_);
return v___x_373_;
}
default: 
{
lean_object* v_e_374_; lean_object* v___x_375_; 
v_e_374_ = lean_ctor_get(v_t_350_, 0);
lean_inc_ref(v_e_374_);
lean_dec_ref(v_t_350_);
v___x_375_ = lean_apply_1(v_k_351_, v_e_374_);
return v___x_375_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim(lean_object* v_motive__7_376_, lean_object* v_ctorIdx_377_, lean_object* v_t_378_, lean_object* v_h_379_, lean_object* v_k_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_378_, v_k_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___boxed(lean_object* v_motive__7_382_, lean_object* v_ctorIdx_383_, lean_object* v_t_384_, lean_object* v_h_385_, lean_object* v_k_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim(v_motive__7_382_, v_ctorIdx_383_, v_t_384_, v_h_385_, v_k_386_);
lean_dec(v_ctorIdx_383_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_core_elim___redArg(lean_object* v_t_388_, lean_object* v_core_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_388_, v_core_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_core_elim(lean_object* v_motive__7_391_, lean_object* v_t_392_, lean_object* v_h_393_, lean_object* v_core_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_392_, v_core_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_coreOfNat_elim___redArg(lean_object* v_t_396_, lean_object* v_coreOfNat_397_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_396_, v_coreOfNat_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_coreOfNat_elim(lean_object* v_motive__7_399_, lean_object* v_t_400_, lean_object* v_h_401_, lean_object* v_coreOfNat_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_400_, v_coreOfNat_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_norm_elim___redArg(lean_object* v_t_404_, lean_object* v_norm_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_404_, v_norm_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_norm_elim(lean_object* v_motive__7_407_, lean_object* v_t_408_, lean_object* v_h_409_, lean_object* v_norm_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_408_, v_norm_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_divCoeffs_elim___redArg(lean_object* v_t_412_, lean_object* v_divCoeffs_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_412_, v_divCoeffs_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_divCoeffs_elim(lean_object* v_motive__7_415_, lean_object* v_t_416_, lean_object* v_h_417_, lean_object* v_divCoeffs_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_416_, v_divCoeffs_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveCombine_elim___redArg(lean_object* v_t_420_, lean_object* v_solveCombine_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_420_, v_solveCombine_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveCombine_elim(lean_object* v_motive__7_423_, lean_object* v_t_424_, lean_object* v_h_425_, lean_object* v_solveCombine_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_424_, v_solveCombine_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveElim_elim___redArg(lean_object* v_t_428_, lean_object* v_solveElim_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_428_, v_solveElim_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveElim_elim(lean_object* v_motive__7_431_, lean_object* v_t_432_, lean_object* v_h_433_, lean_object* v_solveElim_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_432_, v_solveElim_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_elim_elim___redArg(lean_object* v_t_436_, lean_object* v_elim_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_436_, v_elim_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_elim_elim(lean_object* v_motive__7_439_, lean_object* v_t_440_, lean_object* v_h_441_, lean_object* v_elim_442_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_440_, v_elim_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ofEq_elim___redArg(lean_object* v_t_444_, lean_object* v_ofEq_445_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_444_, v_ofEq_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ofEq_elim(lean_object* v_motive__7_447_, lean_object* v_t_448_, lean_object* v_h_449_, lean_object* v_ofEq_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_448_, v_ofEq_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_subst_elim___redArg(lean_object* v_t_452_, lean_object* v_subst_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_452_, v_subst_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_subst_elim(lean_object* v_motive__7_455_, lean_object* v_t_456_, lean_object* v_h_457_, lean_object* v_subst_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_456_, v_subst_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2081_elim___redArg(lean_object* v_t_460_, lean_object* v_cooper_u2081_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_460_, v_cooper_u2081_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2081_elim(lean_object* v_motive__7_463_, lean_object* v_t_464_, lean_object* v_h_465_, lean_object* v_cooper_u2081_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_464_, v_cooper_u2081_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2082_elim___redArg(lean_object* v_t_468_, lean_object* v_cooper_u2082_469_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_468_, v_cooper_u2082_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2082_elim(lean_object* v_motive__7_471_, lean_object* v_t_472_, lean_object* v_h_473_, lean_object* v_cooper_u2082_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_472_, v_cooper_u2082_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_reorder_elim___redArg(lean_object* v_t_476_, lean_object* v_reorder_477_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_476_, v_reorder_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_reorder_elim(lean_object* v_motive__7_479_, lean_object* v_t_480_, lean_object* v_h_481_, lean_object* v_reorder_482_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_480_, v_reorder_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_commRingNorm_elim___redArg(lean_object* v_t_484_, lean_object* v_commRingNorm_485_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_484_, v_commRingNorm_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_commRingNorm_elim(lean_object* v_motive__7_487_, lean_object* v_t_488_, lean_object* v_h_489_, lean_object* v_commRingNorm_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_488_, v_commRingNorm_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorIdx(lean_object* v_x_492_){
_start:
{
switch(lean_obj_tag(v_x_492_))
{
case 0:
{
lean_object* v___x_493_; 
v___x_493_ = lean_unsigned_to_nat(0u);
return v___x_493_;
}
case 1:
{
lean_object* v___x_494_; 
v___x_494_ = lean_unsigned_to_nat(1u);
return v___x_494_;
}
case 2:
{
lean_object* v___x_495_; 
v___x_495_ = lean_unsigned_to_nat(2u);
return v___x_495_;
}
case 3:
{
lean_object* v___x_496_; 
v___x_496_ = lean_unsigned_to_nat(3u);
return v___x_496_;
}
case 4:
{
lean_object* v___x_497_; 
v___x_497_ = lean_unsigned_to_nat(4u);
return v___x_497_;
}
case 5:
{
lean_object* v___x_498_; 
v___x_498_ = lean_unsigned_to_nat(5u);
return v___x_498_;
}
case 6:
{
lean_object* v___x_499_; 
v___x_499_ = lean_unsigned_to_nat(6u);
return v___x_499_;
}
case 7:
{
lean_object* v___x_500_; 
v___x_500_ = lean_unsigned_to_nat(7u);
return v___x_500_;
}
case 8:
{
lean_object* v___x_501_; 
v___x_501_ = lean_unsigned_to_nat(8u);
return v___x_501_;
}
case 9:
{
lean_object* v___x_502_; 
v___x_502_ = lean_unsigned_to_nat(9u);
return v___x_502_;
}
case 10:
{
lean_object* v___x_503_; 
v___x_503_ = lean_unsigned_to_nat(10u);
return v___x_503_;
}
case 11:
{
lean_object* v___x_504_; 
v___x_504_ = lean_unsigned_to_nat(11u);
return v___x_504_;
}
case 12:
{
lean_object* v___x_505_; 
v___x_505_ = lean_unsigned_to_nat(12u);
return v___x_505_;
}
case 13:
{
lean_object* v___x_506_; 
v___x_506_ = lean_unsigned_to_nat(13u);
return v___x_506_;
}
case 14:
{
lean_object* v___x_507_; 
v___x_507_ = lean_unsigned_to_nat(14u);
return v___x_507_;
}
case 15:
{
lean_object* v___x_508_; 
v___x_508_ = lean_unsigned_to_nat(15u);
return v___x_508_;
}
case 16:
{
lean_object* v___x_509_; 
v___x_509_ = lean_unsigned_to_nat(16u);
return v___x_509_;
}
default: 
{
lean_object* v___x_510_; 
v___x_510_ = lean_unsigned_to_nat(17u);
return v___x_510_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorIdx___boxed(lean_object* v_x_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorIdx(v_x_511_);
lean_dec_ref(v_x_511_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(lean_object* v_t_513_, lean_object* v_k_514_){
_start:
{
switch(lean_obj_tag(v_t_513_))
{
case 1:
{
lean_object* v_e_515_; lean_object* v_p_516_; lean_object* v___x_517_; 
v_e_515_ = lean_ctor_get(v_t_513_, 0);
lean_inc_ref(v_e_515_);
v_p_516_ = lean_ctor_get(v_t_513_, 1);
lean_inc_ref(v_p_516_);
lean_dec_ref_known(v_t_513_, 2);
v___x_517_ = lean_apply_2(v_k_514_, v_e_515_, v_p_516_);
return v___x_517_;
}
case 2:
{
lean_object* v_e_518_; uint8_t v_pos_519_; lean_object* v_toIntThm_520_; lean_object* v_lhs_521_; lean_object* v_rhs_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v_e_518_ = lean_ctor_get(v_t_513_, 0);
lean_inc_ref(v_e_518_);
v_pos_519_ = lean_ctor_get_uint8(v_t_513_, sizeof(void*)*4);
v_toIntThm_520_ = lean_ctor_get(v_t_513_, 1);
lean_inc_ref(v_toIntThm_520_);
v_lhs_521_ = lean_ctor_get(v_t_513_, 2);
lean_inc_ref(v_lhs_521_);
v_rhs_522_ = lean_ctor_get(v_t_513_, 3);
lean_inc_ref(v_rhs_522_);
lean_dec_ref_known(v_t_513_, 4);
v___x_523_ = lean_box(v_pos_519_);
v___x_524_ = lean_apply_5(v_k_514_, v_e_518_, v___x_523_, v_toIntThm_520_, v_lhs_521_, v_rhs_522_);
return v___x_524_;
}
case 5:
{
lean_object* v_h_525_; lean_object* v___x_526_; 
v_h_525_ = lean_ctor_get(v_t_513_, 0);
lean_inc(v_h_525_);
lean_dec_ref_known(v_t_513_, 1);
v___x_526_ = lean_apply_1(v_k_514_, v_h_525_);
return v___x_526_;
}
case 8:
{
lean_object* v_c_u2081_527_; lean_object* v_c_u2082_528_; lean_object* v___x_529_; 
v_c_u2081_527_ = lean_ctor_get(v_t_513_, 0);
lean_inc_ref(v_c_u2081_527_);
v_c_u2082_528_ = lean_ctor_get(v_t_513_, 1);
lean_inc_ref(v_c_u2082_528_);
lean_dec_ref_known(v_t_513_, 2);
v___x_529_ = lean_apply_2(v_k_514_, v_c_u2081_527_, v_c_u2082_528_);
return v___x_529_;
}
case 9:
{
lean_object* v_c_u2081_530_; lean_object* v_c_u2082_531_; lean_object* v_k_532_; lean_object* v___x_533_; 
v_c_u2081_530_ = lean_ctor_get(v_t_513_, 0);
lean_inc_ref(v_c_u2081_530_);
v_c_u2082_531_ = lean_ctor_get(v_t_513_, 1);
lean_inc_ref(v_c_u2082_531_);
v_k_532_ = lean_ctor_get(v_t_513_, 2);
lean_inc(v_k_532_);
lean_dec_ref_known(v_t_513_, 3);
v___x_533_ = lean_apply_3(v_k_514_, v_c_u2081_530_, v_c_u2082_531_, v_k_532_);
return v___x_533_;
}
case 10:
{
lean_object* v_x_534_; lean_object* v_c_u2081_535_; lean_object* v_c_u2082_536_; lean_object* v___x_537_; 
v_x_534_ = lean_ctor_get(v_t_513_, 0);
lean_inc(v_x_534_);
v_c_u2081_535_ = lean_ctor_get(v_t_513_, 1);
lean_inc_ref(v_c_u2081_535_);
v_c_u2082_536_ = lean_ctor_get(v_t_513_, 2);
lean_inc_ref(v_c_u2082_536_);
lean_dec_ref_known(v_t_513_, 3);
v___x_537_ = lean_apply_3(v_k_514_, v_x_534_, v_c_u2081_535_, v_c_u2082_536_);
return v___x_537_;
}
case 11:
{
lean_object* v_c_u2081_538_; lean_object* v_c_u2082_539_; lean_object* v___x_540_; 
v_c_u2081_538_ = lean_ctor_get(v_t_513_, 0);
lean_inc_ref(v_c_u2081_538_);
v_c_u2082_539_ = lean_ctor_get(v_t_513_, 1);
lean_inc_ref(v_c_u2082_539_);
lean_dec_ref_known(v_t_513_, 2);
v___x_540_ = lean_apply_2(v_k_514_, v_c_u2081_538_, v_c_u2082_539_);
return v___x_540_;
}
case 12:
{
lean_object* v_c_u2081_541_; lean_object* v_decVar_542_; lean_object* v_h_543_; lean_object* v_decVars_544_; lean_object* v___x_545_; 
v_c_u2081_541_ = lean_ctor_get(v_t_513_, 0);
lean_inc_ref(v_c_u2081_541_);
v_decVar_542_ = lean_ctor_get(v_t_513_, 1);
lean_inc(v_decVar_542_);
v_h_543_ = lean_ctor_get(v_t_513_, 2);
lean_inc_ref(v_h_543_);
v_decVars_544_ = lean_ctor_get(v_t_513_, 3);
lean_inc_ref(v_decVars_544_);
lean_dec_ref_known(v_t_513_, 4);
v___x_545_ = lean_apply_4(v_k_514_, v_c_u2081_541_, v_decVar_542_, v_h_543_, v_decVars_544_);
return v___x_545_;
}
case 14:
{
lean_object* v_c_u2081_546_; lean_object* v_c_u2082_547_; lean_object* v___x_548_; 
v_c_u2081_546_ = lean_ctor_get(v_t_513_, 0);
lean_inc_ref(v_c_u2081_546_);
v_c_u2082_547_ = lean_ctor_get(v_t_513_, 1);
lean_inc_ref(v_c_u2082_547_);
lean_dec_ref_known(v_t_513_, 2);
v___x_548_ = lean_apply_2(v_k_514_, v_c_u2081_546_, v_c_u2082_547_);
return v___x_548_;
}
case 15:
{
lean_object* v_c_u2081_549_; lean_object* v_c_u2082_550_; lean_object* v___x_551_; 
v_c_u2081_549_ = lean_ctor_get(v_t_513_, 0);
lean_inc_ref(v_c_u2081_549_);
v_c_u2082_550_ = lean_ctor_get(v_t_513_, 1);
lean_inc_ref(v_c_u2082_550_);
lean_dec_ref_known(v_t_513_, 2);
v___x_551_ = lean_apply_2(v_k_514_, v_c_u2081_549_, v_c_u2082_550_);
return v___x_551_;
}
case 17:
{
lean_object* v_c_552_; lean_object* v_e_553_; lean_object* v_p_554_; lean_object* v___x_555_; 
v_c_552_ = lean_ctor_get(v_t_513_, 0);
lean_inc_ref(v_c_552_);
v_e_553_ = lean_ctor_get(v_t_513_, 1);
lean_inc_ref(v_e_553_);
v_p_554_ = lean_ctor_get(v_t_513_, 2);
lean_inc_ref(v_p_554_);
lean_dec_ref_known(v_t_513_, 3);
v___x_555_ = lean_apply_3(v_k_514_, v_c_552_, v_e_553_, v_p_554_);
return v___x_555_;
}
default: 
{
lean_object* v_e_556_; lean_object* v___x_557_; 
v_e_556_ = lean_ctor_get(v_t_513_, 0);
lean_inc_ref(v_e_556_);
lean_dec_ref(v_t_513_);
v___x_557_ = lean_apply_1(v_k_514_, v_e_556_);
return v___x_557_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim(lean_object* v_motive__9_558_, lean_object* v_ctorIdx_559_, lean_object* v_t_560_, lean_object* v_h_561_, lean_object* v_k_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_560_, v_k_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___boxed(lean_object* v_motive__9_564_, lean_object* v_ctorIdx_565_, lean_object* v_t_566_, lean_object* v_h_567_, lean_object* v_k_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim(v_motive__9_564_, v_ctorIdx_565_, v_t_566_, v_h_567_, v_k_568_);
lean_dec(v_ctorIdx_565_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_core_elim___redArg(lean_object* v_t_570_, lean_object* v_core_571_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_570_, v_core_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_core_elim(lean_object* v_motive__9_573_, lean_object* v_t_574_, lean_object* v_h_575_, lean_object* v_core_576_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_574_, v_core_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreNeg_elim___redArg(lean_object* v_t_578_, lean_object* v_coreNeg_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_578_, v_coreNeg_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreNeg_elim(lean_object* v_motive__9_581_, lean_object* v_t_582_, lean_object* v_h_583_, lean_object* v_coreNeg_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_582_, v_coreNeg_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreToInt_elim___redArg(lean_object* v_t_586_, lean_object* v_coreToInt_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_586_, v_coreToInt_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreToInt_elim(lean_object* v_motive__9_589_, lean_object* v_t_590_, lean_object* v_h_591_, lean_object* v_coreToInt_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_590_, v_coreToInt_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofNatNonneg_elim___redArg(lean_object* v_t_594_, lean_object* v_ofNatNonneg_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_594_, v_ofNatNonneg_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofNatNonneg_elim(lean_object* v_motive__9_597_, lean_object* v_t_598_, lean_object* v_h_599_, lean_object* v_ofNatNonneg_600_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_598_, v_ofNatNonneg_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_bound_elim___redArg(lean_object* v_t_602_, lean_object* v_bound_603_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_602_, v_bound_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_bound_elim(lean_object* v_motive__9_605_, lean_object* v_t_606_, lean_object* v_h_607_, lean_object* v_bound_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_606_, v_bound_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dec_elim___redArg(lean_object* v_t_610_, lean_object* v_dec_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_610_, v_dec_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dec_elim(lean_object* v_motive__9_613_, lean_object* v_t_614_, lean_object* v_h_615_, lean_object* v_dec_616_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_614_, v_dec_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_norm_elim___redArg(lean_object* v_t_618_, lean_object* v_norm_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_618_, v_norm_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_norm_elim(lean_object* v_motive__9_621_, lean_object* v_t_622_, lean_object* v_h_623_, lean_object* v_norm_624_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_622_, v_norm_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_divCoeffs_elim___redArg(lean_object* v_t_626_, lean_object* v_divCoeffs_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_626_, v_divCoeffs_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_divCoeffs_elim(lean_object* v_motive__9_629_, lean_object* v_t_630_, lean_object* v_h_631_, lean_object* v_divCoeffs_632_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_630_, v_divCoeffs_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combine_elim___redArg(lean_object* v_t_634_, lean_object* v_combine_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_634_, v_combine_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combine_elim(lean_object* v_motive__9_637_, lean_object* v_t_638_, lean_object* v_h_639_, lean_object* v_combine_640_){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_638_, v_combine_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combineDivCoeffs_elim___redArg(lean_object* v_t_642_, lean_object* v_combineDivCoeffs_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_642_, v_combineDivCoeffs_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combineDivCoeffs_elim(lean_object* v_motive__9_645_, lean_object* v_t_646_, lean_object* v_h_647_, lean_object* v_combineDivCoeffs_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_646_, v_combineDivCoeffs_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_subst_elim___redArg(lean_object* v_t_650_, lean_object* v_subst_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_650_, v_subst_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_subst_elim(lean_object* v_motive__9_653_, lean_object* v_t_654_, lean_object* v_h_655_, lean_object* v_subst_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_654_, v_subst_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofLeDiseq_elim___redArg(lean_object* v_t_658_, lean_object* v_ofLeDiseq_659_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_658_, v_ofLeDiseq_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofLeDiseq_elim(lean_object* v_motive__9_661_, lean_object* v_t_662_, lean_object* v_h_663_, lean_object* v_ofLeDiseq_664_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_662_, v_ofLeDiseq_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofDiseqSplit_elim___redArg(lean_object* v_t_666_, lean_object* v_ofDiseqSplit_667_){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_666_, v_ofDiseqSplit_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofDiseqSplit_elim(lean_object* v_motive__9_669_, lean_object* v_t_670_, lean_object* v_h_671_, lean_object* v_ofDiseqSplit_672_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_670_, v_ofDiseqSplit_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_cooper_elim___redArg(lean_object* v_t_674_, lean_object* v_cooper_675_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_674_, v_cooper_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_cooper_elim(lean_object* v_motive__9_677_, lean_object* v_t_678_, lean_object* v_h_679_, lean_object* v_cooper_680_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_678_, v_cooper_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dvdTight_elim___redArg(lean_object* v_t_682_, lean_object* v_dvdTight_683_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_682_, v_dvdTight_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dvdTight_elim(lean_object* v_motive__9_685_, lean_object* v_t_686_, lean_object* v_h_687_, lean_object* v_dvdTight_688_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_686_, v_dvdTight_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_negDvdTight_elim___redArg(lean_object* v_t_690_, lean_object* v_negDvdTight_691_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_690_, v_negDvdTight_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_negDvdTight_elim(lean_object* v_motive__9_693_, lean_object* v_t_694_, lean_object* v_h_695_, lean_object* v_negDvdTight_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_694_, v_negDvdTight_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_reorder_elim___redArg(lean_object* v_t_698_, lean_object* v_reorder_699_){
_start:
{
lean_object* v___x_700_; 
v___x_700_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_698_, v_reorder_699_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_reorder_elim(lean_object* v_motive__9_701_, lean_object* v_t_702_, lean_object* v_h_703_, lean_object* v_reorder_704_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_702_, v_reorder_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_commRingNorm_elim___redArg(lean_object* v_t_706_, lean_object* v_commRingNorm_707_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_706_, v_commRingNorm_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_commRingNorm_elim(lean_object* v_motive__9_709_, lean_object* v_t_710_, lean_object* v_h_711_, lean_object* v_commRingNorm_712_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_710_, v_commRingNorm_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorIdx(lean_object* v_x_714_){
_start:
{
switch(lean_obj_tag(v_x_714_))
{
case 0:
{
lean_object* v___x_715_; 
v___x_715_ = lean_unsigned_to_nat(0u);
return v___x_715_;
}
case 1:
{
lean_object* v___x_716_; 
v___x_716_ = lean_unsigned_to_nat(1u);
return v___x_716_;
}
case 2:
{
lean_object* v___x_717_; 
v___x_717_ = lean_unsigned_to_nat(2u);
return v___x_717_;
}
case 3:
{
lean_object* v___x_718_; 
v___x_718_ = lean_unsigned_to_nat(3u);
return v___x_718_;
}
case 4:
{
lean_object* v___x_719_; 
v___x_719_ = lean_unsigned_to_nat(4u);
return v___x_719_;
}
case 5:
{
lean_object* v___x_720_; 
v___x_720_ = lean_unsigned_to_nat(5u);
return v___x_720_;
}
case 6:
{
lean_object* v___x_721_; 
v___x_721_ = lean_unsigned_to_nat(6u);
return v___x_721_;
}
case 7:
{
lean_object* v___x_722_; 
v___x_722_ = lean_unsigned_to_nat(7u);
return v___x_722_;
}
default: 
{
lean_object* v___x_723_; 
v___x_723_ = lean_unsigned_to_nat(8u);
return v___x_723_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorIdx___boxed(lean_object* v_x_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorIdx(v_x_724_);
lean_dec_ref(v_x_724_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(lean_object* v_t_726_, lean_object* v_k_727_){
_start:
{
switch(lean_obj_tag(v_t_726_))
{
case 0:
{
lean_object* v_a_728_; lean_object* v_zero_729_; lean_object* v___x_730_; 
v_a_728_ = lean_ctor_get(v_t_726_, 0);
lean_inc_ref(v_a_728_);
v_zero_729_ = lean_ctor_get(v_t_726_, 1);
lean_inc_ref(v_zero_729_);
lean_dec_ref_known(v_t_726_, 2);
v___x_730_ = lean_apply_2(v_k_727_, v_a_728_, v_zero_729_);
return v___x_730_;
}
case 1:
{
lean_object* v_a_731_; lean_object* v_b_732_; lean_object* v_p_u2081_733_; lean_object* v_p_u2082_734_; lean_object* v___x_735_; 
v_a_731_ = lean_ctor_get(v_t_726_, 0);
lean_inc_ref(v_a_731_);
v_b_732_ = lean_ctor_get(v_t_726_, 1);
lean_inc_ref(v_b_732_);
v_p_u2081_733_ = lean_ctor_get(v_t_726_, 2);
lean_inc_ref(v_p_u2081_733_);
v_p_u2082_734_ = lean_ctor_get(v_t_726_, 3);
lean_inc_ref(v_p_u2082_734_);
lean_dec_ref_known(v_t_726_, 4);
v___x_735_ = lean_apply_4(v_k_727_, v_a_731_, v_b_732_, v_p_u2081_733_, v_p_u2082_734_);
return v___x_735_;
}
case 2:
{
lean_object* v_a_736_; lean_object* v_b_737_; lean_object* v_toIntThm_738_; lean_object* v_lhs_739_; lean_object* v_rhs_740_; lean_object* v___x_741_; 
v_a_736_ = lean_ctor_get(v_t_726_, 0);
lean_inc_ref(v_a_736_);
v_b_737_ = lean_ctor_get(v_t_726_, 1);
lean_inc_ref(v_b_737_);
v_toIntThm_738_ = lean_ctor_get(v_t_726_, 2);
lean_inc_ref(v_toIntThm_738_);
v_lhs_739_ = lean_ctor_get(v_t_726_, 3);
lean_inc_ref(v_lhs_739_);
v_rhs_740_ = lean_ctor_get(v_t_726_, 4);
lean_inc_ref(v_rhs_740_);
lean_dec_ref_known(v_t_726_, 5);
v___x_741_ = lean_apply_5(v_k_727_, v_a_736_, v_b_737_, v_toIntThm_738_, v_lhs_739_, v_rhs_740_);
return v___x_741_;
}
case 6:
{
lean_object* v_x_742_; lean_object* v_c_u2081_743_; lean_object* v_c_u2082_744_; lean_object* v___x_745_; 
v_x_742_ = lean_ctor_get(v_t_726_, 0);
lean_inc(v_x_742_);
v_c_u2081_743_ = lean_ctor_get(v_t_726_, 1);
lean_inc_ref(v_c_u2081_743_);
v_c_u2082_744_ = lean_ctor_get(v_t_726_, 2);
lean_inc_ref(v_c_u2082_744_);
lean_dec_ref_known(v_t_726_, 3);
v___x_745_ = lean_apply_3(v_k_727_, v_x_742_, v_c_u2081_743_, v_c_u2082_744_);
return v___x_745_;
}
case 8:
{
lean_object* v_c_746_; lean_object* v_e_747_; lean_object* v_p_748_; lean_object* v___x_749_; 
v_c_746_ = lean_ctor_get(v_t_726_, 0);
lean_inc_ref(v_c_746_);
v_e_747_ = lean_ctor_get(v_t_726_, 1);
lean_inc_ref(v_e_747_);
v_p_748_ = lean_ctor_get(v_t_726_, 2);
lean_inc_ref(v_p_748_);
lean_dec_ref_known(v_t_726_, 3);
v___x_749_ = lean_apply_3(v_k_727_, v_c_746_, v_e_747_, v_p_748_);
return v___x_749_;
}
default: 
{
lean_object* v_c_750_; lean_object* v___x_751_; 
v_c_750_ = lean_ctor_get(v_t_726_, 0);
lean_inc_ref(v_c_750_);
lean_dec_ref(v_t_726_);
v___x_751_ = lean_apply_1(v_k_727_, v_c_750_);
return v___x_751_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim(lean_object* v_motive__11_752_, lean_object* v_ctorIdx_753_, lean_object* v_t_754_, lean_object* v_h_755_, lean_object* v_k_756_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_754_, v_k_756_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___boxed(lean_object* v_motive__11_758_, lean_object* v_ctorIdx_759_, lean_object* v_t_760_, lean_object* v_h_761_, lean_object* v_k_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim(v_motive__11_758_, v_ctorIdx_759_, v_t_760_, v_h_761_, v_k_762_);
lean_dec(v_ctorIdx_759_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core0_elim___redArg(lean_object* v_t_764_, lean_object* v_core0_765_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_764_, v_core0_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core0_elim(lean_object* v_motive__11_767_, lean_object* v_t_768_, lean_object* v_h_769_, lean_object* v_core0_770_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_768_, v_core0_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core_elim___redArg(lean_object* v_t_772_, lean_object* v_core_773_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_772_, v_core_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core_elim(lean_object* v_motive__11_775_, lean_object* v_t_776_, lean_object* v_h_777_, lean_object* v_core_778_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_776_, v_core_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_coreToInt_elim___redArg(lean_object* v_t_780_, lean_object* v_coreToInt_781_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_780_, v_coreToInt_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_coreToInt_elim(lean_object* v_motive__11_783_, lean_object* v_t_784_, lean_object* v_h_785_, lean_object* v_coreToInt_786_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_784_, v_coreToInt_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_norm_elim___redArg(lean_object* v_t_788_, lean_object* v_norm_789_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_788_, v_norm_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_norm_elim(lean_object* v_motive__11_791_, lean_object* v_t_792_, lean_object* v_h_793_, lean_object* v_norm_794_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_792_, v_norm_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_divCoeffs_elim___redArg(lean_object* v_t_796_, lean_object* v_divCoeffs_797_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_796_, v_divCoeffs_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_divCoeffs_elim(lean_object* v_motive__11_799_, lean_object* v_t_800_, lean_object* v_h_801_, lean_object* v_divCoeffs_802_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_800_, v_divCoeffs_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_neg_elim___redArg(lean_object* v_t_804_, lean_object* v_neg_805_){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_804_, v_neg_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_neg_elim(lean_object* v_motive__11_807_, lean_object* v_t_808_, lean_object* v_h_809_, lean_object* v_neg_810_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_808_, v_neg_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_subst_elim___redArg(lean_object* v_t_812_, lean_object* v_subst_813_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_812_, v_subst_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_subst_elim(lean_object* v_motive__11_815_, lean_object* v_t_816_, lean_object* v_h_817_, lean_object* v_subst_818_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_816_, v_subst_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_reorder_elim___redArg(lean_object* v_t_820_, lean_object* v_reorder_821_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_820_, v_reorder_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_reorder_elim(lean_object* v_motive__11_823_, lean_object* v_t_824_, lean_object* v_h_825_, lean_object* v_reorder_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_824_, v_reorder_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_commRingNorm_elim___redArg(lean_object* v_t_828_, lean_object* v_commRingNorm_829_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_828_, v_commRingNorm_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_commRingNorm_elim(lean_object* v_motive__11_831_, lean_object* v_t_832_, lean_object* v_h_833_, lean_object* v_commRingNorm_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_832_, v_commRingNorm_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorIdx(lean_object* v_x_836_){
_start:
{
switch(lean_obj_tag(v_x_836_))
{
case 0:
{
lean_object* v___x_837_; 
v___x_837_ = lean_unsigned_to_nat(0u);
return v___x_837_;
}
case 1:
{
lean_object* v___x_838_; 
v___x_838_ = lean_unsigned_to_nat(1u);
return v___x_838_;
}
case 2:
{
lean_object* v___x_839_; 
v___x_839_ = lean_unsigned_to_nat(2u);
return v___x_839_;
}
case 3:
{
lean_object* v___x_840_; 
v___x_840_ = lean_unsigned_to_nat(3u);
return v___x_840_;
}
default: 
{
lean_object* v___x_841_; 
v___x_841_ = lean_unsigned_to_nat(4u);
return v___x_841_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorIdx___boxed(lean_object* v_x_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorIdx(v_x_842_);
lean_dec_ref(v_x_842_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(lean_object* v_t_844_, lean_object* v_k_845_){
_start:
{
if (lean_obj_tag(v_t_844_) == 4)
{
lean_object* v_c_u2081_846_; lean_object* v_c_u2082_847_; lean_object* v_c_u2083_848_; lean_object* v___x_849_; 
v_c_u2081_846_ = lean_ctor_get(v_t_844_, 0);
lean_inc_ref(v_c_u2081_846_);
v_c_u2082_847_ = lean_ctor_get(v_t_844_, 1);
lean_inc_ref(v_c_u2082_847_);
v_c_u2083_848_ = lean_ctor_get(v_t_844_, 2);
lean_inc_ref(v_c_u2083_848_);
lean_dec_ref_known(v_t_844_, 3);
v___x_849_ = lean_apply_3(v_k_845_, v_c_u2081_846_, v_c_u2082_847_, v_c_u2083_848_);
return v___x_849_;
}
else
{
lean_object* v_c_850_; lean_object* v___x_851_; 
v_c_850_ = lean_ctor_get(v_t_844_, 0);
lean_inc_ref(v_c_850_);
lean_dec_ref(v_t_844_);
v___x_851_ = lean_apply_1(v_k_845_, v_c_850_);
return v___x_851_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim(lean_object* v_motive__12_852_, lean_object* v_ctorIdx_853_, lean_object* v_t_854_, lean_object* v_h_855_, lean_object* v_k_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_854_, v_k_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___boxed(lean_object* v_motive__12_858_, lean_object* v_ctorIdx_859_, lean_object* v_t_860_, lean_object* v_h_861_, lean_object* v_k_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim(v_motive__12_858_, v_ctorIdx_859_, v_t_860_, v_h_861_, v_k_862_);
lean_dec(v_ctorIdx_859_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_dvd_elim___redArg(lean_object* v_t_864_, lean_object* v_dvd_865_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_864_, v_dvd_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_dvd_elim(lean_object* v_motive__12_867_, lean_object* v_t_868_, lean_object* v_h_869_, lean_object* v_dvd_870_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_868_, v_dvd_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_le_elim___redArg(lean_object* v_t_872_, lean_object* v_le_873_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_872_, v_le_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_le_elim(lean_object* v_motive__12_875_, lean_object* v_t_876_, lean_object* v_h_877_, lean_object* v_le_878_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_876_, v_le_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_eq_elim___redArg(lean_object* v_t_880_, lean_object* v_eq_881_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_880_, v_eq_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_eq_elim(lean_object* v_motive__12_883_, lean_object* v_t_884_, lean_object* v_h_885_, lean_object* v_eq_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_884_, v_eq_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_diseq_elim___redArg(lean_object* v_t_888_, lean_object* v_diseq_889_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_888_, v_diseq_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_diseq_elim(lean_object* v_motive__12_891_, lean_object* v_t_892_, lean_object* v_h_893_, lean_object* v_diseq_894_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_892_, v_diseq_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_cooper_elim___redArg(lean_object* v_t_896_, lean_object* v_cooper_897_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_896_, v_cooper_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_cooper_elim(lean_object* v_motive__12_899_, lean_object* v_t_900_, lean_object* v_h_901_, lean_object* v_cooper_902_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_900_, v_cooper_902_);
return v___x_903_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0);
v___x_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
return v___x_905_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3(void){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_909_ = lean_box(0);
v___x_910_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__2));
v___x_911_ = l_Lean_Expr_const___override(v___x_910_, v___x_909_);
return v___x_911_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4(void){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3);
v___x_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
return v___x_913_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5(void){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_914_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4);
v___x_915_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0);
v___x_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
lean_ctor_set(v___x_916_, 1, v___x_914_);
return v___x_916_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr(void){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5);
return v___x_917_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0(void){
_start:
{
lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_918_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3);
v___x_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_919_, 0, v___x_918_);
return v___x_919_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1(void){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_920_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0);
v___x_921_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0);
v___x_922_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0);
v___x_923_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
lean_ctor_set(v___x_923_, 1, v___x_921_);
lean_ctor_set(v___x_923_, 2, v___x_920_);
return v___x_923_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr(void){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1);
return v___x_924_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0(void){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; uint8_t v___x_927_; lean_object* v___x_928_; 
v___x_925_ = lean_box(0);
v___x_926_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5);
v___x_927_ = 0;
v___x_928_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_928_, 0, v___x_926_);
lean_ctor_set(v___x_928_, 1, v___x_926_);
lean_ctor_set(v___x_928_, 2, v___x_925_);
lean_ctor_set_uint8(v___x_928_, sizeof(void*)*3, v___x_927_);
return v___x_928_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred(void){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0);
return v___x_929_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1(void){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_932_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__0));
v___x_933_ = lean_unsigned_to_nat(0u);
v___x_934_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0);
v___x_935_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
lean_ctor_set(v___x_935_, 1, v___x_933_);
lean_ctor_set(v___x_935_, 2, v___x_932_);
return v___x_935_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit(void){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1);
return v___x_936_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_937_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__1(void){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_938_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0);
v___x_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0(lean_object* v_00_u03b2_940_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__1);
return v___x_941_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0(void){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_942_ = lean_unsigned_to_nat(32u);
v___x_943_ = lean_mk_empty_array_with_capacity(v___x_942_);
v___x_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
return v___x_944_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1(void){
_start:
{
size_t v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_945_ = ((size_t)5ULL);
v___x_946_ = lean_unsigned_to_nat(0u);
v___x_947_ = lean_unsigned_to_nat(32u);
v___x_948_ = lean_mk_empty_array_with_capacity(v___x_947_);
v___x_949_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0);
v___x_950_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_950_, 0, v___x_949_);
lean_ctor_set(v___x_950_, 1, v___x_948_);
lean_ctor_set(v___x_950_, 2, v___x_946_);
lean_ctor_set(v___x_950_, 3, v___x_946_);
lean_ctor_set_usize(v___x_950_, 4, v___x_945_);
return v___x_950_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2(void){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_951_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3(void){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2);
v___x_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
return v___x_953_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__4(void){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0(lean_box(0));
return v___x_954_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5(void){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; uint8_t v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_955_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__4);
v___x_956_ = lean_box(0);
v___x_957_ = 0;
v___x_958_ = lean_unsigned_to_nat(0u);
v___x_959_ = lean_box(0);
v___x_960_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3);
v___x_961_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1);
v___x_962_ = lean_alloc_ctor(0, 24, 2);
lean_ctor_set(v___x_962_, 0, v___x_961_);
lean_ctor_set(v___x_962_, 1, v___x_960_);
lean_ctor_set(v___x_962_, 2, v___x_961_);
lean_ctor_set(v___x_962_, 3, v___x_960_);
lean_ctor_set(v___x_962_, 4, v___x_960_);
lean_ctor_set(v___x_962_, 5, v___x_960_);
lean_ctor_set(v___x_962_, 6, v___x_961_);
lean_ctor_set(v___x_962_, 7, v___x_961_);
lean_ctor_set(v___x_962_, 8, v___x_961_);
lean_ctor_set(v___x_962_, 9, v___x_961_);
lean_ctor_set(v___x_962_, 10, v___x_961_);
lean_ctor_set(v___x_962_, 11, v___x_959_);
lean_ctor_set(v___x_962_, 12, v___x_961_);
lean_ctor_set(v___x_962_, 13, v___x_961_);
lean_ctor_set(v___x_962_, 14, v___x_958_);
lean_ctor_set(v___x_962_, 15, v___x_958_);
lean_ctor_set(v___x_962_, 16, v___x_956_);
lean_ctor_set(v___x_962_, 17, v___x_960_);
lean_ctor_set(v___x_962_, 18, v___x_955_);
lean_ctor_set(v___x_962_, 19, v___x_960_);
lean_ctor_set(v___x_962_, 20, v___x_961_);
lean_ctor_set(v___x_962_, 21, v___x_960_);
lean_ctor_set(v___x_962_, 22, v___x_960_);
lean_ctor_set(v___x_962_, 23, v___x_960_);
lean_ctor_set_uint8(v___x_962_, sizeof(void*)*24, v___x_957_);
lean_ctor_set_uint8(v___x_962_, sizeof(void*)*24 + 1, v___x_957_);
return v___x_962_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default(void){
_start:
{
lean_object* v___x_963_; 
v___x_963_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5);
return v___x_963_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState(void){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default;
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(lean_object* v___x_965_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_967_, 0, v___x_965_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2____boxed(lean_object* v___x_968_, lean_object* v___y_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(v___x_968_);
return v_res_970_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_971_; lean_object* v___f_972_; 
v___x_971_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5);
v___f_972_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_972_, 0, v___x_971_);
return v___f_972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_974_; lean_object* v___x_975_; 
v___f_974_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_);
v___x_975_ = l_Lean_Meta_Grind_registerSolverExtension___redArg(v___f_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2____boxed(lean_object* v_a_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_();
return v_res_977_;
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
