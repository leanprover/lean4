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
default: 
{
lean_object* v___x_67_; 
v___x_67_ = lean_unsigned_to_nat(16u);
return v___x_67_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorIdx___boxed(lean_object* v_x_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorIdx(v_x_68_);
lean_dec_ref(v_x_68_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(lean_object* v_t_70_, lean_object* v_k_71_){
_start:
{
switch(lean_obj_tag(v_t_70_))
{
case 1:
{
lean_object* v_a_72_; lean_object* v_b_73_; lean_object* v_p_u2081_74_; lean_object* v_p_u2082_75_; lean_object* v___x_76_; 
v_a_72_ = lean_ctor_get(v_t_70_, 0);
lean_inc_ref(v_a_72_);
v_b_73_ = lean_ctor_get(v_t_70_, 1);
lean_inc_ref(v_b_73_);
v_p_u2081_74_ = lean_ctor_get(v_t_70_, 2);
lean_inc_ref(v_p_u2081_74_);
v_p_u2082_75_ = lean_ctor_get(v_t_70_, 3);
lean_inc_ref(v_p_u2082_75_);
lean_dec_ref(v_t_70_);
v___x_76_ = lean_apply_4(v_k_71_, v_a_72_, v_b_73_, v_p_u2081_74_, v_p_u2082_75_);
return v___x_76_;
}
case 2:
{
lean_object* v_a_77_; lean_object* v_b_78_; lean_object* v_toIntThm_79_; lean_object* v_lhs_80_; lean_object* v_rhs_81_; lean_object* v___x_82_; 
v_a_77_ = lean_ctor_get(v_t_70_, 0);
lean_inc_ref(v_a_77_);
v_b_78_ = lean_ctor_get(v_t_70_, 1);
lean_inc_ref(v_b_78_);
v_toIntThm_79_ = lean_ctor_get(v_t_70_, 2);
lean_inc_ref(v_toIntThm_79_);
v_lhs_80_ = lean_ctor_get(v_t_70_, 3);
lean_inc_ref(v_lhs_80_);
v_rhs_81_ = lean_ctor_get(v_t_70_, 4);
lean_inc_ref(v_rhs_81_);
lean_dec_ref(v_t_70_);
v___x_82_ = lean_apply_5(v_k_71_, v_a_77_, v_b_78_, v_toIntThm_79_, v_lhs_80_, v_rhs_81_);
return v___x_82_;
}
case 4:
{
lean_object* v_h_83_; lean_object* v_x_84_; lean_object* v_e_x27_85_; lean_object* v___x_86_; 
v_h_83_ = lean_ctor_get(v_t_70_, 0);
lean_inc_ref(v_h_83_);
v_x_84_ = lean_ctor_get(v_t_70_, 1);
lean_inc(v_x_84_);
v_e_x27_85_ = lean_ctor_get(v_t_70_, 2);
lean_inc_ref(v_e_x27_85_);
lean_dec_ref(v_t_70_);
v___x_86_ = lean_apply_3(v_k_71_, v_h_83_, v_x_84_, v_e_x27_85_);
return v___x_86_;
}
case 5:
{
lean_object* v_c_87_; lean_object* v___x_88_; 
v_c_87_ = lean_ctor_get(v_t_70_, 0);
lean_inc_ref(v_c_87_);
lean_dec_ref(v_t_70_);
v___x_88_ = lean_apply_1(v_k_71_, v_c_87_);
return v___x_88_;
}
case 6:
{
lean_object* v_c_89_; lean_object* v___x_90_; 
v_c_89_ = lean_ctor_get(v_t_70_, 0);
lean_inc_ref(v_c_89_);
lean_dec_ref(v_t_70_);
v___x_90_ = lean_apply_1(v_k_71_, v_c_89_);
return v___x_90_;
}
case 7:
{
lean_object* v_x_91_; lean_object* v_c_u2081_92_; lean_object* v_c_u2082_93_; lean_object* v___x_94_; 
v_x_91_ = lean_ctor_get(v_t_70_, 0);
lean_inc(v_x_91_);
v_c_u2081_92_ = lean_ctor_get(v_t_70_, 1);
lean_inc_ref(v_c_u2081_92_);
v_c_u2082_93_ = lean_ctor_get(v_t_70_, 2);
lean_inc_ref(v_c_u2082_93_);
lean_dec_ref(v_t_70_);
v___x_94_ = lean_apply_3(v_k_71_, v_x_91_, v_c_u2081_92_, v_c_u2082_93_);
return v___x_94_;
}
case 9:
{
lean_object* v_c_95_; lean_object* v___x_96_; 
v_c_95_ = lean_ctor_get(v_t_70_, 0);
lean_inc_ref(v_c_95_);
lean_dec_ref(v_t_70_);
v___x_96_ = lean_apply_1(v_k_71_, v_c_95_);
return v___x_96_;
}
case 10:
{
lean_object* v_c_97_; lean_object* v_e_98_; lean_object* v_p_99_; lean_object* v___x_100_; 
v_c_97_ = lean_ctor_get(v_t_70_, 0);
lean_inc_ref(v_c_97_);
v_e_98_ = lean_ctor_get(v_t_70_, 1);
lean_inc_ref(v_e_98_);
v_p_99_ = lean_ctor_get(v_t_70_, 2);
lean_inc_ref(v_p_99_);
lean_dec_ref(v_t_70_);
v___x_100_ = lean_apply_3(v_k_71_, v_c_97_, v_e_98_, v_p_99_);
return v___x_100_;
}
case 11:
{
lean_object* v_e_101_; lean_object* v_p_102_; lean_object* v_re_103_; lean_object* v_rp_104_; lean_object* v_p_x27_105_; lean_object* v___x_106_; 
v_e_101_ = lean_ctor_get(v_t_70_, 0);
lean_inc_ref(v_e_101_);
v_p_102_ = lean_ctor_get(v_t_70_, 1);
lean_inc_ref(v_p_102_);
v_re_103_ = lean_ctor_get(v_t_70_, 2);
lean_inc_ref(v_re_103_);
v_rp_104_ = lean_ctor_get(v_t_70_, 3);
lean_inc_ref(v_rp_104_);
v_p_x27_105_ = lean_ctor_get(v_t_70_, 4);
lean_inc_ref(v_p_x27_105_);
lean_dec_ref(v_t_70_);
v___x_106_ = lean_apply_5(v_k_71_, v_e_101_, v_p_102_, v_re_103_, v_rp_104_, v_p_x27_105_);
return v___x_106_;
}
case 12:
{
lean_object* v_h_107_; lean_object* v_x_108_; lean_object* v_e_x27_109_; lean_object* v_p_110_; lean_object* v_re_111_; lean_object* v_rp_112_; lean_object* v_p_x27_113_; lean_object* v___x_114_; 
v_h_107_ = lean_ctor_get(v_t_70_, 0);
lean_inc_ref(v_h_107_);
v_x_108_ = lean_ctor_get(v_t_70_, 1);
lean_inc(v_x_108_);
v_e_x27_109_ = lean_ctor_get(v_t_70_, 2);
lean_inc_ref(v_e_x27_109_);
v_p_110_ = lean_ctor_get(v_t_70_, 3);
lean_inc_ref(v_p_110_);
v_re_111_ = lean_ctor_get(v_t_70_, 4);
lean_inc_ref(v_re_111_);
v_rp_112_ = lean_ctor_get(v_t_70_, 5);
lean_inc_ref(v_rp_112_);
v_p_x27_113_ = lean_ctor_get(v_t_70_, 6);
lean_inc_ref(v_p_x27_113_);
lean_dec_ref(v_t_70_);
v___x_114_ = lean_apply_7(v_k_71_, v_h_107_, v_x_108_, v_e_x27_109_, v_p_110_, v_re_111_, v_rp_112_, v_p_x27_113_);
return v___x_114_;
}
case 13:
{
lean_object* v_a_x3f_115_; lean_object* v_cs_116_; lean_object* v___x_117_; 
v_a_x3f_115_ = lean_ctor_get(v_t_70_, 0);
lean_inc(v_a_x3f_115_);
v_cs_116_ = lean_ctor_get(v_t_70_, 1);
lean_inc_ref(v_cs_116_);
lean_dec_ref(v_t_70_);
v___x_117_ = lean_apply_2(v_k_71_, v_a_x3f_115_, v_cs_116_);
return v___x_117_;
}
case 14:
{
lean_object* v_k_118_; lean_object* v_y_x3f_119_; lean_object* v_c_120_; lean_object* v___x_121_; 
v_k_118_ = lean_ctor_get(v_t_70_, 0);
lean_inc(v_k_118_);
v_y_x3f_119_ = lean_ctor_get(v_t_70_, 1);
lean_inc(v_y_x3f_119_);
v_c_120_ = lean_ctor_get(v_t_70_, 2);
lean_inc_ref(v_c_120_);
lean_dec_ref(v_t_70_);
v___x_121_ = lean_apply_3(v_k_71_, v_k_118_, v_y_x3f_119_, v_c_120_);
return v___x_121_;
}
case 15:
{
lean_object* v_k_122_; lean_object* v_y_x3f_123_; lean_object* v_c_124_; lean_object* v___x_125_; 
v_k_122_ = lean_ctor_get(v_t_70_, 0);
lean_inc(v_k_122_);
v_y_x3f_123_ = lean_ctor_get(v_t_70_, 1);
lean_inc(v_y_x3f_123_);
v_c_124_ = lean_ctor_get(v_t_70_, 2);
lean_inc_ref(v_c_124_);
lean_dec_ref(v_t_70_);
v___x_125_ = lean_apply_3(v_k_71_, v_k_122_, v_y_x3f_123_, v_c_124_);
return v___x_125_;
}
case 16:
{
lean_object* v_ka_126_; lean_object* v_ca_x3f_127_; lean_object* v_kb_128_; lean_object* v_cb_x3f_129_; lean_object* v___x_130_; 
v_ka_126_ = lean_ctor_get(v_t_70_, 0);
lean_inc(v_ka_126_);
v_ca_x3f_127_ = lean_ctor_get(v_t_70_, 1);
lean_inc(v_ca_x3f_127_);
v_kb_128_ = lean_ctor_get(v_t_70_, 2);
lean_inc(v_kb_128_);
v_cb_x3f_129_ = lean_ctor_get(v_t_70_, 3);
lean_inc(v_cb_x3f_129_);
lean_dec_ref(v_t_70_);
v___x_130_ = lean_apply_4(v_k_71_, v_ka_126_, v_ca_x3f_127_, v_kb_128_, v_cb_x3f_129_);
return v___x_130_;
}
default: 
{
lean_object* v_a_131_; lean_object* v_zero_132_; lean_object* v___x_133_; 
v_a_131_ = lean_ctor_get(v_t_70_, 0);
lean_inc_ref(v_a_131_);
v_zero_132_ = lean_ctor_get(v_t_70_, 1);
lean_inc_ref(v_zero_132_);
lean_dec_ref(v_t_70_);
v___x_133_ = lean_apply_2(v_k_71_, v_a_131_, v_zero_132_);
return v___x_133_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim(lean_object* v_motive__2_134_, lean_object* v_ctorIdx_135_, lean_object* v_t_136_, lean_object* v_h_137_, lean_object* v_k_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_136_, v_k_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___boxed(lean_object* v_motive__2_140_, lean_object* v_ctorIdx_141_, lean_object* v_t_142_, lean_object* v_h_143_, lean_object* v_k_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim(v_motive__2_140_, v_ctorIdx_141_, v_t_142_, v_h_143_, v_k_144_);
lean_dec(v_ctorIdx_141_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core0_elim___redArg(lean_object* v_t_146_, lean_object* v_core0_147_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_146_, v_core0_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core0_elim(lean_object* v_motive__2_149_, lean_object* v_t_150_, lean_object* v_h_151_, lean_object* v_core0_152_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_150_, v_core0_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core_elim___redArg(lean_object* v_t_154_, lean_object* v_core_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_154_, v_core_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core_elim(lean_object* v_motive__2_157_, lean_object* v_t_158_, lean_object* v_h_159_, lean_object* v_core_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_158_, v_core_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_coreToInt_elim___redArg(lean_object* v_t_162_, lean_object* v_coreToInt_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_162_, v_coreToInt_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_coreToInt_elim(lean_object* v_motive__2_165_, lean_object* v_t_166_, lean_object* v_h_167_, lean_object* v_coreToInt_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_166_, v_coreToInt_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defn_elim___redArg(lean_object* v_t_170_, lean_object* v_defn_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_170_, v_defn_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defn_elim(lean_object* v_motive__2_173_, lean_object* v_t_174_, lean_object* v_h_175_, lean_object* v_defn_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_174_, v_defn_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnNat_elim___redArg(lean_object* v_t_178_, lean_object* v_defnNat_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_178_, v_defnNat_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnNat_elim(lean_object* v_motive__2_181_, lean_object* v_t_182_, lean_object* v_h_183_, lean_object* v_defnNat_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_182_, v_defnNat_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_norm_elim___redArg(lean_object* v_t_186_, lean_object* v_norm_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_186_, v_norm_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_norm_elim(lean_object* v_motive__2_189_, lean_object* v_t_190_, lean_object* v_h_191_, lean_object* v_norm_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_190_, v_norm_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_divCoeffs_elim___redArg(lean_object* v_t_194_, lean_object* v_divCoeffs_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_194_, v_divCoeffs_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_divCoeffs_elim(lean_object* v_motive__2_197_, lean_object* v_t_198_, lean_object* v_h_199_, lean_object* v_divCoeffs_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_198_, v_divCoeffs_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_subst_elim___redArg(lean_object* v_t_202_, lean_object* v_subst_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_202_, v_subst_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_subst_elim(lean_object* v_motive__2_205_, lean_object* v_t_206_, lean_object* v_h_207_, lean_object* v_subst_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_206_, v_subst_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofLeGe_elim___redArg(lean_object* v_t_210_, lean_object* v_ofLeGe_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_210_, v_ofLeGe_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofLeGe_elim(lean_object* v_motive__2_213_, lean_object* v_t_214_, lean_object* v_h_215_, lean_object* v_ofLeGe_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_214_, v_ofLeGe_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_reorder_elim___redArg(lean_object* v_t_218_, lean_object* v_reorder_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_218_, v_reorder_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_reorder_elim(lean_object* v_motive__2_221_, lean_object* v_t_222_, lean_object* v_h_223_, lean_object* v_reorder_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_222_, v_reorder_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_commRingNorm_elim___redArg(lean_object* v_t_226_, lean_object* v_commRingNorm_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_226_, v_commRingNorm_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_commRingNorm_elim(lean_object* v_motive__2_229_, lean_object* v_t_230_, lean_object* v_h_231_, lean_object* v_commRingNorm_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_230_, v_commRingNorm_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnCommRing_elim___redArg(lean_object* v_t_234_, lean_object* v_defnCommRing_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_234_, v_defnCommRing_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnCommRing_elim(lean_object* v_motive__2_237_, lean_object* v_t_238_, lean_object* v_h_239_, lean_object* v_defnCommRing_240_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_238_, v_defnCommRing_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnNatCommRing_elim___redArg(lean_object* v_t_242_, lean_object* v_defnNatCommRing_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_242_, v_defnNatCommRing_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnNatCommRing_elim(lean_object* v_motive__2_245_, lean_object* v_t_246_, lean_object* v_h_247_, lean_object* v_defnNatCommRing_248_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_246_, v_defnNatCommRing_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mul_elim___redArg(lean_object* v_t_250_, lean_object* v_mul_251_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_250_, v_mul_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mul_elim(lean_object* v_motive__2_253_, lean_object* v_t_254_, lean_object* v_h_255_, lean_object* v_mul_256_){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_254_, v_mul_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_div_elim___redArg(lean_object* v_t_258_, lean_object* v_div_259_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_258_, v_div_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_div_elim(lean_object* v_motive__2_261_, lean_object* v_t_262_, lean_object* v_h_263_, lean_object* v_div_264_){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_262_, v_div_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mod_elim___redArg(lean_object* v_t_266_, lean_object* v_mod_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_266_, v_mod_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mod_elim(lean_object* v_motive__2_269_, lean_object* v_t_270_, lean_object* v_h_271_, lean_object* v_mod_272_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_270_, v_mod_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_pow_elim___redArg(lean_object* v_t_274_, lean_object* v_pow_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_274_, v_pow_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_pow_elim(lean_object* v_motive__2_277_, lean_object* v_t_278_, lean_object* v_h_279_, lean_object* v_pow_280_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_278_, v_pow_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorIdx(lean_object* v_x_282_){
_start:
{
if (lean_obj_tag(v_x_282_) == 0)
{
lean_object* v___x_283_; 
v___x_283_ = lean_unsigned_to_nat(0u);
return v___x_283_;
}
else
{
lean_object* v___x_284_; 
v___x_284_ = lean_unsigned_to_nat(1u);
return v___x_284_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorIdx___boxed(lean_object* v_x_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorIdx(v_x_285_);
lean_dec_ref(v_x_285_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(lean_object* v_t_287_, lean_object* v_k_288_){
_start:
{
if (lean_obj_tag(v_t_287_) == 0)
{
lean_object* v_h_289_; lean_object* v___x_290_; 
v_h_289_ = lean_ctor_get(v_t_287_, 0);
lean_inc(v_h_289_);
lean_dec_ref(v_t_287_);
v___x_290_ = lean_apply_1(v_k_288_, v_h_289_);
return v___x_290_;
}
else
{
lean_object* v_hs_291_; lean_object* v_decVars_292_; lean_object* v___x_293_; 
v_hs_291_ = lean_ctor_get(v_t_287_, 0);
lean_inc_ref(v_hs_291_);
v_decVars_292_ = lean_ctor_get(v_t_287_, 1);
lean_inc_ref(v_decVars_292_);
lean_dec_ref(v_t_287_);
v___x_293_ = lean_apply_2(v_k_288_, v_hs_291_, v_decVars_292_);
return v___x_293_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim(lean_object* v_motive__6_294_, lean_object* v_ctorIdx_295_, lean_object* v_t_296_, lean_object* v_h_297_, lean_object* v_k_298_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_296_, v_k_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___boxed(lean_object* v_motive__6_300_, lean_object* v_ctorIdx_301_, lean_object* v_t_302_, lean_object* v_h_303_, lean_object* v_k_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim(v_motive__6_300_, v_ctorIdx_301_, v_t_302_, v_h_303_, v_k_304_);
lean_dec(v_ctorIdx_301_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_dec_elim___redArg(lean_object* v_t_306_, lean_object* v_dec_307_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_306_, v_dec_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_dec_elim(lean_object* v_motive__6_309_, lean_object* v_t_310_, lean_object* v_h_311_, lean_object* v_dec_312_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_310_, v_dec_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_last_elim___redArg(lean_object* v_t_314_, lean_object* v_last_315_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_314_, v_last_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_last_elim(lean_object* v_motive__6_317_, lean_object* v_t_318_, lean_object* v_h_319_, lean_object* v_last_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_318_, v_last_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorIdx(lean_object* v_x_322_){
_start:
{
switch(lean_obj_tag(v_x_322_))
{
case 0:
{
lean_object* v___x_323_; 
v___x_323_ = lean_unsigned_to_nat(0u);
return v___x_323_;
}
case 1:
{
lean_object* v___x_324_; 
v___x_324_ = lean_unsigned_to_nat(1u);
return v___x_324_;
}
case 2:
{
lean_object* v___x_325_; 
v___x_325_ = lean_unsigned_to_nat(2u);
return v___x_325_;
}
case 3:
{
lean_object* v___x_326_; 
v___x_326_ = lean_unsigned_to_nat(3u);
return v___x_326_;
}
case 4:
{
lean_object* v___x_327_; 
v___x_327_ = lean_unsigned_to_nat(4u);
return v___x_327_;
}
case 5:
{
lean_object* v___x_328_; 
v___x_328_ = lean_unsigned_to_nat(5u);
return v___x_328_;
}
case 6:
{
lean_object* v___x_329_; 
v___x_329_ = lean_unsigned_to_nat(6u);
return v___x_329_;
}
case 7:
{
lean_object* v___x_330_; 
v___x_330_ = lean_unsigned_to_nat(7u);
return v___x_330_;
}
case 8:
{
lean_object* v___x_331_; 
v___x_331_ = lean_unsigned_to_nat(8u);
return v___x_331_;
}
case 9:
{
lean_object* v___x_332_; 
v___x_332_ = lean_unsigned_to_nat(9u);
return v___x_332_;
}
case 10:
{
lean_object* v___x_333_; 
v___x_333_ = lean_unsigned_to_nat(10u);
return v___x_333_;
}
case 11:
{
lean_object* v___x_334_; 
v___x_334_ = lean_unsigned_to_nat(11u);
return v___x_334_;
}
default: 
{
lean_object* v___x_335_; 
v___x_335_ = lean_unsigned_to_nat(12u);
return v___x_335_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorIdx___boxed(lean_object* v_x_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorIdx(v_x_336_);
lean_dec_ref(v_x_336_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(lean_object* v_t_338_, lean_object* v_k_339_){
_start:
{
switch(lean_obj_tag(v_t_338_))
{
case 1:
{
lean_object* v_e_340_; lean_object* v_thm_341_; lean_object* v_d_342_; lean_object* v_a_343_; lean_object* v___x_344_; 
v_e_340_ = lean_ctor_get(v_t_338_, 0);
lean_inc_ref(v_e_340_);
v_thm_341_ = lean_ctor_get(v_t_338_, 1);
lean_inc_ref(v_thm_341_);
v_d_342_ = lean_ctor_get(v_t_338_, 2);
lean_inc(v_d_342_);
v_a_343_ = lean_ctor_get(v_t_338_, 3);
lean_inc_ref(v_a_343_);
lean_dec_ref(v_t_338_);
v___x_344_ = lean_apply_4(v_k_339_, v_e_340_, v_thm_341_, v_d_342_, v_a_343_);
return v___x_344_;
}
case 4:
{
lean_object* v_c_u2081_345_; lean_object* v_c_u2082_346_; lean_object* v___x_347_; 
v_c_u2081_345_ = lean_ctor_get(v_t_338_, 0);
lean_inc_ref(v_c_u2081_345_);
v_c_u2082_346_ = lean_ctor_get(v_t_338_, 1);
lean_inc_ref(v_c_u2082_346_);
lean_dec_ref(v_t_338_);
v___x_347_ = lean_apply_2(v_k_339_, v_c_u2081_345_, v_c_u2082_346_);
return v___x_347_;
}
case 5:
{
lean_object* v_c_u2081_348_; lean_object* v_c_u2082_349_; lean_object* v___x_350_; 
v_c_u2081_348_ = lean_ctor_get(v_t_338_, 0);
lean_inc_ref(v_c_u2081_348_);
v_c_u2082_349_ = lean_ctor_get(v_t_338_, 1);
lean_inc_ref(v_c_u2082_349_);
lean_dec_ref(v_t_338_);
v___x_350_ = lean_apply_2(v_k_339_, v_c_u2081_348_, v_c_u2082_349_);
return v___x_350_;
}
case 7:
{
lean_object* v_x_351_; lean_object* v_c_352_; lean_object* v___x_353_; 
v_x_351_ = lean_ctor_get(v_t_338_, 0);
lean_inc(v_x_351_);
v_c_352_ = lean_ctor_get(v_t_338_, 1);
lean_inc_ref(v_c_352_);
lean_dec_ref(v_t_338_);
v___x_353_ = lean_apply_2(v_k_339_, v_x_351_, v_c_352_);
return v___x_353_;
}
case 8:
{
lean_object* v_x_354_; lean_object* v_c_u2081_355_; lean_object* v_c_u2082_356_; lean_object* v___x_357_; 
v_x_354_ = lean_ctor_get(v_t_338_, 0);
lean_inc(v_x_354_);
v_c_u2081_355_ = lean_ctor_get(v_t_338_, 1);
lean_inc_ref(v_c_u2081_355_);
v_c_u2082_356_ = lean_ctor_get(v_t_338_, 2);
lean_inc_ref(v_c_u2082_356_);
lean_dec_ref(v_t_338_);
v___x_357_ = lean_apply_3(v_k_339_, v_x_354_, v_c_u2081_355_, v_c_u2082_356_);
return v___x_357_;
}
case 12:
{
lean_object* v_c_358_; lean_object* v_e_359_; lean_object* v_p_360_; lean_object* v___x_361_; 
v_c_358_ = lean_ctor_get(v_t_338_, 0);
lean_inc_ref(v_c_358_);
v_e_359_ = lean_ctor_get(v_t_338_, 1);
lean_inc_ref(v_e_359_);
v_p_360_ = lean_ctor_get(v_t_338_, 2);
lean_inc_ref(v_p_360_);
lean_dec_ref(v_t_338_);
v___x_361_ = lean_apply_3(v_k_339_, v_c_358_, v_e_359_, v_p_360_);
return v___x_361_;
}
default: 
{
lean_object* v_e_362_; lean_object* v___x_363_; 
v_e_362_ = lean_ctor_get(v_t_338_, 0);
lean_inc_ref(v_e_362_);
lean_dec_ref(v_t_338_);
v___x_363_ = lean_apply_1(v_k_339_, v_e_362_);
return v___x_363_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim(lean_object* v_motive__7_364_, lean_object* v_ctorIdx_365_, lean_object* v_t_366_, lean_object* v_h_367_, lean_object* v_k_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_366_, v_k_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___boxed(lean_object* v_motive__7_370_, lean_object* v_ctorIdx_371_, lean_object* v_t_372_, lean_object* v_h_373_, lean_object* v_k_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim(v_motive__7_370_, v_ctorIdx_371_, v_t_372_, v_h_373_, v_k_374_);
lean_dec(v_ctorIdx_371_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_core_elim___redArg(lean_object* v_t_376_, lean_object* v_core_377_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_376_, v_core_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_core_elim(lean_object* v_motive__7_379_, lean_object* v_t_380_, lean_object* v_h_381_, lean_object* v_core_382_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_380_, v_core_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_coreOfNat_elim___redArg(lean_object* v_t_384_, lean_object* v_coreOfNat_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_384_, v_coreOfNat_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_coreOfNat_elim(lean_object* v_motive__7_387_, lean_object* v_t_388_, lean_object* v_h_389_, lean_object* v_coreOfNat_390_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_388_, v_coreOfNat_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_norm_elim___redArg(lean_object* v_t_392_, lean_object* v_norm_393_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_392_, v_norm_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_norm_elim(lean_object* v_motive__7_395_, lean_object* v_t_396_, lean_object* v_h_397_, lean_object* v_norm_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_396_, v_norm_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_divCoeffs_elim___redArg(lean_object* v_t_400_, lean_object* v_divCoeffs_401_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_400_, v_divCoeffs_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_divCoeffs_elim(lean_object* v_motive__7_403_, lean_object* v_t_404_, lean_object* v_h_405_, lean_object* v_divCoeffs_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_404_, v_divCoeffs_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveCombine_elim___redArg(lean_object* v_t_408_, lean_object* v_solveCombine_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_408_, v_solveCombine_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveCombine_elim(lean_object* v_motive__7_411_, lean_object* v_t_412_, lean_object* v_h_413_, lean_object* v_solveCombine_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_412_, v_solveCombine_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveElim_elim___redArg(lean_object* v_t_416_, lean_object* v_solveElim_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_416_, v_solveElim_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveElim_elim(lean_object* v_motive__7_419_, lean_object* v_t_420_, lean_object* v_h_421_, lean_object* v_solveElim_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_420_, v_solveElim_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_elim_elim___redArg(lean_object* v_t_424_, lean_object* v_elim_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_424_, v_elim_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_elim_elim(lean_object* v_motive__7_427_, lean_object* v_t_428_, lean_object* v_h_429_, lean_object* v_elim_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_428_, v_elim_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ofEq_elim___redArg(lean_object* v_t_432_, lean_object* v_ofEq_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_432_, v_ofEq_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ofEq_elim(lean_object* v_motive__7_435_, lean_object* v_t_436_, lean_object* v_h_437_, lean_object* v_ofEq_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_436_, v_ofEq_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_subst_elim___redArg(lean_object* v_t_440_, lean_object* v_subst_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_440_, v_subst_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_subst_elim(lean_object* v_motive__7_443_, lean_object* v_t_444_, lean_object* v_h_445_, lean_object* v_subst_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_444_, v_subst_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2081_elim___redArg(lean_object* v_t_448_, lean_object* v_cooper_u2081_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_448_, v_cooper_u2081_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2081_elim(lean_object* v_motive__7_451_, lean_object* v_t_452_, lean_object* v_h_453_, lean_object* v_cooper_u2081_454_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_452_, v_cooper_u2081_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2082_elim___redArg(lean_object* v_t_456_, lean_object* v_cooper_u2082_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_456_, v_cooper_u2082_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2082_elim(lean_object* v_motive__7_459_, lean_object* v_t_460_, lean_object* v_h_461_, lean_object* v_cooper_u2082_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_460_, v_cooper_u2082_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_reorder_elim___redArg(lean_object* v_t_464_, lean_object* v_reorder_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_464_, v_reorder_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_reorder_elim(lean_object* v_motive__7_467_, lean_object* v_t_468_, lean_object* v_h_469_, lean_object* v_reorder_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_468_, v_reorder_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_commRingNorm_elim___redArg(lean_object* v_t_472_, lean_object* v_commRingNorm_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_472_, v_commRingNorm_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_commRingNorm_elim(lean_object* v_motive__7_475_, lean_object* v_t_476_, lean_object* v_h_477_, lean_object* v_commRingNorm_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_476_, v_commRingNorm_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorIdx(lean_object* v_x_480_){
_start:
{
switch(lean_obj_tag(v_x_480_))
{
case 0:
{
lean_object* v___x_481_; 
v___x_481_ = lean_unsigned_to_nat(0u);
return v___x_481_;
}
case 1:
{
lean_object* v___x_482_; 
v___x_482_ = lean_unsigned_to_nat(1u);
return v___x_482_;
}
case 2:
{
lean_object* v___x_483_; 
v___x_483_ = lean_unsigned_to_nat(2u);
return v___x_483_;
}
case 3:
{
lean_object* v___x_484_; 
v___x_484_ = lean_unsigned_to_nat(3u);
return v___x_484_;
}
case 4:
{
lean_object* v___x_485_; 
v___x_485_ = lean_unsigned_to_nat(4u);
return v___x_485_;
}
case 5:
{
lean_object* v___x_486_; 
v___x_486_ = lean_unsigned_to_nat(5u);
return v___x_486_;
}
case 6:
{
lean_object* v___x_487_; 
v___x_487_ = lean_unsigned_to_nat(6u);
return v___x_487_;
}
case 7:
{
lean_object* v___x_488_; 
v___x_488_ = lean_unsigned_to_nat(7u);
return v___x_488_;
}
case 8:
{
lean_object* v___x_489_; 
v___x_489_ = lean_unsigned_to_nat(8u);
return v___x_489_;
}
case 9:
{
lean_object* v___x_490_; 
v___x_490_ = lean_unsigned_to_nat(9u);
return v___x_490_;
}
case 10:
{
lean_object* v___x_491_; 
v___x_491_ = lean_unsigned_to_nat(10u);
return v___x_491_;
}
case 11:
{
lean_object* v___x_492_; 
v___x_492_ = lean_unsigned_to_nat(11u);
return v___x_492_;
}
case 12:
{
lean_object* v___x_493_; 
v___x_493_ = lean_unsigned_to_nat(12u);
return v___x_493_;
}
case 13:
{
lean_object* v___x_494_; 
v___x_494_ = lean_unsigned_to_nat(13u);
return v___x_494_;
}
case 14:
{
lean_object* v___x_495_; 
v___x_495_ = lean_unsigned_to_nat(14u);
return v___x_495_;
}
case 15:
{
lean_object* v___x_496_; 
v___x_496_ = lean_unsigned_to_nat(15u);
return v___x_496_;
}
case 16:
{
lean_object* v___x_497_; 
v___x_497_ = lean_unsigned_to_nat(16u);
return v___x_497_;
}
default: 
{
lean_object* v___x_498_; 
v___x_498_ = lean_unsigned_to_nat(17u);
return v___x_498_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorIdx___boxed(lean_object* v_x_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorIdx(v_x_499_);
lean_dec_ref(v_x_499_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(lean_object* v_t_501_, lean_object* v_k_502_){
_start:
{
switch(lean_obj_tag(v_t_501_))
{
case 1:
{
lean_object* v_e_503_; lean_object* v_p_504_; lean_object* v___x_505_; 
v_e_503_ = lean_ctor_get(v_t_501_, 0);
lean_inc_ref(v_e_503_);
v_p_504_ = lean_ctor_get(v_t_501_, 1);
lean_inc_ref(v_p_504_);
lean_dec_ref(v_t_501_);
v___x_505_ = lean_apply_2(v_k_502_, v_e_503_, v_p_504_);
return v___x_505_;
}
case 2:
{
lean_object* v_e_506_; uint8_t v_pos_507_; lean_object* v_toIntThm_508_; lean_object* v_lhs_509_; lean_object* v_rhs_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v_e_506_ = lean_ctor_get(v_t_501_, 0);
lean_inc_ref(v_e_506_);
v_pos_507_ = lean_ctor_get_uint8(v_t_501_, sizeof(void*)*4);
v_toIntThm_508_ = lean_ctor_get(v_t_501_, 1);
lean_inc_ref(v_toIntThm_508_);
v_lhs_509_ = lean_ctor_get(v_t_501_, 2);
lean_inc_ref(v_lhs_509_);
v_rhs_510_ = lean_ctor_get(v_t_501_, 3);
lean_inc_ref(v_rhs_510_);
lean_dec_ref(v_t_501_);
v___x_511_ = lean_box(v_pos_507_);
v___x_512_ = lean_apply_5(v_k_502_, v_e_506_, v___x_511_, v_toIntThm_508_, v_lhs_509_, v_rhs_510_);
return v___x_512_;
}
case 5:
{
lean_object* v_h_513_; lean_object* v___x_514_; 
v_h_513_ = lean_ctor_get(v_t_501_, 0);
lean_inc(v_h_513_);
lean_dec_ref(v_t_501_);
v___x_514_ = lean_apply_1(v_k_502_, v_h_513_);
return v___x_514_;
}
case 8:
{
lean_object* v_c_u2081_515_; lean_object* v_c_u2082_516_; lean_object* v___x_517_; 
v_c_u2081_515_ = lean_ctor_get(v_t_501_, 0);
lean_inc_ref(v_c_u2081_515_);
v_c_u2082_516_ = lean_ctor_get(v_t_501_, 1);
lean_inc_ref(v_c_u2082_516_);
lean_dec_ref(v_t_501_);
v___x_517_ = lean_apply_2(v_k_502_, v_c_u2081_515_, v_c_u2082_516_);
return v___x_517_;
}
case 9:
{
lean_object* v_c_u2081_518_; lean_object* v_c_u2082_519_; lean_object* v_k_520_; lean_object* v___x_521_; 
v_c_u2081_518_ = lean_ctor_get(v_t_501_, 0);
lean_inc_ref(v_c_u2081_518_);
v_c_u2082_519_ = lean_ctor_get(v_t_501_, 1);
lean_inc_ref(v_c_u2082_519_);
v_k_520_ = lean_ctor_get(v_t_501_, 2);
lean_inc(v_k_520_);
lean_dec_ref(v_t_501_);
v___x_521_ = lean_apply_3(v_k_502_, v_c_u2081_518_, v_c_u2082_519_, v_k_520_);
return v___x_521_;
}
case 10:
{
lean_object* v_x_522_; lean_object* v_c_u2081_523_; lean_object* v_c_u2082_524_; lean_object* v___x_525_; 
v_x_522_ = lean_ctor_get(v_t_501_, 0);
lean_inc(v_x_522_);
v_c_u2081_523_ = lean_ctor_get(v_t_501_, 1);
lean_inc_ref(v_c_u2081_523_);
v_c_u2082_524_ = lean_ctor_get(v_t_501_, 2);
lean_inc_ref(v_c_u2082_524_);
lean_dec_ref(v_t_501_);
v___x_525_ = lean_apply_3(v_k_502_, v_x_522_, v_c_u2081_523_, v_c_u2082_524_);
return v___x_525_;
}
case 11:
{
lean_object* v_c_u2081_526_; lean_object* v_c_u2082_527_; lean_object* v___x_528_; 
v_c_u2081_526_ = lean_ctor_get(v_t_501_, 0);
lean_inc_ref(v_c_u2081_526_);
v_c_u2082_527_ = lean_ctor_get(v_t_501_, 1);
lean_inc_ref(v_c_u2082_527_);
lean_dec_ref(v_t_501_);
v___x_528_ = lean_apply_2(v_k_502_, v_c_u2081_526_, v_c_u2082_527_);
return v___x_528_;
}
case 12:
{
lean_object* v_c_u2081_529_; lean_object* v_decVar_530_; lean_object* v_h_531_; lean_object* v_decVars_532_; lean_object* v___x_533_; 
v_c_u2081_529_ = lean_ctor_get(v_t_501_, 0);
lean_inc_ref(v_c_u2081_529_);
v_decVar_530_ = lean_ctor_get(v_t_501_, 1);
lean_inc(v_decVar_530_);
v_h_531_ = lean_ctor_get(v_t_501_, 2);
lean_inc_ref(v_h_531_);
v_decVars_532_ = lean_ctor_get(v_t_501_, 3);
lean_inc_ref(v_decVars_532_);
lean_dec_ref(v_t_501_);
v___x_533_ = lean_apply_4(v_k_502_, v_c_u2081_529_, v_decVar_530_, v_h_531_, v_decVars_532_);
return v___x_533_;
}
case 14:
{
lean_object* v_c_u2081_534_; lean_object* v_c_u2082_535_; lean_object* v___x_536_; 
v_c_u2081_534_ = lean_ctor_get(v_t_501_, 0);
lean_inc_ref(v_c_u2081_534_);
v_c_u2082_535_ = lean_ctor_get(v_t_501_, 1);
lean_inc_ref(v_c_u2082_535_);
lean_dec_ref(v_t_501_);
v___x_536_ = lean_apply_2(v_k_502_, v_c_u2081_534_, v_c_u2082_535_);
return v___x_536_;
}
case 15:
{
lean_object* v_c_u2081_537_; lean_object* v_c_u2082_538_; lean_object* v___x_539_; 
v_c_u2081_537_ = lean_ctor_get(v_t_501_, 0);
lean_inc_ref(v_c_u2081_537_);
v_c_u2082_538_ = lean_ctor_get(v_t_501_, 1);
lean_inc_ref(v_c_u2082_538_);
lean_dec_ref(v_t_501_);
v___x_539_ = lean_apply_2(v_k_502_, v_c_u2081_537_, v_c_u2082_538_);
return v___x_539_;
}
case 17:
{
lean_object* v_c_540_; lean_object* v_e_541_; lean_object* v_p_542_; lean_object* v___x_543_; 
v_c_540_ = lean_ctor_get(v_t_501_, 0);
lean_inc_ref(v_c_540_);
v_e_541_ = lean_ctor_get(v_t_501_, 1);
lean_inc_ref(v_e_541_);
v_p_542_ = lean_ctor_get(v_t_501_, 2);
lean_inc_ref(v_p_542_);
lean_dec_ref(v_t_501_);
v___x_543_ = lean_apply_3(v_k_502_, v_c_540_, v_e_541_, v_p_542_);
return v___x_543_;
}
default: 
{
lean_object* v_e_544_; lean_object* v___x_545_; 
v_e_544_ = lean_ctor_get(v_t_501_, 0);
lean_inc_ref(v_e_544_);
lean_dec_ref(v_t_501_);
v___x_545_ = lean_apply_1(v_k_502_, v_e_544_);
return v___x_545_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim(lean_object* v_motive__9_546_, lean_object* v_ctorIdx_547_, lean_object* v_t_548_, lean_object* v_h_549_, lean_object* v_k_550_){
_start:
{
lean_object* v___x_551_; 
v___x_551_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_548_, v_k_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___boxed(lean_object* v_motive__9_552_, lean_object* v_ctorIdx_553_, lean_object* v_t_554_, lean_object* v_h_555_, lean_object* v_k_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim(v_motive__9_552_, v_ctorIdx_553_, v_t_554_, v_h_555_, v_k_556_);
lean_dec(v_ctorIdx_553_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_core_elim___redArg(lean_object* v_t_558_, lean_object* v_core_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_558_, v_core_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_core_elim(lean_object* v_motive__9_561_, lean_object* v_t_562_, lean_object* v_h_563_, lean_object* v_core_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_562_, v_core_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreNeg_elim___redArg(lean_object* v_t_566_, lean_object* v_coreNeg_567_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_566_, v_coreNeg_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreNeg_elim(lean_object* v_motive__9_569_, lean_object* v_t_570_, lean_object* v_h_571_, lean_object* v_coreNeg_572_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_570_, v_coreNeg_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreToInt_elim___redArg(lean_object* v_t_574_, lean_object* v_coreToInt_575_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_574_, v_coreToInt_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreToInt_elim(lean_object* v_motive__9_577_, lean_object* v_t_578_, lean_object* v_h_579_, lean_object* v_coreToInt_580_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_578_, v_coreToInt_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofNatNonneg_elim___redArg(lean_object* v_t_582_, lean_object* v_ofNatNonneg_583_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_582_, v_ofNatNonneg_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofNatNonneg_elim(lean_object* v_motive__9_585_, lean_object* v_t_586_, lean_object* v_h_587_, lean_object* v_ofNatNonneg_588_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_586_, v_ofNatNonneg_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_bound_elim___redArg(lean_object* v_t_590_, lean_object* v_bound_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_590_, v_bound_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_bound_elim(lean_object* v_motive__9_593_, lean_object* v_t_594_, lean_object* v_h_595_, lean_object* v_bound_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_594_, v_bound_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dec_elim___redArg(lean_object* v_t_598_, lean_object* v_dec_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_598_, v_dec_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dec_elim(lean_object* v_motive__9_601_, lean_object* v_t_602_, lean_object* v_h_603_, lean_object* v_dec_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_602_, v_dec_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_norm_elim___redArg(lean_object* v_t_606_, lean_object* v_norm_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_606_, v_norm_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_norm_elim(lean_object* v_motive__9_609_, lean_object* v_t_610_, lean_object* v_h_611_, lean_object* v_norm_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_610_, v_norm_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_divCoeffs_elim___redArg(lean_object* v_t_614_, lean_object* v_divCoeffs_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_614_, v_divCoeffs_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_divCoeffs_elim(lean_object* v_motive__9_617_, lean_object* v_t_618_, lean_object* v_h_619_, lean_object* v_divCoeffs_620_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_618_, v_divCoeffs_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combine_elim___redArg(lean_object* v_t_622_, lean_object* v_combine_623_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_622_, v_combine_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combine_elim(lean_object* v_motive__9_625_, lean_object* v_t_626_, lean_object* v_h_627_, lean_object* v_combine_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_626_, v_combine_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combineDivCoeffs_elim___redArg(lean_object* v_t_630_, lean_object* v_combineDivCoeffs_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_630_, v_combineDivCoeffs_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combineDivCoeffs_elim(lean_object* v_motive__9_633_, lean_object* v_t_634_, lean_object* v_h_635_, lean_object* v_combineDivCoeffs_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_634_, v_combineDivCoeffs_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_subst_elim___redArg(lean_object* v_t_638_, lean_object* v_subst_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_638_, v_subst_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_subst_elim(lean_object* v_motive__9_641_, lean_object* v_t_642_, lean_object* v_h_643_, lean_object* v_subst_644_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_642_, v_subst_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofLeDiseq_elim___redArg(lean_object* v_t_646_, lean_object* v_ofLeDiseq_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_646_, v_ofLeDiseq_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofLeDiseq_elim(lean_object* v_motive__9_649_, lean_object* v_t_650_, lean_object* v_h_651_, lean_object* v_ofLeDiseq_652_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_650_, v_ofLeDiseq_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofDiseqSplit_elim___redArg(lean_object* v_t_654_, lean_object* v_ofDiseqSplit_655_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_654_, v_ofDiseqSplit_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofDiseqSplit_elim(lean_object* v_motive__9_657_, lean_object* v_t_658_, lean_object* v_h_659_, lean_object* v_ofDiseqSplit_660_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_658_, v_ofDiseqSplit_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_cooper_elim___redArg(lean_object* v_t_662_, lean_object* v_cooper_663_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_662_, v_cooper_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_cooper_elim(lean_object* v_motive__9_665_, lean_object* v_t_666_, lean_object* v_h_667_, lean_object* v_cooper_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_666_, v_cooper_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dvdTight_elim___redArg(lean_object* v_t_670_, lean_object* v_dvdTight_671_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_670_, v_dvdTight_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dvdTight_elim(lean_object* v_motive__9_673_, lean_object* v_t_674_, lean_object* v_h_675_, lean_object* v_dvdTight_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_674_, v_dvdTight_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_negDvdTight_elim___redArg(lean_object* v_t_678_, lean_object* v_negDvdTight_679_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_678_, v_negDvdTight_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_negDvdTight_elim(lean_object* v_motive__9_681_, lean_object* v_t_682_, lean_object* v_h_683_, lean_object* v_negDvdTight_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_682_, v_negDvdTight_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_reorder_elim___redArg(lean_object* v_t_686_, lean_object* v_reorder_687_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_686_, v_reorder_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_reorder_elim(lean_object* v_motive__9_689_, lean_object* v_t_690_, lean_object* v_h_691_, lean_object* v_reorder_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_690_, v_reorder_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_commRingNorm_elim___redArg(lean_object* v_t_694_, lean_object* v_commRingNorm_695_){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_694_, v_commRingNorm_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_commRingNorm_elim(lean_object* v_motive__9_697_, lean_object* v_t_698_, lean_object* v_h_699_, lean_object* v_commRingNorm_700_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_698_, v_commRingNorm_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorIdx(lean_object* v_x_702_){
_start:
{
switch(lean_obj_tag(v_x_702_))
{
case 0:
{
lean_object* v___x_703_; 
v___x_703_ = lean_unsigned_to_nat(0u);
return v___x_703_;
}
case 1:
{
lean_object* v___x_704_; 
v___x_704_ = lean_unsigned_to_nat(1u);
return v___x_704_;
}
case 2:
{
lean_object* v___x_705_; 
v___x_705_ = lean_unsigned_to_nat(2u);
return v___x_705_;
}
case 3:
{
lean_object* v___x_706_; 
v___x_706_ = lean_unsigned_to_nat(3u);
return v___x_706_;
}
case 4:
{
lean_object* v___x_707_; 
v___x_707_ = lean_unsigned_to_nat(4u);
return v___x_707_;
}
case 5:
{
lean_object* v___x_708_; 
v___x_708_ = lean_unsigned_to_nat(5u);
return v___x_708_;
}
case 6:
{
lean_object* v___x_709_; 
v___x_709_ = lean_unsigned_to_nat(6u);
return v___x_709_;
}
case 7:
{
lean_object* v___x_710_; 
v___x_710_ = lean_unsigned_to_nat(7u);
return v___x_710_;
}
default: 
{
lean_object* v___x_711_; 
v___x_711_ = lean_unsigned_to_nat(8u);
return v___x_711_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorIdx___boxed(lean_object* v_x_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorIdx(v_x_712_);
lean_dec_ref(v_x_712_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(lean_object* v_t_714_, lean_object* v_k_715_){
_start:
{
switch(lean_obj_tag(v_t_714_))
{
case 0:
{
lean_object* v_a_716_; lean_object* v_zero_717_; lean_object* v___x_718_; 
v_a_716_ = lean_ctor_get(v_t_714_, 0);
lean_inc_ref(v_a_716_);
v_zero_717_ = lean_ctor_get(v_t_714_, 1);
lean_inc_ref(v_zero_717_);
lean_dec_ref(v_t_714_);
v___x_718_ = lean_apply_2(v_k_715_, v_a_716_, v_zero_717_);
return v___x_718_;
}
case 1:
{
lean_object* v_a_719_; lean_object* v_b_720_; lean_object* v_p_u2081_721_; lean_object* v_p_u2082_722_; lean_object* v___x_723_; 
v_a_719_ = lean_ctor_get(v_t_714_, 0);
lean_inc_ref(v_a_719_);
v_b_720_ = lean_ctor_get(v_t_714_, 1);
lean_inc_ref(v_b_720_);
v_p_u2081_721_ = lean_ctor_get(v_t_714_, 2);
lean_inc_ref(v_p_u2081_721_);
v_p_u2082_722_ = lean_ctor_get(v_t_714_, 3);
lean_inc_ref(v_p_u2082_722_);
lean_dec_ref(v_t_714_);
v___x_723_ = lean_apply_4(v_k_715_, v_a_719_, v_b_720_, v_p_u2081_721_, v_p_u2082_722_);
return v___x_723_;
}
case 2:
{
lean_object* v_a_724_; lean_object* v_b_725_; lean_object* v_toIntThm_726_; lean_object* v_lhs_727_; lean_object* v_rhs_728_; lean_object* v___x_729_; 
v_a_724_ = lean_ctor_get(v_t_714_, 0);
lean_inc_ref(v_a_724_);
v_b_725_ = lean_ctor_get(v_t_714_, 1);
lean_inc_ref(v_b_725_);
v_toIntThm_726_ = lean_ctor_get(v_t_714_, 2);
lean_inc_ref(v_toIntThm_726_);
v_lhs_727_ = lean_ctor_get(v_t_714_, 3);
lean_inc_ref(v_lhs_727_);
v_rhs_728_ = lean_ctor_get(v_t_714_, 4);
lean_inc_ref(v_rhs_728_);
lean_dec_ref(v_t_714_);
v___x_729_ = lean_apply_5(v_k_715_, v_a_724_, v_b_725_, v_toIntThm_726_, v_lhs_727_, v_rhs_728_);
return v___x_729_;
}
case 6:
{
lean_object* v_x_730_; lean_object* v_c_u2081_731_; lean_object* v_c_u2082_732_; lean_object* v___x_733_; 
v_x_730_ = lean_ctor_get(v_t_714_, 0);
lean_inc(v_x_730_);
v_c_u2081_731_ = lean_ctor_get(v_t_714_, 1);
lean_inc_ref(v_c_u2081_731_);
v_c_u2082_732_ = lean_ctor_get(v_t_714_, 2);
lean_inc_ref(v_c_u2082_732_);
lean_dec_ref(v_t_714_);
v___x_733_ = lean_apply_3(v_k_715_, v_x_730_, v_c_u2081_731_, v_c_u2082_732_);
return v___x_733_;
}
case 8:
{
lean_object* v_c_734_; lean_object* v_e_735_; lean_object* v_p_736_; lean_object* v___x_737_; 
v_c_734_ = lean_ctor_get(v_t_714_, 0);
lean_inc_ref(v_c_734_);
v_e_735_ = lean_ctor_get(v_t_714_, 1);
lean_inc_ref(v_e_735_);
v_p_736_ = lean_ctor_get(v_t_714_, 2);
lean_inc_ref(v_p_736_);
lean_dec_ref(v_t_714_);
v___x_737_ = lean_apply_3(v_k_715_, v_c_734_, v_e_735_, v_p_736_);
return v___x_737_;
}
default: 
{
lean_object* v_c_738_; lean_object* v___x_739_; 
v_c_738_ = lean_ctor_get(v_t_714_, 0);
lean_inc_ref(v_c_738_);
lean_dec_ref(v_t_714_);
v___x_739_ = lean_apply_1(v_k_715_, v_c_738_);
return v___x_739_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim(lean_object* v_motive__11_740_, lean_object* v_ctorIdx_741_, lean_object* v_t_742_, lean_object* v_h_743_, lean_object* v_k_744_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_742_, v_k_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___boxed(lean_object* v_motive__11_746_, lean_object* v_ctorIdx_747_, lean_object* v_t_748_, lean_object* v_h_749_, lean_object* v_k_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim(v_motive__11_746_, v_ctorIdx_747_, v_t_748_, v_h_749_, v_k_750_);
lean_dec(v_ctorIdx_747_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core0_elim___redArg(lean_object* v_t_752_, lean_object* v_core0_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_752_, v_core0_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core0_elim(lean_object* v_motive__11_755_, lean_object* v_t_756_, lean_object* v_h_757_, lean_object* v_core0_758_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_756_, v_core0_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core_elim___redArg(lean_object* v_t_760_, lean_object* v_core_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_760_, v_core_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core_elim(lean_object* v_motive__11_763_, lean_object* v_t_764_, lean_object* v_h_765_, lean_object* v_core_766_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_764_, v_core_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_coreToInt_elim___redArg(lean_object* v_t_768_, lean_object* v_coreToInt_769_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_768_, v_coreToInt_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_coreToInt_elim(lean_object* v_motive__11_771_, lean_object* v_t_772_, lean_object* v_h_773_, lean_object* v_coreToInt_774_){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_772_, v_coreToInt_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_norm_elim___redArg(lean_object* v_t_776_, lean_object* v_norm_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_776_, v_norm_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_norm_elim(lean_object* v_motive__11_779_, lean_object* v_t_780_, lean_object* v_h_781_, lean_object* v_norm_782_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_780_, v_norm_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_divCoeffs_elim___redArg(lean_object* v_t_784_, lean_object* v_divCoeffs_785_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_784_, v_divCoeffs_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_divCoeffs_elim(lean_object* v_motive__11_787_, lean_object* v_t_788_, lean_object* v_h_789_, lean_object* v_divCoeffs_790_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_788_, v_divCoeffs_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_neg_elim___redArg(lean_object* v_t_792_, lean_object* v_neg_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_792_, v_neg_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_neg_elim(lean_object* v_motive__11_795_, lean_object* v_t_796_, lean_object* v_h_797_, lean_object* v_neg_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_796_, v_neg_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_subst_elim___redArg(lean_object* v_t_800_, lean_object* v_subst_801_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_800_, v_subst_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_subst_elim(lean_object* v_motive__11_803_, lean_object* v_t_804_, lean_object* v_h_805_, lean_object* v_subst_806_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_804_, v_subst_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_reorder_elim___redArg(lean_object* v_t_808_, lean_object* v_reorder_809_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_808_, v_reorder_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_reorder_elim(lean_object* v_motive__11_811_, lean_object* v_t_812_, lean_object* v_h_813_, lean_object* v_reorder_814_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_812_, v_reorder_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_commRingNorm_elim___redArg(lean_object* v_t_816_, lean_object* v_commRingNorm_817_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_816_, v_commRingNorm_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_commRingNorm_elim(lean_object* v_motive__11_819_, lean_object* v_t_820_, lean_object* v_h_821_, lean_object* v_commRingNorm_822_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_820_, v_commRingNorm_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorIdx(lean_object* v_x_824_){
_start:
{
switch(lean_obj_tag(v_x_824_))
{
case 0:
{
lean_object* v___x_825_; 
v___x_825_ = lean_unsigned_to_nat(0u);
return v___x_825_;
}
case 1:
{
lean_object* v___x_826_; 
v___x_826_ = lean_unsigned_to_nat(1u);
return v___x_826_;
}
case 2:
{
lean_object* v___x_827_; 
v___x_827_ = lean_unsigned_to_nat(2u);
return v___x_827_;
}
case 3:
{
lean_object* v___x_828_; 
v___x_828_ = lean_unsigned_to_nat(3u);
return v___x_828_;
}
default: 
{
lean_object* v___x_829_; 
v___x_829_ = lean_unsigned_to_nat(4u);
return v___x_829_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorIdx___boxed(lean_object* v_x_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorIdx(v_x_830_);
lean_dec_ref(v_x_830_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(lean_object* v_t_832_, lean_object* v_k_833_){
_start:
{
if (lean_obj_tag(v_t_832_) == 4)
{
lean_object* v_c_u2081_834_; lean_object* v_c_u2082_835_; lean_object* v_c_u2083_836_; lean_object* v___x_837_; 
v_c_u2081_834_ = lean_ctor_get(v_t_832_, 0);
lean_inc_ref(v_c_u2081_834_);
v_c_u2082_835_ = lean_ctor_get(v_t_832_, 1);
lean_inc_ref(v_c_u2082_835_);
v_c_u2083_836_ = lean_ctor_get(v_t_832_, 2);
lean_inc_ref(v_c_u2083_836_);
lean_dec_ref(v_t_832_);
v___x_837_ = lean_apply_3(v_k_833_, v_c_u2081_834_, v_c_u2082_835_, v_c_u2083_836_);
return v___x_837_;
}
else
{
lean_object* v_c_838_; lean_object* v___x_839_; 
v_c_838_ = lean_ctor_get(v_t_832_, 0);
lean_inc_ref(v_c_838_);
lean_dec_ref(v_t_832_);
v___x_839_ = lean_apply_1(v_k_833_, v_c_838_);
return v___x_839_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim(lean_object* v_motive__12_840_, lean_object* v_ctorIdx_841_, lean_object* v_t_842_, lean_object* v_h_843_, lean_object* v_k_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_842_, v_k_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___boxed(lean_object* v_motive__12_846_, lean_object* v_ctorIdx_847_, lean_object* v_t_848_, lean_object* v_h_849_, lean_object* v_k_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim(v_motive__12_846_, v_ctorIdx_847_, v_t_848_, v_h_849_, v_k_850_);
lean_dec(v_ctorIdx_847_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_dvd_elim___redArg(lean_object* v_t_852_, lean_object* v_dvd_853_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_852_, v_dvd_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_dvd_elim(lean_object* v_motive__12_855_, lean_object* v_t_856_, lean_object* v_h_857_, lean_object* v_dvd_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_856_, v_dvd_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_le_elim___redArg(lean_object* v_t_860_, lean_object* v_le_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_860_, v_le_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_le_elim(lean_object* v_motive__12_863_, lean_object* v_t_864_, lean_object* v_h_865_, lean_object* v_le_866_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_864_, v_le_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_eq_elim___redArg(lean_object* v_t_868_, lean_object* v_eq_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_868_, v_eq_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_eq_elim(lean_object* v_motive__12_871_, lean_object* v_t_872_, lean_object* v_h_873_, lean_object* v_eq_874_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_872_, v_eq_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_diseq_elim___redArg(lean_object* v_t_876_, lean_object* v_diseq_877_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_876_, v_diseq_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_diseq_elim(lean_object* v_motive__12_879_, lean_object* v_t_880_, lean_object* v_h_881_, lean_object* v_diseq_882_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_880_, v_diseq_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_cooper_elim___redArg(lean_object* v_t_884_, lean_object* v_cooper_885_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_884_, v_cooper_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_cooper_elim(lean_object* v_motive__12_887_, lean_object* v_t_888_, lean_object* v_h_889_, lean_object* v_cooper_890_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_888_, v_cooper_890_);
return v___x_891_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0(void){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0);
v___x_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
return v___x_893_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3(void){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_897_ = lean_box(0);
v___x_898_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__2));
v___x_899_ = l_Lean_Expr_const___override(v___x_898_, v___x_897_);
return v___x_899_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4(void){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_900_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3);
v___x_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
return v___x_901_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_902_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4);
v___x_903_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0);
v___x_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
lean_ctor_set(v___x_904_, 1, v___x_902_);
return v___x_904_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr(void){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5);
return v___x_905_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3);
v___x_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
return v___x_907_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1(void){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_908_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0);
v___x_909_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0);
v___x_910_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0);
v___x_911_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
lean_ctor_set(v___x_911_, 1, v___x_909_);
lean_ctor_set(v___x_911_, 2, v___x_908_);
return v___x_911_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr(void){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1);
return v___x_912_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0(void){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; uint8_t v___x_915_; lean_object* v___x_916_; 
v___x_913_ = lean_box(0);
v___x_914_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5);
v___x_915_ = 0;
v___x_916_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_916_, 0, v___x_914_);
lean_ctor_set(v___x_916_, 1, v___x_914_);
lean_ctor_set(v___x_916_, 2, v___x_913_);
lean_ctor_set_uint8(v___x_916_, sizeof(void*)*3, v___x_915_);
return v___x_916_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred(void){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0);
return v___x_917_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1(void){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_920_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__0));
v___x_921_ = lean_unsigned_to_nat(0u);
v___x_922_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0);
v___x_923_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
lean_ctor_set(v___x_923_, 1, v___x_921_);
lean_ctor_set(v___x_923_, 2, v___x_920_);
return v___x_923_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit(void){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1);
return v___x_924_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_925_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__1(void){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_926_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0);
v___x_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0(lean_object* v_00_u03b2_928_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__1);
return v___x_929_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0(void){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_930_ = lean_unsigned_to_nat(32u);
v___x_931_ = lean_mk_empty_array_with_capacity(v___x_930_);
v___x_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
return v___x_932_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1(void){
_start:
{
size_t v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_933_ = ((size_t)5ULL);
v___x_934_ = lean_unsigned_to_nat(0u);
v___x_935_ = lean_unsigned_to_nat(32u);
v___x_936_ = lean_mk_empty_array_with_capacity(v___x_935_);
v___x_937_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0);
v___x_938_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_938_, 0, v___x_937_);
lean_ctor_set(v___x_938_, 1, v___x_936_);
lean_ctor_set(v___x_938_, 2, v___x_934_);
lean_ctor_set(v___x_938_, 3, v___x_934_);
lean_ctor_set_usize(v___x_938_, 4, v___x_933_);
return v___x_938_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2(void){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_939_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3(void){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2);
v___x_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
return v___x_941_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__4(void){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0(lean_box(0));
return v___x_942_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; uint8_t v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_943_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__4);
v___x_944_ = lean_box(0);
v___x_945_ = 0;
v___x_946_ = lean_unsigned_to_nat(0u);
v___x_947_ = lean_box(0);
v___x_948_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3);
v___x_949_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1);
v___x_950_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v___x_950_, 0, v___x_949_);
lean_ctor_set(v___x_950_, 1, v___x_948_);
lean_ctor_set(v___x_950_, 2, v___x_949_);
lean_ctor_set(v___x_950_, 3, v___x_948_);
lean_ctor_set(v___x_950_, 4, v___x_948_);
lean_ctor_set(v___x_950_, 5, v___x_948_);
lean_ctor_set(v___x_950_, 6, v___x_949_);
lean_ctor_set(v___x_950_, 7, v___x_949_);
lean_ctor_set(v___x_950_, 8, v___x_949_);
lean_ctor_set(v___x_950_, 9, v___x_949_);
lean_ctor_set(v___x_950_, 10, v___x_949_);
lean_ctor_set(v___x_950_, 11, v___x_947_);
lean_ctor_set(v___x_950_, 12, v___x_949_);
lean_ctor_set(v___x_950_, 13, v___x_949_);
lean_ctor_set(v___x_950_, 14, v___x_946_);
lean_ctor_set(v___x_950_, 15, v___x_944_);
lean_ctor_set(v___x_950_, 16, v___x_948_);
lean_ctor_set(v___x_950_, 17, v___x_943_);
lean_ctor_set(v___x_950_, 18, v___x_948_);
lean_ctor_set(v___x_950_, 19, v___x_949_);
lean_ctor_set(v___x_950_, 20, v___x_948_);
lean_ctor_set(v___x_950_, 21, v___x_948_);
lean_ctor_set(v___x_950_, 22, v___x_948_);
lean_ctor_set_uint8(v___x_950_, sizeof(void*)*23, v___x_945_);
lean_ctor_set_uint8(v___x_950_, sizeof(void*)*23 + 1, v___x_945_);
return v___x_950_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default(void){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5);
return v___x_951_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState(void){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default;
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(lean_object* v___x_953_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_955_, 0, v___x_953_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2____boxed(lean_object* v___x_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(v___x_956_);
return v_res_958_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_959_; lean_object* v___f_960_; 
v___x_959_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5);
v___f_960_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_960_, 0, v___x_959_);
return v___f_960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_962_; lean_object* v___x_963_; 
v___f_962_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_);
v___x_963_ = l_Lean_Meta_Grind_registerSolverExtension___redArg(v___f_962_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2____boxed(lean_object* v_a_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_();
return v_res_965_;
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
