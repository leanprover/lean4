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
extern lean_object* l_Int_Internal_Linear_instInhabitedExpr_default;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0;
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_le_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_le_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_le_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_le_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_eq_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_eq_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_eq_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_eq_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_eqNeg_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_eqNeg_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_eqNeg_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_eqNeg_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullKind_default;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullKind;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullAlt_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullAlt_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullAlt_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullAlt;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_orHull_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_orHull_elim(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_ctorIdx___impl(uint8_t v_x_50_){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_box(v_x_50_);
v___x_52_ = lean_obj_tag_nat(v___x_51_);
lean_dec(v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_ctorIdx___impl___boxed(lean_object* v_x_53_){
_start:
{
uint8_t v_x_4__boxed_54_; lean_object* v_res_55_; 
v_x_4__boxed_54_ = lean_unbox(v_x_53_);
v_res_55_ = l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_ctorIdx___impl(v_x_4__boxed_54_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_ctorElim___redArg(lean_object* v_k_56_){
_start:
{
lean_inc(v_k_56_);
return v_k_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_ctorElim___redArg___boxed(lean_object* v_k_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_ctorElim___redArg(v_k_57_);
lean_dec(v_k_57_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_ctorElim(lean_object* v_motive_59_, lean_object* v_ctorIdx_60_, uint8_t v_t_61_, lean_object* v_h_62_, lean_object* v_k_63_){
_start:
{
lean_inc(v_k_63_);
return v_k_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_ctorElim___boxed(lean_object* v_motive_64_, lean_object* v_ctorIdx_65_, lean_object* v_t_66_, lean_object* v_h_67_, lean_object* v_k_68_){
_start:
{
uint8_t v_t_boxed_69_; lean_object* v_res_70_; 
v_t_boxed_69_ = lean_unbox(v_t_66_);
v_res_70_ = l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_ctorElim(v_motive_64_, v_ctorIdx_65_, v_t_boxed_69_, v_h_67_, v_k_68_);
lean_dec(v_k_68_);
lean_dec(v_ctorIdx_65_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_le_elim___redArg(lean_object* v_le_71_){
_start:
{
lean_inc(v_le_71_);
return v_le_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_le_elim___redArg___boxed(lean_object* v_le_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_le_elim___redArg(v_le_72_);
lean_dec(v_le_72_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_le_elim(lean_object* v_motive_74_, uint8_t v_t_75_, lean_object* v_h_76_, lean_object* v_le_77_){
_start:
{
lean_inc(v_le_77_);
return v_le_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_le_elim___boxed(lean_object* v_motive_78_, lean_object* v_t_79_, lean_object* v_h_80_, lean_object* v_le_81_){
_start:
{
uint8_t v_t_boxed_82_; lean_object* v_res_83_; 
v_t_boxed_82_ = lean_unbox(v_t_79_);
v_res_83_ = l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_le_elim(v_motive_78_, v_t_boxed_82_, v_h_80_, v_le_81_);
lean_dec(v_le_81_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_eq_elim___redArg(lean_object* v_eq_84_){
_start:
{
lean_inc(v_eq_84_);
return v_eq_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_eq_elim___redArg___boxed(lean_object* v_eq_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_eq_elim___redArg(v_eq_85_);
lean_dec(v_eq_85_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_eq_elim(lean_object* v_motive_87_, uint8_t v_t_88_, lean_object* v_h_89_, lean_object* v_eq_90_){
_start:
{
lean_inc(v_eq_90_);
return v_eq_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_eq_elim___boxed(lean_object* v_motive_91_, lean_object* v_t_92_, lean_object* v_h_93_, lean_object* v_eq_94_){
_start:
{
uint8_t v_t_boxed_95_; lean_object* v_res_96_; 
v_t_boxed_95_ = lean_unbox(v_t_92_);
v_res_96_ = l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_eq_elim(v_motive_91_, v_t_boxed_95_, v_h_93_, v_eq_94_);
lean_dec(v_eq_94_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_eqNeg_elim___redArg(lean_object* v_eqNeg_97_){
_start:
{
lean_inc(v_eqNeg_97_);
return v_eqNeg_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_eqNeg_elim___redArg___boxed(lean_object* v_eqNeg_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_eqNeg_elim___redArg(v_eqNeg_98_);
lean_dec(v_eqNeg_98_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_eqNeg_elim(lean_object* v_motive_100_, uint8_t v_t_101_, lean_object* v_h_102_, lean_object* v_eqNeg_103_){
_start:
{
lean_inc(v_eqNeg_103_);
return v_eqNeg_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_eqNeg_elim___boxed(lean_object* v_motive_104_, lean_object* v_t_105_, lean_object* v_h_106_, lean_object* v_eqNeg_107_){
_start:
{
uint8_t v_t_boxed_108_; lean_object* v_res_109_; 
v_t_boxed_108_ = lean_unbox(v_t_105_);
v_res_109_ = l_Lean_Meta_Grind_Arith_Cutsat_OrHullKind_eqNeg_elim(v_motive_104_, v_t_boxed_108_, v_h_106_, v_eqNeg_107_);
lean_dec(v_eqNeg_107_);
return v_res_109_;
}
}
static uint8_t _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullKind_default(void){
_start:
{
uint8_t v___x_110_; 
v___x_110_ = 0;
return v___x_110_;
}
}
static uint8_t _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullKind(void){
_start:
{
uint8_t v___x_111_; 
v___x_111_ = 0;
return v___x_111_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullAlt_default___closed__0(void){
_start:
{
lean_object* v___x_112_; uint8_t v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_112_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0);
v___x_113_ = 0;
v___x_114_ = l_Int_Internal_Linear_instInhabitedExpr_default;
v___x_115_ = lean_box(0);
v___x_116_ = lean_box(0);
v___x_117_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set(v___x_117_, 1, v___x_115_);
lean_ctor_set(v___x_117_, 2, v___x_114_);
lean_ctor_set(v___x_117_, 3, v___x_114_);
lean_ctor_set(v___x_117_, 4, v___x_112_);
lean_ctor_set_uint8(v___x_117_, sizeof(void*)*5, v___x_113_);
return v___x_117_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullAlt_default(void){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullAlt_default___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullAlt_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullAlt_default___closed__0);
return v___x_118_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullAlt(void){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullAlt_default;
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorIdx___impl(lean_object* v_x_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = lean_obj_tag_nat(v_x_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorIdx___impl___boxed(lean_object* v_x_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorIdx___impl(v_x_122_);
lean_dec_ref(v_x_122_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(lean_object* v_t_124_, lean_object* v_k_125_){
_start:
{
switch(lean_obj_tag(v_t_124_))
{
case 0:
{
lean_object* v_a_126_; lean_object* v_zero_127_; lean_object* v___x_128_; 
v_a_126_ = lean_ctor_get(v_t_124_, 0);
lean_inc_ref(v_a_126_);
v_zero_127_ = lean_ctor_get(v_t_124_, 1);
lean_inc_ref(v_zero_127_);
lean_dec_ref_known(v_t_124_, 2);
v___x_128_ = lean_apply_2(v_k_125_, v_a_126_, v_zero_127_);
return v___x_128_;
}
case 1:
{
lean_object* v_a_129_; lean_object* v_b_130_; lean_object* v_p_u2081_131_; lean_object* v_p_u2082_132_; lean_object* v___x_133_; 
v_a_129_ = lean_ctor_get(v_t_124_, 0);
lean_inc_ref(v_a_129_);
v_b_130_ = lean_ctor_get(v_t_124_, 1);
lean_inc_ref(v_b_130_);
v_p_u2081_131_ = lean_ctor_get(v_t_124_, 2);
lean_inc_ref(v_p_u2081_131_);
v_p_u2082_132_ = lean_ctor_get(v_t_124_, 3);
lean_inc_ref(v_p_u2082_132_);
lean_dec_ref_known(v_t_124_, 4);
v___x_133_ = lean_apply_4(v_k_125_, v_a_129_, v_b_130_, v_p_u2081_131_, v_p_u2082_132_);
return v___x_133_;
}
case 2:
{
lean_object* v_a_134_; lean_object* v_b_135_; lean_object* v_toIntThm_136_; lean_object* v_lhs_137_; lean_object* v_rhs_138_; lean_object* v___x_139_; 
v_a_134_ = lean_ctor_get(v_t_124_, 0);
lean_inc_ref(v_a_134_);
v_b_135_ = lean_ctor_get(v_t_124_, 1);
lean_inc_ref(v_b_135_);
v_toIntThm_136_ = lean_ctor_get(v_t_124_, 2);
lean_inc_ref(v_toIntThm_136_);
v_lhs_137_ = lean_ctor_get(v_t_124_, 3);
lean_inc_ref(v_lhs_137_);
v_rhs_138_ = lean_ctor_get(v_t_124_, 4);
lean_inc_ref(v_rhs_138_);
lean_dec_ref_known(v_t_124_, 5);
v___x_139_ = lean_apply_5(v_k_125_, v_a_134_, v_b_135_, v_toIntThm_136_, v_lhs_137_, v_rhs_138_);
return v___x_139_;
}
case 3:
{
lean_object* v_h_140_; lean_object* v_lhs_141_; lean_object* v_rhs_142_; lean_object* v___x_143_; 
v_h_140_ = lean_ctor_get(v_t_124_, 0);
lean_inc_ref(v_h_140_);
v_lhs_141_ = lean_ctor_get(v_t_124_, 1);
lean_inc_ref(v_lhs_141_);
v_rhs_142_ = lean_ctor_get(v_t_124_, 2);
lean_inc_ref(v_rhs_142_);
lean_dec_ref_known(v_t_124_, 3);
v___x_143_ = lean_apply_3(v_k_125_, v_h_140_, v_lhs_141_, v_rhs_142_);
return v___x_143_;
}
case 4:
{
lean_object* v_e_144_; lean_object* v_p_145_; lean_object* v___x_146_; 
v_e_144_ = lean_ctor_get(v_t_124_, 0);
lean_inc_ref(v_e_144_);
v_p_145_ = lean_ctor_get(v_t_124_, 1);
lean_inc_ref(v_p_145_);
lean_dec_ref_known(v_t_124_, 2);
v___x_146_ = lean_apply_2(v_k_125_, v_e_144_, v_p_145_);
return v___x_146_;
}
case 5:
{
lean_object* v_h_147_; lean_object* v_x_148_; lean_object* v_e_x27_149_; lean_object* v___x_150_; 
v_h_147_ = lean_ctor_get(v_t_124_, 0);
lean_inc_ref(v_h_147_);
v_x_148_ = lean_ctor_get(v_t_124_, 1);
lean_inc(v_x_148_);
v_e_x27_149_ = lean_ctor_get(v_t_124_, 2);
lean_inc_ref(v_e_x27_149_);
lean_dec_ref_known(v_t_124_, 3);
v___x_150_ = lean_apply_3(v_k_125_, v_h_147_, v_x_148_, v_e_x27_149_);
return v___x_150_;
}
case 8:
{
lean_object* v_x_151_; lean_object* v_c_u2081_152_; lean_object* v_c_u2082_153_; lean_object* v___x_154_; 
v_x_151_ = lean_ctor_get(v_t_124_, 0);
lean_inc(v_x_151_);
v_c_u2081_152_ = lean_ctor_get(v_t_124_, 1);
lean_inc_ref(v_c_u2081_152_);
v_c_u2082_153_ = lean_ctor_get(v_t_124_, 2);
lean_inc_ref(v_c_u2082_153_);
lean_dec_ref_known(v_t_124_, 3);
v___x_154_ = lean_apply_3(v_k_125_, v_x_151_, v_c_u2081_152_, v_c_u2082_153_);
return v___x_154_;
}
case 9:
{
lean_object* v_c_u2081_155_; lean_object* v_c_u2082_156_; lean_object* v___x_157_; 
v_c_u2081_155_ = lean_ctor_get(v_t_124_, 0);
lean_inc_ref(v_c_u2081_155_);
v_c_u2082_156_ = lean_ctor_get(v_t_124_, 1);
lean_inc_ref(v_c_u2082_156_);
lean_dec_ref_known(v_t_124_, 2);
v___x_157_ = lean_apply_2(v_k_125_, v_c_u2081_155_, v_c_u2082_156_);
return v___x_157_;
}
case 11:
{
lean_object* v_c_158_; lean_object* v_e_159_; lean_object* v_x_160_; lean_object* v_t_161_; lean_object* v___x_162_; 
v_c_158_ = lean_ctor_get(v_t_124_, 0);
lean_inc_ref(v_c_158_);
v_e_159_ = lean_ctor_get(v_t_124_, 1);
lean_inc_ref(v_e_159_);
v_x_160_ = lean_ctor_get(v_t_124_, 2);
lean_inc(v_x_160_);
v_t_161_ = lean_ctor_get(v_t_124_, 3);
lean_inc_ref(v_t_161_);
lean_dec_ref_known(v_t_124_, 4);
v___x_162_ = lean_apply_4(v_k_125_, v_c_158_, v_e_159_, v_x_160_, v_t_161_);
return v___x_162_;
}
case 13:
{
lean_object* v_c_163_; lean_object* v_e_164_; lean_object* v_p_165_; lean_object* v___x_166_; 
v_c_163_ = lean_ctor_get(v_t_124_, 0);
lean_inc_ref(v_c_163_);
v_e_164_ = lean_ctor_get(v_t_124_, 1);
lean_inc_ref(v_e_164_);
v_p_165_ = lean_ctor_get(v_t_124_, 2);
lean_inc_ref(v_p_165_);
lean_dec_ref_known(v_t_124_, 3);
v___x_166_ = lean_apply_3(v_k_125_, v_c_163_, v_e_164_, v_p_165_);
return v___x_166_;
}
case 14:
{
lean_object* v_e_167_; lean_object* v_p_168_; lean_object* v_re_169_; lean_object* v_rp_170_; lean_object* v_p_x27_171_; lean_object* v___x_172_; 
v_e_167_ = lean_ctor_get(v_t_124_, 0);
lean_inc_ref(v_e_167_);
v_p_168_ = lean_ctor_get(v_t_124_, 1);
lean_inc_ref(v_p_168_);
v_re_169_ = lean_ctor_get(v_t_124_, 2);
lean_inc_ref(v_re_169_);
v_rp_170_ = lean_ctor_get(v_t_124_, 3);
lean_inc_ref(v_rp_170_);
v_p_x27_171_ = lean_ctor_get(v_t_124_, 4);
lean_inc_ref(v_p_x27_171_);
lean_dec_ref_known(v_t_124_, 5);
v___x_172_ = lean_apply_5(v_k_125_, v_e_167_, v_p_168_, v_re_169_, v_rp_170_, v_p_x27_171_);
return v___x_172_;
}
case 15:
{
lean_object* v_h_173_; lean_object* v_x_174_; lean_object* v_e_x27_175_; lean_object* v_p_176_; lean_object* v_re_177_; lean_object* v_rp_178_; lean_object* v_p_x27_179_; lean_object* v___x_180_; 
v_h_173_ = lean_ctor_get(v_t_124_, 0);
lean_inc_ref(v_h_173_);
v_x_174_ = lean_ctor_get(v_t_124_, 1);
lean_inc(v_x_174_);
v_e_x27_175_ = lean_ctor_get(v_t_124_, 2);
lean_inc_ref(v_e_x27_175_);
v_p_176_ = lean_ctor_get(v_t_124_, 3);
lean_inc_ref(v_p_176_);
v_re_177_ = lean_ctor_get(v_t_124_, 4);
lean_inc_ref(v_re_177_);
v_rp_178_ = lean_ctor_get(v_t_124_, 5);
lean_inc_ref(v_rp_178_);
v_p_x27_179_ = lean_ctor_get(v_t_124_, 6);
lean_inc_ref(v_p_x27_179_);
lean_dec_ref_known(v_t_124_, 7);
v___x_180_ = lean_apply_7(v_k_125_, v_h_173_, v_x_174_, v_e_x27_175_, v_p_176_, v_re_177_, v_rp_178_, v_p_x27_179_);
return v___x_180_;
}
case 16:
{
lean_object* v_a_x3f_181_; lean_object* v_cs_182_; lean_object* v___x_183_; 
v_a_x3f_181_ = lean_ctor_get(v_t_124_, 0);
lean_inc(v_a_x3f_181_);
v_cs_182_ = lean_ctor_get(v_t_124_, 1);
lean_inc_ref(v_cs_182_);
lean_dec_ref_known(v_t_124_, 2);
v___x_183_ = lean_apply_2(v_k_125_, v_a_x3f_181_, v_cs_182_);
return v___x_183_;
}
case 17:
{
lean_object* v_k_184_; lean_object* v_y_x3f_185_; lean_object* v_c_186_; lean_object* v___x_187_; 
v_k_184_ = lean_ctor_get(v_t_124_, 0);
lean_inc(v_k_184_);
v_y_x3f_185_ = lean_ctor_get(v_t_124_, 1);
lean_inc(v_y_x3f_185_);
v_c_186_ = lean_ctor_get(v_t_124_, 2);
lean_inc_ref(v_c_186_);
lean_dec_ref_known(v_t_124_, 3);
v___x_187_ = lean_apply_3(v_k_125_, v_k_184_, v_y_x3f_185_, v_c_186_);
return v___x_187_;
}
case 18:
{
lean_object* v_k_188_; lean_object* v_y_x3f_189_; lean_object* v_c_190_; lean_object* v___x_191_; 
v_k_188_ = lean_ctor_get(v_t_124_, 0);
lean_inc(v_k_188_);
v_y_x3f_189_ = lean_ctor_get(v_t_124_, 1);
lean_inc(v_y_x3f_189_);
v_c_190_ = lean_ctor_get(v_t_124_, 2);
lean_inc_ref(v_c_190_);
lean_dec_ref_known(v_t_124_, 3);
v___x_191_ = lean_apply_3(v_k_125_, v_k_188_, v_y_x3f_189_, v_c_190_);
return v___x_191_;
}
case 19:
{
lean_object* v_ka_192_; lean_object* v_ca_x3f_193_; lean_object* v_kb_194_; lean_object* v_cb_x3f_195_; lean_object* v___x_196_; 
v_ka_192_ = lean_ctor_get(v_t_124_, 0);
lean_inc(v_ka_192_);
v_ca_x3f_193_ = lean_ctor_get(v_t_124_, 1);
lean_inc(v_ca_x3f_193_);
v_kb_194_ = lean_ctor_get(v_t_124_, 2);
lean_inc(v_kb_194_);
v_cb_x3f_195_ = lean_ctor_get(v_t_124_, 3);
lean_inc(v_cb_x3f_195_);
lean_dec_ref_known(v_t_124_, 4);
v___x_196_ = lean_apply_4(v_k_125_, v_ka_192_, v_ca_x3f_193_, v_kb_194_, v_cb_x3f_195_);
return v___x_196_;
}
default: 
{
lean_object* v_c_197_; lean_object* v___x_198_; 
v_c_197_ = lean_ctor_get(v_t_124_, 0);
lean_inc_ref(v_c_197_);
lean_dec_ref(v_t_124_);
v___x_198_ = lean_apply_1(v_k_125_, v_c_197_);
return v___x_198_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim(lean_object* v_motive__2_199_, lean_object* v_ctorIdx_200_, lean_object* v_t_201_, lean_object* v_h_202_, lean_object* v_k_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_201_, v_k_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___boxed(lean_object* v_motive__2_205_, lean_object* v_ctorIdx_206_, lean_object* v_t_207_, lean_object* v_h_208_, lean_object* v_k_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim(v_motive__2_205_, v_ctorIdx_206_, v_t_207_, v_h_208_, v_k_209_);
lean_dec(v_ctorIdx_206_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core0_elim___redArg(lean_object* v_t_211_, lean_object* v_core0_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_211_, v_core0_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core0_elim(lean_object* v_motive__2_214_, lean_object* v_t_215_, lean_object* v_h_216_, lean_object* v_core0_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_215_, v_core0_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core_elim___redArg(lean_object* v_t_219_, lean_object* v_core_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_219_, v_core_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core_elim(lean_object* v_motive__2_222_, lean_object* v_t_223_, lean_object* v_h_224_, lean_object* v_core_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_223_, v_core_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_coreToInt_elim___redArg(lean_object* v_t_227_, lean_object* v_coreToInt_228_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_227_, v_coreToInt_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_coreToInt_elim(lean_object* v_motive__2_230_, lean_object* v_t_231_, lean_object* v_h_232_, lean_object* v_coreToInt_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_231_, v_coreToInt_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_hyp_elim___redArg(lean_object* v_t_235_, lean_object* v_hyp_236_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_235_, v_hyp_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_hyp_elim(lean_object* v_motive__2_238_, lean_object* v_t_239_, lean_object* v_h_240_, lean_object* v_hyp_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_239_, v_hyp_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defn_elim___redArg(lean_object* v_t_243_, lean_object* v_defn_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_243_, v_defn_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defn_elim(lean_object* v_motive__2_246_, lean_object* v_t_247_, lean_object* v_h_248_, lean_object* v_defn_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_247_, v_defn_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnExpr_elim___redArg(lean_object* v_t_251_, lean_object* v_defnExpr_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_251_, v_defnExpr_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnExpr_elim(lean_object* v_motive__2_254_, lean_object* v_t_255_, lean_object* v_h_256_, lean_object* v_defnExpr_257_){
_start:
{
lean_object* v___x_258_; 
v___x_258_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_255_, v_defnExpr_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_norm_elim___redArg(lean_object* v_t_259_, lean_object* v_norm_260_){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_259_, v_norm_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_norm_elim(lean_object* v_motive__2_262_, lean_object* v_t_263_, lean_object* v_h_264_, lean_object* v_norm_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_263_, v_norm_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_divCoeffs_elim___redArg(lean_object* v_t_267_, lean_object* v_divCoeffs_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_267_, v_divCoeffs_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_divCoeffs_elim(lean_object* v_motive__2_270_, lean_object* v_t_271_, lean_object* v_h_272_, lean_object* v_divCoeffs_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_271_, v_divCoeffs_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_subst_elim___redArg(lean_object* v_t_275_, lean_object* v_subst_276_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_275_, v_subst_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_subst_elim(lean_object* v_motive__2_278_, lean_object* v_t_279_, lean_object* v_h_280_, lean_object* v_subst_281_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_279_, v_subst_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofLeGe_elim___redArg(lean_object* v_t_283_, lean_object* v_ofLeGe_284_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_283_, v_ofLeGe_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofLeGe_elim(lean_object* v_motive__2_286_, lean_object* v_t_287_, lean_object* v_h_288_, lean_object* v_ofLeGe_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_287_, v_ofLeGe_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofZeroDvd_elim___redArg(lean_object* v_t_291_, lean_object* v_ofZeroDvd_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_291_, v_ofZeroDvd_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofZeroDvd_elim(lean_object* v_motive__2_294_, lean_object* v_t_295_, lean_object* v_h_296_, lean_object* v_ofZeroDvd_297_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_295_, v_ofZeroDvd_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofDvdDiv_elim___redArg(lean_object* v_t_299_, lean_object* v_ofDvdDiv_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_299_, v_ofDvdDiv_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofDvdDiv_elim(lean_object* v_motive__2_302_, lean_object* v_t_303_, lean_object* v_h_304_, lean_object* v_ofDvdDiv_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_303_, v_ofDvdDiv_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_reorder_elim___redArg(lean_object* v_t_307_, lean_object* v_reorder_308_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_307_, v_reorder_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_reorder_elim(lean_object* v_motive__2_310_, lean_object* v_t_311_, lean_object* v_h_312_, lean_object* v_reorder_313_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_311_, v_reorder_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_commRingNorm_elim___redArg(lean_object* v_t_315_, lean_object* v_commRingNorm_316_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_315_, v_commRingNorm_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_commRingNorm_elim(lean_object* v_motive__2_318_, lean_object* v_t_319_, lean_object* v_h_320_, lean_object* v_commRingNorm_321_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_319_, v_commRingNorm_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnCommRing_elim___redArg(lean_object* v_t_323_, lean_object* v_defnCommRing_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_323_, v_defnCommRing_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnCommRing_elim(lean_object* v_motive__2_326_, lean_object* v_t_327_, lean_object* v_h_328_, lean_object* v_defnCommRing_329_){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_327_, v_defnCommRing_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnExprCommRing_elim___redArg(lean_object* v_t_331_, lean_object* v_defnExprCommRing_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_331_, v_defnExprCommRing_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnExprCommRing_elim(lean_object* v_motive__2_334_, lean_object* v_t_335_, lean_object* v_h_336_, lean_object* v_defnExprCommRing_337_){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_335_, v_defnExprCommRing_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mul_elim___redArg(lean_object* v_t_339_, lean_object* v_mul_340_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_339_, v_mul_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mul_elim(lean_object* v_motive__2_342_, lean_object* v_t_343_, lean_object* v_h_344_, lean_object* v_mul_345_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_343_, v_mul_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_div_elim___redArg(lean_object* v_t_347_, lean_object* v_div_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_347_, v_div_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_div_elim(lean_object* v_motive__2_350_, lean_object* v_t_351_, lean_object* v_h_352_, lean_object* v_div_353_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_351_, v_div_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mod_elim___redArg(lean_object* v_t_355_, lean_object* v_mod_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_355_, v_mod_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mod_elim(lean_object* v_motive__2_358_, lean_object* v_t_359_, lean_object* v_h_360_, lean_object* v_mod_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_359_, v_mod_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_pow_elim___redArg(lean_object* v_t_363_, lean_object* v_pow_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_363_, v_pow_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_pow_elim(lean_object* v_motive__2_366_, lean_object* v_t_367_, lean_object* v_h_368_, lean_object* v_pow_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_367_, v_pow_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorIdx___impl(lean_object* v_x_371_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = lean_obj_tag_nat(v_x_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorIdx___impl___boxed(lean_object* v_x_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorIdx___impl(v_x_373_);
lean_dec_ref(v_x_373_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(lean_object* v_t_375_, lean_object* v_k_376_){
_start:
{
if (lean_obj_tag(v_t_375_) == 0)
{
lean_object* v_h_377_; lean_object* v___x_378_; 
v_h_377_ = lean_ctor_get(v_t_375_, 0);
lean_inc(v_h_377_);
lean_dec_ref_known(v_t_375_, 1);
v___x_378_ = lean_apply_1(v_k_376_, v_h_377_);
return v___x_378_;
}
else
{
lean_object* v_hs_379_; lean_object* v_decVars_380_; lean_object* v___x_381_; 
v_hs_379_ = lean_ctor_get(v_t_375_, 0);
lean_inc_ref(v_hs_379_);
v_decVars_380_ = lean_ctor_get(v_t_375_, 1);
lean_inc_ref(v_decVars_380_);
lean_dec_ref_known(v_t_375_, 2);
v___x_381_ = lean_apply_2(v_k_376_, v_hs_379_, v_decVars_380_);
return v___x_381_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim(lean_object* v_motive__6_382_, lean_object* v_ctorIdx_383_, lean_object* v_t_384_, lean_object* v_h_385_, lean_object* v_k_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_384_, v_k_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___boxed(lean_object* v_motive__6_388_, lean_object* v_ctorIdx_389_, lean_object* v_t_390_, lean_object* v_h_391_, lean_object* v_k_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim(v_motive__6_388_, v_ctorIdx_389_, v_t_390_, v_h_391_, v_k_392_);
lean_dec(v_ctorIdx_389_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_dec_elim___redArg(lean_object* v_t_394_, lean_object* v_dec_395_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_394_, v_dec_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_dec_elim(lean_object* v_motive__6_397_, lean_object* v_t_398_, lean_object* v_h_399_, lean_object* v_dec_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_398_, v_dec_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_last_elim___redArg(lean_object* v_t_402_, lean_object* v_last_403_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_402_, v_last_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_last_elim(lean_object* v_motive__6_405_, lean_object* v_t_406_, lean_object* v_h_407_, lean_object* v_last_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_406_, v_last_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorIdx___impl(lean_object* v_x_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = lean_obj_tag_nat(v_x_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorIdx___impl___boxed(lean_object* v_x_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorIdx___impl(v_x_412_);
lean_dec_ref(v_x_412_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(lean_object* v_t_414_, lean_object* v_k_415_){
_start:
{
switch(lean_obj_tag(v_t_414_))
{
case 1:
{
lean_object* v_e_416_; lean_object* v_thm_417_; lean_object* v_d_418_; lean_object* v_a_419_; lean_object* v___x_420_; 
v_e_416_ = lean_ctor_get(v_t_414_, 0);
lean_inc_ref(v_e_416_);
v_thm_417_ = lean_ctor_get(v_t_414_, 1);
lean_inc_ref(v_thm_417_);
v_d_418_ = lean_ctor_get(v_t_414_, 2);
lean_inc(v_d_418_);
v_a_419_ = lean_ctor_get(v_t_414_, 3);
lean_inc_ref(v_a_419_);
lean_dec_ref_known(v_t_414_, 4);
v___x_420_ = lean_apply_4(v_k_415_, v_e_416_, v_thm_417_, v_d_418_, v_a_419_);
return v___x_420_;
}
case 4:
{
lean_object* v_c_421_; lean_object* v_a_422_; lean_object* v___x_423_; 
v_c_421_ = lean_ctor_get(v_t_414_, 0);
lean_inc_ref(v_c_421_);
v_a_422_ = lean_ctor_get(v_t_414_, 1);
lean_inc(v_a_422_);
lean_dec_ref_known(v_t_414_, 2);
v___x_423_ = lean_apply_2(v_k_415_, v_c_421_, v_a_422_);
return v___x_423_;
}
case 5:
{
lean_object* v_c_u2081_424_; lean_object* v_c_u2082_425_; lean_object* v___x_426_; 
v_c_u2081_424_ = lean_ctor_get(v_t_414_, 0);
lean_inc_ref(v_c_u2081_424_);
v_c_u2082_425_ = lean_ctor_get(v_t_414_, 1);
lean_inc_ref(v_c_u2082_425_);
lean_dec_ref_known(v_t_414_, 2);
v___x_426_ = lean_apply_2(v_k_415_, v_c_u2081_424_, v_c_u2082_425_);
return v___x_426_;
}
case 6:
{
lean_object* v_c_u2081_427_; lean_object* v_c_u2082_428_; lean_object* v___x_429_; 
v_c_u2081_427_ = lean_ctor_get(v_t_414_, 0);
lean_inc_ref(v_c_u2081_427_);
v_c_u2082_428_ = lean_ctor_get(v_t_414_, 1);
lean_inc_ref(v_c_u2082_428_);
lean_dec_ref_known(v_t_414_, 2);
v___x_429_ = lean_apply_2(v_k_415_, v_c_u2081_427_, v_c_u2082_428_);
return v___x_429_;
}
case 9:
{
lean_object* v_x_430_; lean_object* v_c_u2081_431_; lean_object* v_c_u2082_432_; lean_object* v___x_433_; 
v_x_430_ = lean_ctor_get(v_t_414_, 0);
lean_inc(v_x_430_);
v_c_u2081_431_ = lean_ctor_get(v_t_414_, 1);
lean_inc_ref(v_c_u2081_431_);
v_c_u2082_432_ = lean_ctor_get(v_t_414_, 2);
lean_inc_ref(v_c_u2082_432_);
lean_dec_ref_known(v_t_414_, 3);
v___x_433_ = lean_apply_3(v_k_415_, v_x_430_, v_c_u2081_431_, v_c_u2082_432_);
return v___x_433_;
}
case 13:
{
lean_object* v_c_434_; lean_object* v_e_435_; lean_object* v_p_436_; lean_object* v___x_437_; 
v_c_434_ = lean_ctor_get(v_t_414_, 0);
lean_inc_ref(v_c_434_);
v_e_435_ = lean_ctor_get(v_t_414_, 1);
lean_inc_ref(v_e_435_);
v_p_436_ = lean_ctor_get(v_t_414_, 2);
lean_inc_ref(v_p_436_);
lean_dec_ref_known(v_t_414_, 3);
v___x_437_ = lean_apply_3(v_k_415_, v_c_434_, v_e_435_, v_p_436_);
return v___x_437_;
}
default: 
{
lean_object* v_e_438_; lean_object* v___x_439_; 
v_e_438_ = lean_ctor_get(v_t_414_, 0);
lean_inc_ref(v_e_438_);
lean_dec_ref(v_t_414_);
v___x_439_ = lean_apply_1(v_k_415_, v_e_438_);
return v___x_439_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim(lean_object* v_motive__7_440_, lean_object* v_ctorIdx_441_, lean_object* v_t_442_, lean_object* v_h_443_, lean_object* v_k_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_442_, v_k_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___boxed(lean_object* v_motive__7_446_, lean_object* v_ctorIdx_447_, lean_object* v_t_448_, lean_object* v_h_449_, lean_object* v_k_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim(v_motive__7_446_, v_ctorIdx_447_, v_t_448_, v_h_449_, v_k_450_);
lean_dec(v_ctorIdx_447_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_core_elim___redArg(lean_object* v_t_452_, lean_object* v_core_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_452_, v_core_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_core_elim(lean_object* v_motive__7_455_, lean_object* v_t_456_, lean_object* v_h_457_, lean_object* v_core_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_456_, v_core_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_coreOfNat_elim___redArg(lean_object* v_t_460_, lean_object* v_coreOfNat_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_460_, v_coreOfNat_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_coreOfNat_elim(lean_object* v_motive__7_463_, lean_object* v_t_464_, lean_object* v_h_465_, lean_object* v_coreOfNat_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_464_, v_coreOfNat_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_norm_elim___redArg(lean_object* v_t_468_, lean_object* v_norm_469_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_468_, v_norm_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_norm_elim(lean_object* v_motive__7_471_, lean_object* v_t_472_, lean_object* v_h_473_, lean_object* v_norm_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_472_, v_norm_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_divCoeffs_elim___redArg(lean_object* v_t_476_, lean_object* v_divCoeffs_477_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_476_, v_divCoeffs_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_divCoeffs_elim(lean_object* v_motive__7_479_, lean_object* v_t_480_, lean_object* v_h_481_, lean_object* v_divCoeffs_482_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_480_, v_divCoeffs_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_bmodCoeffs_elim___redArg(lean_object* v_t_484_, lean_object* v_bmodCoeffs_485_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_484_, v_bmodCoeffs_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_bmodCoeffs_elim(lean_object* v_motive__7_487_, lean_object* v_t_488_, lean_object* v_h_489_, lean_object* v_bmodCoeffs_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_488_, v_bmodCoeffs_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveCombine_elim___redArg(lean_object* v_t_492_, lean_object* v_solveCombine_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_492_, v_solveCombine_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveCombine_elim(lean_object* v_motive__7_495_, lean_object* v_t_496_, lean_object* v_h_497_, lean_object* v_solveCombine_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_496_, v_solveCombine_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveElim_elim___redArg(lean_object* v_t_500_, lean_object* v_solveElim_501_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_500_, v_solveElim_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveElim_elim(lean_object* v_motive__7_503_, lean_object* v_t_504_, lean_object* v_h_505_, lean_object* v_solveElim_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_504_, v_solveElim_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_elim_elim___redArg(lean_object* v_t_508_, lean_object* v_elim_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_508_, v_elim_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_elim_elim(lean_object* v_motive__7_511_, lean_object* v_t_512_, lean_object* v_h_513_, lean_object* v_elim_514_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_512_, v_elim_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ofEqZero_elim___redArg(lean_object* v_t_516_, lean_object* v_ofEqZero_517_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_516_, v_ofEqZero_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ofEqZero_elim(lean_object* v_motive__7_519_, lean_object* v_t_520_, lean_object* v_h_521_, lean_object* v_ofEqZero_522_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_520_, v_ofEqZero_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_subst_elim___redArg(lean_object* v_t_524_, lean_object* v_subst_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_524_, v_subst_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_subst_elim(lean_object* v_motive__7_527_, lean_object* v_t_528_, lean_object* v_h_529_, lean_object* v_subst_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_528_, v_subst_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2081_elim___redArg(lean_object* v_t_532_, lean_object* v_cooper_u2081_533_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_532_, v_cooper_u2081_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2081_elim(lean_object* v_motive__7_535_, lean_object* v_t_536_, lean_object* v_h_537_, lean_object* v_cooper_u2081_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_536_, v_cooper_u2081_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2082_elim___redArg(lean_object* v_t_540_, lean_object* v_cooper_u2082_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_540_, v_cooper_u2082_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2082_elim(lean_object* v_motive__7_543_, lean_object* v_t_544_, lean_object* v_h_545_, lean_object* v_cooper_u2082_546_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_544_, v_cooper_u2082_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_reorder_elim___redArg(lean_object* v_t_548_, lean_object* v_reorder_549_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_548_, v_reorder_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_reorder_elim(lean_object* v_motive__7_551_, lean_object* v_t_552_, lean_object* v_h_553_, lean_object* v_reorder_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_552_, v_reorder_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_commRingNorm_elim___redArg(lean_object* v_t_556_, lean_object* v_commRingNorm_557_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_556_, v_commRingNorm_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_commRingNorm_elim(lean_object* v_motive__7_559_, lean_object* v_t_560_, lean_object* v_h_561_, lean_object* v_commRingNorm_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_560_, v_commRingNorm_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorIdx___impl(lean_object* v_x_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = lean_obj_tag_nat(v_x_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorIdx___impl___boxed(lean_object* v_x_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorIdx___impl(v_x_566_);
lean_dec_ref(v_x_566_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(lean_object* v_t_568_, lean_object* v_k_569_){
_start:
{
switch(lean_obj_tag(v_t_568_))
{
case 1:
{
lean_object* v_e_570_; lean_object* v_p_571_; lean_object* v___x_572_; 
v_e_570_ = lean_ctor_get(v_t_568_, 0);
lean_inc_ref(v_e_570_);
v_p_571_ = lean_ctor_get(v_t_568_, 1);
lean_inc_ref(v_p_571_);
lean_dec_ref_known(v_t_568_, 2);
v___x_572_ = lean_apply_2(v_k_569_, v_e_570_, v_p_571_);
return v___x_572_;
}
case 2:
{
lean_object* v_e_573_; uint8_t v_pos_574_; lean_object* v_toIntThm_575_; lean_object* v_lhs_576_; lean_object* v_rhs_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v_e_573_ = lean_ctor_get(v_t_568_, 0);
lean_inc_ref(v_e_573_);
v_pos_574_ = lean_ctor_get_uint8(v_t_568_, sizeof(void*)*4);
v_toIntThm_575_ = lean_ctor_get(v_t_568_, 1);
lean_inc_ref(v_toIntThm_575_);
v_lhs_576_ = lean_ctor_get(v_t_568_, 2);
lean_inc_ref(v_lhs_576_);
v_rhs_577_ = lean_ctor_get(v_t_568_, 3);
lean_inc_ref(v_rhs_577_);
lean_dec_ref_known(v_t_568_, 4);
v___x_578_ = lean_box(v_pos_574_);
v___x_579_ = lean_apply_5(v_k_569_, v_e_573_, v___x_578_, v_toIntThm_575_, v_lhs_576_, v_rhs_577_);
return v___x_579_;
}
case 3:
{
lean_object* v_e_580_; uint8_t v_pos_581_; lean_object* v_lhs_582_; lean_object* v_rhs_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v_e_580_ = lean_ctor_get(v_t_568_, 0);
lean_inc_ref(v_e_580_);
v_pos_581_ = lean_ctor_get_uint8(v_t_568_, sizeof(void*)*3);
v_lhs_582_ = lean_ctor_get(v_t_568_, 1);
lean_inc_ref(v_lhs_582_);
v_rhs_583_ = lean_ctor_get(v_t_568_, 2);
lean_inc_ref(v_rhs_583_);
lean_dec_ref_known(v_t_568_, 3);
v___x_584_ = lean_box(v_pos_581_);
v___x_585_ = lean_apply_4(v_k_569_, v_e_580_, v___x_584_, v_lhs_582_, v_rhs_583_);
return v___x_585_;
}
case 5:
{
lean_object* v_h_586_; lean_object* v_lhs_587_; lean_object* v_rhs_588_; lean_object* v___x_589_; 
v_h_586_ = lean_ctor_get(v_t_568_, 0);
lean_inc_ref(v_h_586_);
v_lhs_587_ = lean_ctor_get(v_t_568_, 1);
lean_inc_ref(v_lhs_587_);
v_rhs_588_ = lean_ctor_get(v_t_568_, 2);
lean_inc_ref(v_rhs_588_);
lean_dec_ref_known(v_t_568_, 3);
v___x_589_ = lean_apply_3(v_k_569_, v_h_586_, v_lhs_587_, v_rhs_588_);
return v___x_589_;
}
case 7:
{
lean_object* v_h_590_; lean_object* v___x_591_; 
v_h_590_ = lean_ctor_get(v_t_568_, 0);
lean_inc(v_h_590_);
lean_dec_ref_known(v_t_568_, 1);
v___x_591_ = lean_apply_1(v_k_569_, v_h_590_);
return v___x_591_;
}
case 10:
{
lean_object* v_c_u2081_592_; lean_object* v_c_u2082_593_; lean_object* v___x_594_; 
v_c_u2081_592_ = lean_ctor_get(v_t_568_, 0);
lean_inc_ref(v_c_u2081_592_);
v_c_u2082_593_ = lean_ctor_get(v_t_568_, 1);
lean_inc_ref(v_c_u2082_593_);
lean_dec_ref_known(v_t_568_, 2);
v___x_594_ = lean_apply_2(v_k_569_, v_c_u2081_592_, v_c_u2082_593_);
return v___x_594_;
}
case 11:
{
lean_object* v_c_u2081_595_; lean_object* v_c_u2082_596_; lean_object* v_k_597_; lean_object* v___x_598_; 
v_c_u2081_595_ = lean_ctor_get(v_t_568_, 0);
lean_inc_ref(v_c_u2081_595_);
v_c_u2082_596_ = lean_ctor_get(v_t_568_, 1);
lean_inc_ref(v_c_u2082_596_);
v_k_597_ = lean_ctor_get(v_t_568_, 2);
lean_inc(v_k_597_);
lean_dec_ref_known(v_t_568_, 3);
v___x_598_ = lean_apply_3(v_k_569_, v_c_u2081_595_, v_c_u2082_596_, v_k_597_);
return v___x_598_;
}
case 12:
{
lean_object* v_x_599_; lean_object* v_c_u2081_600_; lean_object* v_c_u2082_601_; lean_object* v___x_602_; 
v_x_599_ = lean_ctor_get(v_t_568_, 0);
lean_inc(v_x_599_);
v_c_u2081_600_ = lean_ctor_get(v_t_568_, 1);
lean_inc_ref(v_c_u2081_600_);
v_c_u2082_601_ = lean_ctor_get(v_t_568_, 2);
lean_inc_ref(v_c_u2082_601_);
lean_dec_ref_known(v_t_568_, 3);
v___x_602_ = lean_apply_3(v_k_569_, v_x_599_, v_c_u2081_600_, v_c_u2082_601_);
return v___x_602_;
}
case 13:
{
lean_object* v_c_u2081_603_; lean_object* v_c_u2082_604_; lean_object* v___x_605_; 
v_c_u2081_603_ = lean_ctor_get(v_t_568_, 0);
lean_inc_ref(v_c_u2081_603_);
v_c_u2082_604_ = lean_ctor_get(v_t_568_, 1);
lean_inc_ref(v_c_u2082_604_);
lean_dec_ref_known(v_t_568_, 2);
v___x_605_ = lean_apply_2(v_k_569_, v_c_u2081_603_, v_c_u2082_604_);
return v___x_605_;
}
case 14:
{
lean_object* v_c_u2081_606_; lean_object* v_decVar_607_; lean_object* v_h_608_; lean_object* v_decVars_609_; lean_object* v___x_610_; 
v_c_u2081_606_ = lean_ctor_get(v_t_568_, 0);
lean_inc_ref(v_c_u2081_606_);
v_decVar_607_ = lean_ctor_get(v_t_568_, 1);
lean_inc(v_decVar_607_);
v_h_608_ = lean_ctor_get(v_t_568_, 2);
lean_inc_ref(v_h_608_);
v_decVars_609_ = lean_ctor_get(v_t_568_, 3);
lean_inc_ref(v_decVars_609_);
lean_dec_ref_known(v_t_568_, 4);
v___x_610_ = lean_apply_4(v_k_569_, v_c_u2081_606_, v_decVar_607_, v_h_608_, v_decVars_609_);
return v___x_610_;
}
case 16:
{
lean_object* v_c_u2081_611_; lean_object* v_c_u2082_612_; lean_object* v_t_613_; lean_object* v_g_614_; lean_object* v___x_615_; 
v_c_u2081_611_ = lean_ctor_get(v_t_568_, 0);
lean_inc_ref(v_c_u2081_611_);
v_c_u2082_612_ = lean_ctor_get(v_t_568_, 1);
lean_inc_ref(v_c_u2082_612_);
v_t_613_ = lean_ctor_get(v_t_568_, 2);
lean_inc(v_t_613_);
v_g_614_ = lean_ctor_get(v_t_568_, 3);
lean_inc(v_g_614_);
lean_dec_ref_known(v_t_568_, 4);
v___x_615_ = lean_apply_4(v_k_569_, v_c_u2081_611_, v_c_u2082_612_, v_t_613_, v_g_614_);
return v___x_615_;
}
case 17:
{
lean_object* v_e_616_; lean_object* v_alts_617_; lean_object* v___x_618_; 
v_e_616_ = lean_ctor_get(v_t_568_, 0);
lean_inc_ref(v_e_616_);
v_alts_617_ = lean_ctor_get(v_t_568_, 1);
lean_inc_ref(v_alts_617_);
lean_dec_ref_known(v_t_568_, 2);
v___x_618_ = lean_apply_2(v_k_569_, v_e_616_, v_alts_617_);
return v___x_618_;
}
case 19:
{
lean_object* v_c_619_; lean_object* v_e_620_; lean_object* v_p_621_; lean_object* v___x_622_; 
v_c_619_ = lean_ctor_get(v_t_568_, 0);
lean_inc_ref(v_c_619_);
v_e_620_ = lean_ctor_get(v_t_568_, 1);
lean_inc_ref(v_e_620_);
v_p_621_ = lean_ctor_get(v_t_568_, 2);
lean_inc_ref(v_p_621_);
lean_dec_ref_known(v_t_568_, 3);
v___x_622_ = lean_apply_3(v_k_569_, v_c_619_, v_e_620_, v_p_621_);
return v___x_622_;
}
default: 
{
lean_object* v_e_623_; lean_object* v___x_624_; 
v_e_623_ = lean_ctor_get(v_t_568_, 0);
lean_inc_ref(v_e_623_);
lean_dec_ref(v_t_568_);
v___x_624_ = lean_apply_1(v_k_569_, v_e_623_);
return v___x_624_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim(lean_object* v_motive__9_625_, lean_object* v_ctorIdx_626_, lean_object* v_t_627_, lean_object* v_h_628_, lean_object* v_k_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_627_, v_k_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___boxed(lean_object* v_motive__9_631_, lean_object* v_ctorIdx_632_, lean_object* v_t_633_, lean_object* v_h_634_, lean_object* v_k_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim(v_motive__9_631_, v_ctorIdx_632_, v_t_633_, v_h_634_, v_k_635_);
lean_dec(v_ctorIdx_632_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_core_elim___redArg(lean_object* v_t_637_, lean_object* v_core_638_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_637_, v_core_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_core_elim(lean_object* v_motive__9_640_, lean_object* v_t_641_, lean_object* v_h_642_, lean_object* v_core_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_641_, v_core_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreNeg_elim___redArg(lean_object* v_t_645_, lean_object* v_coreNeg_646_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_645_, v_coreNeg_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreNeg_elim(lean_object* v_motive__9_648_, lean_object* v_t_649_, lean_object* v_h_650_, lean_object* v_coreNeg_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_649_, v_coreNeg_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreToInt_elim___redArg(lean_object* v_t_653_, lean_object* v_coreToInt_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_653_, v_coreToInt_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreToInt_elim(lean_object* v_motive__9_656_, lean_object* v_t_657_, lean_object* v_h_658_, lean_object* v_coreToInt_659_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_657_, v_coreToInt_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreExpr_elim___redArg(lean_object* v_t_661_, lean_object* v_coreExpr_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_661_, v_coreExpr_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreExpr_elim(lean_object* v_motive__9_664_, lean_object* v_t_665_, lean_object* v_h_666_, lean_object* v_coreExpr_667_){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_665_, v_coreExpr_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofNatNonneg_elim___redArg(lean_object* v_t_669_, lean_object* v_ofNatNonneg_670_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_669_, v_ofNatNonneg_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofNatNonneg_elim(lean_object* v_motive__9_672_, lean_object* v_t_673_, lean_object* v_h_674_, lean_object* v_ofNatNonneg_675_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_673_, v_ofNatNonneg_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_hyp_elim___redArg(lean_object* v_t_677_, lean_object* v_hyp_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_677_, v_hyp_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_hyp_elim(lean_object* v_motive__9_680_, lean_object* v_t_681_, lean_object* v_h_682_, lean_object* v_hyp_683_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_681_, v_hyp_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_bound_elim___redArg(lean_object* v_t_685_, lean_object* v_bound_686_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_685_, v_bound_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_bound_elim(lean_object* v_motive__9_688_, lean_object* v_t_689_, lean_object* v_h_690_, lean_object* v_bound_691_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_689_, v_bound_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dec_elim___redArg(lean_object* v_t_693_, lean_object* v_dec_694_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_693_, v_dec_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dec_elim(lean_object* v_motive__9_696_, lean_object* v_t_697_, lean_object* v_h_698_, lean_object* v_dec_699_){
_start:
{
lean_object* v___x_700_; 
v___x_700_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_697_, v_dec_699_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_norm_elim___redArg(lean_object* v_t_701_, lean_object* v_norm_702_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_701_, v_norm_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_norm_elim(lean_object* v_motive__9_704_, lean_object* v_t_705_, lean_object* v_h_706_, lean_object* v_norm_707_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_705_, v_norm_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_divCoeffs_elim___redArg(lean_object* v_t_709_, lean_object* v_divCoeffs_710_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_709_, v_divCoeffs_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_divCoeffs_elim(lean_object* v_motive__9_712_, lean_object* v_t_713_, lean_object* v_h_714_, lean_object* v_divCoeffs_715_){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_713_, v_divCoeffs_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combine_elim___redArg(lean_object* v_t_717_, lean_object* v_combine_718_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_717_, v_combine_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combine_elim(lean_object* v_motive__9_720_, lean_object* v_t_721_, lean_object* v_h_722_, lean_object* v_combine_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_721_, v_combine_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combineDivCoeffs_elim___redArg(lean_object* v_t_725_, lean_object* v_combineDivCoeffs_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_725_, v_combineDivCoeffs_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combineDivCoeffs_elim(lean_object* v_motive__9_728_, lean_object* v_t_729_, lean_object* v_h_730_, lean_object* v_combineDivCoeffs_731_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_729_, v_combineDivCoeffs_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_subst_elim___redArg(lean_object* v_t_733_, lean_object* v_subst_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_733_, v_subst_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_subst_elim(lean_object* v_motive__9_736_, lean_object* v_t_737_, lean_object* v_h_738_, lean_object* v_subst_739_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_737_, v_subst_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofLeDiseq_elim___redArg(lean_object* v_t_741_, lean_object* v_ofLeDiseq_742_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_741_, v_ofLeDiseq_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofLeDiseq_elim(lean_object* v_motive__9_744_, lean_object* v_t_745_, lean_object* v_h_746_, lean_object* v_ofLeDiseq_747_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_745_, v_ofLeDiseq_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofDiseqSplit_elim___redArg(lean_object* v_t_749_, lean_object* v_ofDiseqSplit_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_749_, v_ofDiseqSplit_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofDiseqSplit_elim(lean_object* v_motive__9_752_, lean_object* v_t_753_, lean_object* v_h_754_, lean_object* v_ofDiseqSplit_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_753_, v_ofDiseqSplit_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_cooper_elim___redArg(lean_object* v_t_757_, lean_object* v_cooper_758_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_757_, v_cooper_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_cooper_elim(lean_object* v_motive__9_760_, lean_object* v_t_761_, lean_object* v_h_762_, lean_object* v_cooper_763_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_761_, v_cooper_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dvdTightMod_elim___redArg(lean_object* v_t_765_, lean_object* v_dvdTightMod_766_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_765_, v_dvdTightMod_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dvdTightMod_elim(lean_object* v_motive__9_768_, lean_object* v_t_769_, lean_object* v_h_770_, lean_object* v_dvdTightMod_771_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_769_, v_dvdTightMod_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_orHull_elim___redArg(lean_object* v_t_773_, lean_object* v_orHull_774_){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_773_, v_orHull_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_orHull_elim(lean_object* v_motive__9_776_, lean_object* v_t_777_, lean_object* v_h_778_, lean_object* v_orHull_779_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_777_, v_orHull_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_reorder_elim___redArg(lean_object* v_t_781_, lean_object* v_reorder_782_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_781_, v_reorder_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_reorder_elim(lean_object* v_motive__9_784_, lean_object* v_t_785_, lean_object* v_h_786_, lean_object* v_reorder_787_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_785_, v_reorder_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_commRingNorm_elim___redArg(lean_object* v_t_789_, lean_object* v_commRingNorm_790_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_789_, v_commRingNorm_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_commRingNorm_elim(lean_object* v_motive__9_792_, lean_object* v_t_793_, lean_object* v_h_794_, lean_object* v_commRingNorm_795_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_793_, v_commRingNorm_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorIdx___impl(lean_object* v_x_797_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = lean_obj_tag_nat(v_x_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorIdx___impl___boxed(lean_object* v_x_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorIdx___impl(v_x_799_);
lean_dec_ref(v_x_799_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(lean_object* v_t_801_, lean_object* v_k_802_){
_start:
{
switch(lean_obj_tag(v_t_801_))
{
case 0:
{
lean_object* v_a_803_; lean_object* v_zero_804_; lean_object* v___x_805_; 
v_a_803_ = lean_ctor_get(v_t_801_, 0);
lean_inc_ref(v_a_803_);
v_zero_804_ = lean_ctor_get(v_t_801_, 1);
lean_inc_ref(v_zero_804_);
lean_dec_ref_known(v_t_801_, 2);
v___x_805_ = lean_apply_2(v_k_802_, v_a_803_, v_zero_804_);
return v___x_805_;
}
case 1:
{
lean_object* v_a_806_; lean_object* v_b_807_; lean_object* v_p_u2081_808_; lean_object* v_p_u2082_809_; lean_object* v___x_810_; 
v_a_806_ = lean_ctor_get(v_t_801_, 0);
lean_inc_ref(v_a_806_);
v_b_807_ = lean_ctor_get(v_t_801_, 1);
lean_inc_ref(v_b_807_);
v_p_u2081_808_ = lean_ctor_get(v_t_801_, 2);
lean_inc_ref(v_p_u2081_808_);
v_p_u2082_809_ = lean_ctor_get(v_t_801_, 3);
lean_inc_ref(v_p_u2082_809_);
lean_dec_ref_known(v_t_801_, 4);
v___x_810_ = lean_apply_4(v_k_802_, v_a_806_, v_b_807_, v_p_u2081_808_, v_p_u2082_809_);
return v___x_810_;
}
case 2:
{
lean_object* v_a_811_; lean_object* v_b_812_; lean_object* v_toIntThm_813_; lean_object* v_lhs_814_; lean_object* v_rhs_815_; lean_object* v___x_816_; 
v_a_811_ = lean_ctor_get(v_t_801_, 0);
lean_inc_ref(v_a_811_);
v_b_812_ = lean_ctor_get(v_t_801_, 1);
lean_inc_ref(v_b_812_);
v_toIntThm_813_ = lean_ctor_get(v_t_801_, 2);
lean_inc_ref(v_toIntThm_813_);
v_lhs_814_ = lean_ctor_get(v_t_801_, 3);
lean_inc_ref(v_lhs_814_);
v_rhs_815_ = lean_ctor_get(v_t_801_, 4);
lean_inc_ref(v_rhs_815_);
lean_dec_ref_known(v_t_801_, 5);
v___x_816_ = lean_apply_5(v_k_802_, v_a_811_, v_b_812_, v_toIntThm_813_, v_lhs_814_, v_rhs_815_);
return v___x_816_;
}
case 6:
{
lean_object* v_x_817_; lean_object* v_c_u2081_818_; lean_object* v_c_u2082_819_; lean_object* v___x_820_; 
v_x_817_ = lean_ctor_get(v_t_801_, 0);
lean_inc(v_x_817_);
v_c_u2081_818_ = lean_ctor_get(v_t_801_, 1);
lean_inc_ref(v_c_u2081_818_);
v_c_u2082_819_ = lean_ctor_get(v_t_801_, 2);
lean_inc_ref(v_c_u2082_819_);
lean_dec_ref_known(v_t_801_, 3);
v___x_820_ = lean_apply_3(v_k_802_, v_x_817_, v_c_u2081_818_, v_c_u2082_819_);
return v___x_820_;
}
case 8:
{
lean_object* v_c_821_; lean_object* v_e_822_; lean_object* v_p_823_; lean_object* v___x_824_; 
v_c_821_ = lean_ctor_get(v_t_801_, 0);
lean_inc_ref(v_c_821_);
v_e_822_ = lean_ctor_get(v_t_801_, 1);
lean_inc_ref(v_e_822_);
v_p_823_ = lean_ctor_get(v_t_801_, 2);
lean_inc_ref(v_p_823_);
lean_dec_ref_known(v_t_801_, 3);
v___x_824_ = lean_apply_3(v_k_802_, v_c_821_, v_e_822_, v_p_823_);
return v___x_824_;
}
default: 
{
lean_object* v_c_825_; lean_object* v___x_826_; 
v_c_825_ = lean_ctor_get(v_t_801_, 0);
lean_inc_ref(v_c_825_);
lean_dec_ref(v_t_801_);
v___x_826_ = lean_apply_1(v_k_802_, v_c_825_);
return v___x_826_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim(lean_object* v_motive__11_827_, lean_object* v_ctorIdx_828_, lean_object* v_t_829_, lean_object* v_h_830_, lean_object* v_k_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_829_, v_k_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___boxed(lean_object* v_motive__11_833_, lean_object* v_ctorIdx_834_, lean_object* v_t_835_, lean_object* v_h_836_, lean_object* v_k_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim(v_motive__11_833_, v_ctorIdx_834_, v_t_835_, v_h_836_, v_k_837_);
lean_dec(v_ctorIdx_834_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core0_elim___redArg(lean_object* v_t_839_, lean_object* v_core0_840_){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_839_, v_core0_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core0_elim(lean_object* v_motive__11_842_, lean_object* v_t_843_, lean_object* v_h_844_, lean_object* v_core0_845_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_843_, v_core0_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core_elim___redArg(lean_object* v_t_847_, lean_object* v_core_848_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_847_, v_core_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core_elim(lean_object* v_motive__11_850_, lean_object* v_t_851_, lean_object* v_h_852_, lean_object* v_core_853_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_851_, v_core_853_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_coreToInt_elim___redArg(lean_object* v_t_855_, lean_object* v_coreToInt_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_855_, v_coreToInt_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_coreToInt_elim(lean_object* v_motive__11_858_, lean_object* v_t_859_, lean_object* v_h_860_, lean_object* v_coreToInt_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_859_, v_coreToInt_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_norm_elim___redArg(lean_object* v_t_863_, lean_object* v_norm_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_863_, v_norm_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_norm_elim(lean_object* v_motive__11_866_, lean_object* v_t_867_, lean_object* v_h_868_, lean_object* v_norm_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_867_, v_norm_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_divCoeffs_elim___redArg(lean_object* v_t_871_, lean_object* v_divCoeffs_872_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_871_, v_divCoeffs_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_divCoeffs_elim(lean_object* v_motive__11_874_, lean_object* v_t_875_, lean_object* v_h_876_, lean_object* v_divCoeffs_877_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_875_, v_divCoeffs_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_neg_elim___redArg(lean_object* v_t_879_, lean_object* v_neg_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_879_, v_neg_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_neg_elim(lean_object* v_motive__11_882_, lean_object* v_t_883_, lean_object* v_h_884_, lean_object* v_neg_885_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_883_, v_neg_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_subst_elim___redArg(lean_object* v_t_887_, lean_object* v_subst_888_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_887_, v_subst_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_subst_elim(lean_object* v_motive__11_890_, lean_object* v_t_891_, lean_object* v_h_892_, lean_object* v_subst_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_891_, v_subst_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_reorder_elim___redArg(lean_object* v_t_895_, lean_object* v_reorder_896_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_895_, v_reorder_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_reorder_elim(lean_object* v_motive__11_898_, lean_object* v_t_899_, lean_object* v_h_900_, lean_object* v_reorder_901_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_899_, v_reorder_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_commRingNorm_elim___redArg(lean_object* v_t_903_, lean_object* v_commRingNorm_904_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_903_, v_commRingNorm_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_commRingNorm_elim(lean_object* v_motive__11_906_, lean_object* v_t_907_, lean_object* v_h_908_, lean_object* v_commRingNorm_909_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_907_, v_commRingNorm_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorIdx___impl(lean_object* v_x_911_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = lean_obj_tag_nat(v_x_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorIdx___impl___boxed(lean_object* v_x_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorIdx___impl(v_x_913_);
lean_dec_ref(v_x_913_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(lean_object* v_t_915_, lean_object* v_k_916_){
_start:
{
if (lean_obj_tag(v_t_915_) == 4)
{
lean_object* v_c_u2081_917_; lean_object* v_c_u2082_918_; lean_object* v_c_u2083_919_; lean_object* v___x_920_; 
v_c_u2081_917_ = lean_ctor_get(v_t_915_, 0);
lean_inc_ref(v_c_u2081_917_);
v_c_u2082_918_ = lean_ctor_get(v_t_915_, 1);
lean_inc_ref(v_c_u2082_918_);
v_c_u2083_919_ = lean_ctor_get(v_t_915_, 2);
lean_inc_ref(v_c_u2083_919_);
lean_dec_ref_known(v_t_915_, 3);
v___x_920_ = lean_apply_3(v_k_916_, v_c_u2081_917_, v_c_u2082_918_, v_c_u2083_919_);
return v___x_920_;
}
else
{
lean_object* v_c_921_; lean_object* v___x_922_; 
v_c_921_ = lean_ctor_get(v_t_915_, 0);
lean_inc_ref(v_c_921_);
lean_dec_ref(v_t_915_);
v___x_922_ = lean_apply_1(v_k_916_, v_c_921_);
return v___x_922_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim(lean_object* v_motive__12_923_, lean_object* v_ctorIdx_924_, lean_object* v_t_925_, lean_object* v_h_926_, lean_object* v_k_927_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_925_, v_k_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___boxed(lean_object* v_motive__12_929_, lean_object* v_ctorIdx_930_, lean_object* v_t_931_, lean_object* v_h_932_, lean_object* v_k_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim(v_motive__12_929_, v_ctorIdx_930_, v_t_931_, v_h_932_, v_k_933_);
lean_dec(v_ctorIdx_930_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_dvd_elim___redArg(lean_object* v_t_935_, lean_object* v_dvd_936_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_935_, v_dvd_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_dvd_elim(lean_object* v_motive__12_938_, lean_object* v_t_939_, lean_object* v_h_940_, lean_object* v_dvd_941_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_939_, v_dvd_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_le_elim___redArg(lean_object* v_t_943_, lean_object* v_le_944_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_943_, v_le_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_le_elim(lean_object* v_motive__12_946_, lean_object* v_t_947_, lean_object* v_h_948_, lean_object* v_le_949_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_947_, v_le_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_eq_elim___redArg(lean_object* v_t_951_, lean_object* v_eq_952_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_951_, v_eq_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_eq_elim(lean_object* v_motive__12_954_, lean_object* v_t_955_, lean_object* v_h_956_, lean_object* v_eq_957_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_955_, v_eq_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_diseq_elim___redArg(lean_object* v_t_959_, lean_object* v_diseq_960_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_959_, v_diseq_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_diseq_elim(lean_object* v_motive__12_962_, lean_object* v_t_963_, lean_object* v_h_964_, lean_object* v_diseq_965_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_963_, v_diseq_965_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_cooper_elim___redArg(lean_object* v_t_967_, lean_object* v_cooper_968_){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_967_, v_cooper_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_cooper_elim(lean_object* v_motive__12_970_, lean_object* v_t_971_, lean_object* v_h_972_, lean_object* v_cooper_973_){
_start:
{
lean_object* v___x_974_; 
v___x_974_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_971_, v_cooper_973_);
return v___x_974_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0);
v___x_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
return v___x_976_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3(void){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_980_ = lean_box(0);
v___x_981_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__2));
v___x_982_ = l_Lean_Expr_const___override(v___x_981_, v___x_980_);
return v___x_982_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4(void){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3);
v___x_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
return v___x_984_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5(void){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_985_ = lean_box(0);
v___x_986_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4);
v___x_987_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0);
v___x_988_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
lean_ctor_set(v___x_988_, 1, v___x_986_);
lean_ctor_set(v___x_988_, 2, v___x_985_);
return v___x_988_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr(void){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5);
return v___x_989_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0(void){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3);
v___x_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
return v___x_991_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1(void){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_992_ = lean_box(0);
v___x_993_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0);
v___x_994_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0);
v___x_995_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0);
v___x_996_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
lean_ctor_set(v___x_996_, 1, v___x_994_);
lean_ctor_set(v___x_996_, 2, v___x_993_);
lean_ctor_set(v___x_996_, 3, v___x_992_);
return v___x_996_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr(void){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1);
return v___x_997_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0(void){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; uint8_t v___x_1000_; lean_object* v___x_1001_; 
v___x_998_ = lean_box(0);
v___x_999_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5);
v___x_1000_ = 0;
v___x_1001_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1001_, 0, v___x_999_);
lean_ctor_set(v___x_1001_, 1, v___x_999_);
lean_ctor_set(v___x_1001_, 2, v___x_998_);
lean_ctor_set_uint8(v___x_1001_, sizeof(void*)*3, v___x_1000_);
return v___x_1001_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred(void){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0);
return v___x_1002_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1(void){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1005_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__0));
v___x_1006_ = lean_unsigned_to_nat(0u);
v___x_1007_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0);
v___x_1008_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v___x_1006_);
lean_ctor_set(v___x_1008_, 2, v___x_1005_);
return v___x_1008_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit(void){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1);
return v___x_1009_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1010_; 
v___x_1010_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1010_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1011_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0);
v___x_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg(){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__1);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___boxed(lean_object* v___dummy_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg();
return v_res_1016_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1017_; 
v___x_1017_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg();
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0(lean_object* v_00_u03b2_1018_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0);
return v___x_1019_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0(void){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1020_ = lean_unsigned_to_nat(32u);
v___x_1021_ = lean_mk_empty_array_with_capacity(v___x_1020_);
v___x_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
return v___x_1022_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1(void){
_start:
{
size_t v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1023_ = ((size_t)5ULL);
v___x_1024_ = lean_unsigned_to_nat(0u);
v___x_1025_ = lean_unsigned_to_nat(32u);
v___x_1026_ = lean_mk_empty_array_with_capacity(v___x_1025_);
v___x_1027_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0);
v___x_1028_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
lean_ctor_set(v___x_1028_, 1, v___x_1026_);
lean_ctor_set(v___x_1028_, 2, v___x_1024_);
lean_ctor_set(v___x_1028_, 3, v___x_1024_);
lean_ctor_set_usize(v___x_1028_, 4, v___x_1023_);
return v___x_1028_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0);
v___x_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
return v___x_1030_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3(void){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; uint8_t v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1031_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0);
v___x_1032_ = lean_box(0);
v___x_1033_ = 0;
v___x_1034_ = lean_unsigned_to_nat(0u);
v___x_1035_ = lean_box(0);
v___x_1036_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2);
v___x_1037_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1);
v___x_1038_ = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
lean_ctor_set(v___x_1038_, 1, v___x_1036_);
lean_ctor_set(v___x_1038_, 2, v___x_1037_);
lean_ctor_set(v___x_1038_, 3, v___x_1036_);
lean_ctor_set(v___x_1038_, 4, v___x_1036_);
lean_ctor_set(v___x_1038_, 5, v___x_1037_);
lean_ctor_set(v___x_1038_, 6, v___x_1037_);
lean_ctor_set(v___x_1038_, 7, v___x_1037_);
lean_ctor_set(v___x_1038_, 8, v___x_1037_);
lean_ctor_set(v___x_1038_, 9, v___x_1037_);
lean_ctor_set(v___x_1038_, 10, v___x_1035_);
lean_ctor_set(v___x_1038_, 11, v___x_1037_);
lean_ctor_set(v___x_1038_, 12, v___x_1037_);
lean_ctor_set(v___x_1038_, 13, v___x_1034_);
lean_ctor_set(v___x_1038_, 14, v___x_1034_);
lean_ctor_set(v___x_1038_, 15, v___x_1036_);
lean_ctor_set(v___x_1038_, 16, v___x_1034_);
lean_ctor_set(v___x_1038_, 17, v___x_1032_);
lean_ctor_set(v___x_1038_, 18, v___x_1036_);
lean_ctor_set(v___x_1038_, 19, v___x_1031_);
lean_ctor_set(v___x_1038_, 20, v___x_1036_);
lean_ctor_set_uint8(v___x_1038_, sizeof(void*)*21, v___x_1033_);
lean_ctor_set_uint8(v___x_1038_, sizeof(void*)*21 + 1, v___x_1033_);
return v___x_1038_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default(void){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3);
return v___x_1039_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState(void){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default;
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(lean_object* v___x_1041_){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1041_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2____boxed(lean_object* v___x_1044_, lean_object* v___y_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(v___x_1044_);
return v_res_1046_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1047_; lean_object* v___f_1048_; 
v___x_1047_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3);
v___f_1048_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_1048_, 0, v___x_1047_);
return v___f_1048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_1050_; lean_object* v___x_1051_; 
v___f_1050_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_);
v___x_1051_ = l_Lean_Meta_Grind_registerSolverExtension___redArg(v___f_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2____boxed(lean_object* v_a_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_();
return v_res_1053_;
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
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullKind_default = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullKind_default();
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullKind = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullKind();
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullAlt_default = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullAlt_default();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullAlt_default);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullAlt = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullAlt();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullAlt);
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
