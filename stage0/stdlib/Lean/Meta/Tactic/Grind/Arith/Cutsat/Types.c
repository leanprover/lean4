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
extern lean_object* l_Int_Internal_Linear_instInhabitedExpr_default;
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
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullAtom_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullAtom_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullAtom_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullAtom;
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
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullAtom_default___closed__0(void){
_start:
{
uint8_t v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_112_ = 0;
v___x_113_ = l_Int_Internal_Linear_instInhabitedExpr_default;
v___x_114_ = lean_box(0);
v___x_115_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_115_, 0, v___x_114_);
lean_ctor_set(v___x_115_, 1, v___x_113_);
lean_ctor_set(v___x_115_, 2, v___x_113_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*3, v___x_112_);
return v___x_115_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullAtom_default(void){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullAtom_default___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullAtom_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullAtom_default___closed__0);
return v___x_116_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullAtom(void){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullAtom_default;
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorIdx___impl(lean_object* v_x_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = lean_obj_tag_nat(v_x_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorIdx___impl___boxed(lean_object* v_x_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorIdx___impl(v_x_120_);
lean_dec_ref(v_x_120_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(lean_object* v_t_122_, lean_object* v_k_123_){
_start:
{
switch(lean_obj_tag(v_t_122_))
{
case 0:
{
lean_object* v_a_124_; lean_object* v_zero_125_; lean_object* v___x_126_; 
v_a_124_ = lean_ctor_get(v_t_122_, 0);
lean_inc_ref(v_a_124_);
v_zero_125_ = lean_ctor_get(v_t_122_, 1);
lean_inc_ref(v_zero_125_);
lean_dec_ref_known(v_t_122_, 2);
v___x_126_ = lean_apply_2(v_k_123_, v_a_124_, v_zero_125_);
return v___x_126_;
}
case 1:
{
lean_object* v_a_127_; lean_object* v_b_128_; lean_object* v_p_u2081_129_; lean_object* v_p_u2082_130_; lean_object* v___x_131_; 
v_a_127_ = lean_ctor_get(v_t_122_, 0);
lean_inc_ref(v_a_127_);
v_b_128_ = lean_ctor_get(v_t_122_, 1);
lean_inc_ref(v_b_128_);
v_p_u2081_129_ = lean_ctor_get(v_t_122_, 2);
lean_inc_ref(v_p_u2081_129_);
v_p_u2082_130_ = lean_ctor_get(v_t_122_, 3);
lean_inc_ref(v_p_u2082_130_);
lean_dec_ref_known(v_t_122_, 4);
v___x_131_ = lean_apply_4(v_k_123_, v_a_127_, v_b_128_, v_p_u2081_129_, v_p_u2082_130_);
return v___x_131_;
}
case 2:
{
lean_object* v_a_132_; lean_object* v_b_133_; lean_object* v_toIntThm_134_; lean_object* v_lhs_135_; lean_object* v_rhs_136_; lean_object* v___x_137_; 
v_a_132_ = lean_ctor_get(v_t_122_, 0);
lean_inc_ref(v_a_132_);
v_b_133_ = lean_ctor_get(v_t_122_, 1);
lean_inc_ref(v_b_133_);
v_toIntThm_134_ = lean_ctor_get(v_t_122_, 2);
lean_inc_ref(v_toIntThm_134_);
v_lhs_135_ = lean_ctor_get(v_t_122_, 3);
lean_inc_ref(v_lhs_135_);
v_rhs_136_ = lean_ctor_get(v_t_122_, 4);
lean_inc_ref(v_rhs_136_);
lean_dec_ref_known(v_t_122_, 5);
v___x_137_ = lean_apply_5(v_k_123_, v_a_132_, v_b_133_, v_toIntThm_134_, v_lhs_135_, v_rhs_136_);
return v___x_137_;
}
case 3:
{
lean_object* v_h_138_; lean_object* v_lhs_139_; lean_object* v_rhs_140_; lean_object* v___x_141_; 
v_h_138_ = lean_ctor_get(v_t_122_, 0);
lean_inc_ref(v_h_138_);
v_lhs_139_ = lean_ctor_get(v_t_122_, 1);
lean_inc_ref(v_lhs_139_);
v_rhs_140_ = lean_ctor_get(v_t_122_, 2);
lean_inc_ref(v_rhs_140_);
lean_dec_ref_known(v_t_122_, 3);
v___x_141_ = lean_apply_3(v_k_123_, v_h_138_, v_lhs_139_, v_rhs_140_);
return v___x_141_;
}
case 4:
{
lean_object* v_e_142_; lean_object* v_p_143_; lean_object* v___x_144_; 
v_e_142_ = lean_ctor_get(v_t_122_, 0);
lean_inc_ref(v_e_142_);
v_p_143_ = lean_ctor_get(v_t_122_, 1);
lean_inc_ref(v_p_143_);
lean_dec_ref_known(v_t_122_, 2);
v___x_144_ = lean_apply_2(v_k_123_, v_e_142_, v_p_143_);
return v___x_144_;
}
case 5:
{
lean_object* v_h_145_; lean_object* v_x_146_; lean_object* v_e_x27_147_; lean_object* v___x_148_; 
v_h_145_ = lean_ctor_get(v_t_122_, 0);
lean_inc_ref(v_h_145_);
v_x_146_ = lean_ctor_get(v_t_122_, 1);
lean_inc(v_x_146_);
v_e_x27_147_ = lean_ctor_get(v_t_122_, 2);
lean_inc_ref(v_e_x27_147_);
lean_dec_ref_known(v_t_122_, 3);
v___x_148_ = lean_apply_3(v_k_123_, v_h_145_, v_x_146_, v_e_x27_147_);
return v___x_148_;
}
case 8:
{
lean_object* v_x_149_; lean_object* v_c_u2081_150_; lean_object* v_c_u2082_151_; lean_object* v___x_152_; 
v_x_149_ = lean_ctor_get(v_t_122_, 0);
lean_inc(v_x_149_);
v_c_u2081_150_ = lean_ctor_get(v_t_122_, 1);
lean_inc_ref(v_c_u2081_150_);
v_c_u2082_151_ = lean_ctor_get(v_t_122_, 2);
lean_inc_ref(v_c_u2082_151_);
lean_dec_ref_known(v_t_122_, 3);
v___x_152_ = lean_apply_3(v_k_123_, v_x_149_, v_c_u2081_150_, v_c_u2082_151_);
return v___x_152_;
}
case 9:
{
lean_object* v_c_u2081_153_; lean_object* v_c_u2082_154_; lean_object* v___x_155_; 
v_c_u2081_153_ = lean_ctor_get(v_t_122_, 0);
lean_inc_ref(v_c_u2081_153_);
v_c_u2082_154_ = lean_ctor_get(v_t_122_, 1);
lean_inc_ref(v_c_u2082_154_);
lean_dec_ref_known(v_t_122_, 2);
v___x_155_ = lean_apply_2(v_k_123_, v_c_u2081_153_, v_c_u2082_154_);
return v___x_155_;
}
case 11:
{
lean_object* v_c_156_; lean_object* v_e_157_; lean_object* v_x_158_; lean_object* v_t_159_; lean_object* v___x_160_; 
v_c_156_ = lean_ctor_get(v_t_122_, 0);
lean_inc_ref(v_c_156_);
v_e_157_ = lean_ctor_get(v_t_122_, 1);
lean_inc_ref(v_e_157_);
v_x_158_ = lean_ctor_get(v_t_122_, 2);
lean_inc(v_x_158_);
v_t_159_ = lean_ctor_get(v_t_122_, 3);
lean_inc_ref(v_t_159_);
lean_dec_ref_known(v_t_122_, 4);
v___x_160_ = lean_apply_4(v_k_123_, v_c_156_, v_e_157_, v_x_158_, v_t_159_);
return v___x_160_;
}
case 13:
{
lean_object* v_c_161_; lean_object* v_e_162_; lean_object* v_p_163_; lean_object* v___x_164_; 
v_c_161_ = lean_ctor_get(v_t_122_, 0);
lean_inc_ref(v_c_161_);
v_e_162_ = lean_ctor_get(v_t_122_, 1);
lean_inc_ref(v_e_162_);
v_p_163_ = lean_ctor_get(v_t_122_, 2);
lean_inc_ref(v_p_163_);
lean_dec_ref_known(v_t_122_, 3);
v___x_164_ = lean_apply_3(v_k_123_, v_c_161_, v_e_162_, v_p_163_);
return v___x_164_;
}
case 14:
{
lean_object* v_e_165_; lean_object* v_p_166_; lean_object* v_re_167_; lean_object* v_rp_168_; lean_object* v_p_x27_169_; lean_object* v___x_170_; 
v_e_165_ = lean_ctor_get(v_t_122_, 0);
lean_inc_ref(v_e_165_);
v_p_166_ = lean_ctor_get(v_t_122_, 1);
lean_inc_ref(v_p_166_);
v_re_167_ = lean_ctor_get(v_t_122_, 2);
lean_inc_ref(v_re_167_);
v_rp_168_ = lean_ctor_get(v_t_122_, 3);
lean_inc_ref(v_rp_168_);
v_p_x27_169_ = lean_ctor_get(v_t_122_, 4);
lean_inc_ref(v_p_x27_169_);
lean_dec_ref_known(v_t_122_, 5);
v___x_170_ = lean_apply_5(v_k_123_, v_e_165_, v_p_166_, v_re_167_, v_rp_168_, v_p_x27_169_);
return v___x_170_;
}
case 15:
{
lean_object* v_h_171_; lean_object* v_x_172_; lean_object* v_e_x27_173_; lean_object* v_p_174_; lean_object* v_re_175_; lean_object* v_rp_176_; lean_object* v_p_x27_177_; lean_object* v___x_178_; 
v_h_171_ = lean_ctor_get(v_t_122_, 0);
lean_inc_ref(v_h_171_);
v_x_172_ = lean_ctor_get(v_t_122_, 1);
lean_inc(v_x_172_);
v_e_x27_173_ = lean_ctor_get(v_t_122_, 2);
lean_inc_ref(v_e_x27_173_);
v_p_174_ = lean_ctor_get(v_t_122_, 3);
lean_inc_ref(v_p_174_);
v_re_175_ = lean_ctor_get(v_t_122_, 4);
lean_inc_ref(v_re_175_);
v_rp_176_ = lean_ctor_get(v_t_122_, 5);
lean_inc_ref(v_rp_176_);
v_p_x27_177_ = lean_ctor_get(v_t_122_, 6);
lean_inc_ref(v_p_x27_177_);
lean_dec_ref_known(v_t_122_, 7);
v___x_178_ = lean_apply_7(v_k_123_, v_h_171_, v_x_172_, v_e_x27_173_, v_p_174_, v_re_175_, v_rp_176_, v_p_x27_177_);
return v___x_178_;
}
case 16:
{
lean_object* v_a_x3f_179_; lean_object* v_cs_180_; lean_object* v___x_181_; 
v_a_x3f_179_ = lean_ctor_get(v_t_122_, 0);
lean_inc(v_a_x3f_179_);
v_cs_180_ = lean_ctor_get(v_t_122_, 1);
lean_inc_ref(v_cs_180_);
lean_dec_ref_known(v_t_122_, 2);
v___x_181_ = lean_apply_2(v_k_123_, v_a_x3f_179_, v_cs_180_);
return v___x_181_;
}
case 17:
{
lean_object* v_k_182_; lean_object* v_y_x3f_183_; lean_object* v_c_184_; lean_object* v___x_185_; 
v_k_182_ = lean_ctor_get(v_t_122_, 0);
lean_inc(v_k_182_);
v_y_x3f_183_ = lean_ctor_get(v_t_122_, 1);
lean_inc(v_y_x3f_183_);
v_c_184_ = lean_ctor_get(v_t_122_, 2);
lean_inc_ref(v_c_184_);
lean_dec_ref_known(v_t_122_, 3);
v___x_185_ = lean_apply_3(v_k_123_, v_k_182_, v_y_x3f_183_, v_c_184_);
return v___x_185_;
}
case 18:
{
lean_object* v_k_186_; lean_object* v_y_x3f_187_; lean_object* v_c_188_; lean_object* v___x_189_; 
v_k_186_ = lean_ctor_get(v_t_122_, 0);
lean_inc(v_k_186_);
v_y_x3f_187_ = lean_ctor_get(v_t_122_, 1);
lean_inc(v_y_x3f_187_);
v_c_188_ = lean_ctor_get(v_t_122_, 2);
lean_inc_ref(v_c_188_);
lean_dec_ref_known(v_t_122_, 3);
v___x_189_ = lean_apply_3(v_k_123_, v_k_186_, v_y_x3f_187_, v_c_188_);
return v___x_189_;
}
case 19:
{
lean_object* v_ka_190_; lean_object* v_ca_x3f_191_; lean_object* v_kb_192_; lean_object* v_cb_x3f_193_; lean_object* v___x_194_; 
v_ka_190_ = lean_ctor_get(v_t_122_, 0);
lean_inc(v_ka_190_);
v_ca_x3f_191_ = lean_ctor_get(v_t_122_, 1);
lean_inc(v_ca_x3f_191_);
v_kb_192_ = lean_ctor_get(v_t_122_, 2);
lean_inc(v_kb_192_);
v_cb_x3f_193_ = lean_ctor_get(v_t_122_, 3);
lean_inc(v_cb_x3f_193_);
lean_dec_ref_known(v_t_122_, 4);
v___x_194_ = lean_apply_4(v_k_123_, v_ka_190_, v_ca_x3f_191_, v_kb_192_, v_cb_x3f_193_);
return v___x_194_;
}
default: 
{
lean_object* v_c_195_; lean_object* v___x_196_; 
v_c_195_ = lean_ctor_get(v_t_122_, 0);
lean_inc_ref(v_c_195_);
lean_dec_ref(v_t_122_);
v___x_196_ = lean_apply_1(v_k_123_, v_c_195_);
return v___x_196_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim(lean_object* v_motive__2_197_, lean_object* v_ctorIdx_198_, lean_object* v_t_199_, lean_object* v_h_200_, lean_object* v_k_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_199_, v_k_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___boxed(lean_object* v_motive__2_203_, lean_object* v_ctorIdx_204_, lean_object* v_t_205_, lean_object* v_h_206_, lean_object* v_k_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim(v_motive__2_203_, v_ctorIdx_204_, v_t_205_, v_h_206_, v_k_207_);
lean_dec(v_ctorIdx_204_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core0_elim___redArg(lean_object* v_t_209_, lean_object* v_core0_210_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_209_, v_core0_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core0_elim(lean_object* v_motive__2_212_, lean_object* v_t_213_, lean_object* v_h_214_, lean_object* v_core0_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_213_, v_core0_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core_elim___redArg(lean_object* v_t_217_, lean_object* v_core_218_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_217_, v_core_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core_elim(lean_object* v_motive__2_220_, lean_object* v_t_221_, lean_object* v_h_222_, lean_object* v_core_223_){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_221_, v_core_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_coreToInt_elim___redArg(lean_object* v_t_225_, lean_object* v_coreToInt_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_225_, v_coreToInt_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_coreToInt_elim(lean_object* v_motive__2_228_, lean_object* v_t_229_, lean_object* v_h_230_, lean_object* v_coreToInt_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_229_, v_coreToInt_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_hyp_elim___redArg(lean_object* v_t_233_, lean_object* v_hyp_234_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_233_, v_hyp_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_hyp_elim(lean_object* v_motive__2_236_, lean_object* v_t_237_, lean_object* v_h_238_, lean_object* v_hyp_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_237_, v_hyp_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defn_elim___redArg(lean_object* v_t_241_, lean_object* v_defn_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_241_, v_defn_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defn_elim(lean_object* v_motive__2_244_, lean_object* v_t_245_, lean_object* v_h_246_, lean_object* v_defn_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_245_, v_defn_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnExpr_elim___redArg(lean_object* v_t_249_, lean_object* v_defnExpr_250_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_249_, v_defnExpr_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnExpr_elim(lean_object* v_motive__2_252_, lean_object* v_t_253_, lean_object* v_h_254_, lean_object* v_defnExpr_255_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_253_, v_defnExpr_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_norm_elim___redArg(lean_object* v_t_257_, lean_object* v_norm_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_257_, v_norm_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_norm_elim(lean_object* v_motive__2_260_, lean_object* v_t_261_, lean_object* v_h_262_, lean_object* v_norm_263_){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_261_, v_norm_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_divCoeffs_elim___redArg(lean_object* v_t_265_, lean_object* v_divCoeffs_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_265_, v_divCoeffs_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_divCoeffs_elim(lean_object* v_motive__2_268_, lean_object* v_t_269_, lean_object* v_h_270_, lean_object* v_divCoeffs_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_269_, v_divCoeffs_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_subst_elim___redArg(lean_object* v_t_273_, lean_object* v_subst_274_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_273_, v_subst_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_subst_elim(lean_object* v_motive__2_276_, lean_object* v_t_277_, lean_object* v_h_278_, lean_object* v_subst_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_277_, v_subst_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofLeGe_elim___redArg(lean_object* v_t_281_, lean_object* v_ofLeGe_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_281_, v_ofLeGe_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofLeGe_elim(lean_object* v_motive__2_284_, lean_object* v_t_285_, lean_object* v_h_286_, lean_object* v_ofLeGe_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_285_, v_ofLeGe_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofZeroDvd_elim___redArg(lean_object* v_t_289_, lean_object* v_ofZeroDvd_290_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_289_, v_ofZeroDvd_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofZeroDvd_elim(lean_object* v_motive__2_292_, lean_object* v_t_293_, lean_object* v_h_294_, lean_object* v_ofZeroDvd_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_293_, v_ofZeroDvd_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofDvdDiv_elim___redArg(lean_object* v_t_297_, lean_object* v_ofDvdDiv_298_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_297_, v_ofDvdDiv_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofDvdDiv_elim(lean_object* v_motive__2_300_, lean_object* v_t_301_, lean_object* v_h_302_, lean_object* v_ofDvdDiv_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_301_, v_ofDvdDiv_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_reorder_elim___redArg(lean_object* v_t_305_, lean_object* v_reorder_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_305_, v_reorder_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_reorder_elim(lean_object* v_motive__2_308_, lean_object* v_t_309_, lean_object* v_h_310_, lean_object* v_reorder_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_309_, v_reorder_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_commRingNorm_elim___redArg(lean_object* v_t_313_, lean_object* v_commRingNorm_314_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_313_, v_commRingNorm_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_commRingNorm_elim(lean_object* v_motive__2_316_, lean_object* v_t_317_, lean_object* v_h_318_, lean_object* v_commRingNorm_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_317_, v_commRingNorm_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnCommRing_elim___redArg(lean_object* v_t_321_, lean_object* v_defnCommRing_322_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_321_, v_defnCommRing_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnCommRing_elim(lean_object* v_motive__2_324_, lean_object* v_t_325_, lean_object* v_h_326_, lean_object* v_defnCommRing_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_325_, v_defnCommRing_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnExprCommRing_elim___redArg(lean_object* v_t_329_, lean_object* v_defnExprCommRing_330_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_329_, v_defnExprCommRing_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnExprCommRing_elim(lean_object* v_motive__2_332_, lean_object* v_t_333_, lean_object* v_h_334_, lean_object* v_defnExprCommRing_335_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_333_, v_defnExprCommRing_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mul_elim___redArg(lean_object* v_t_337_, lean_object* v_mul_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_337_, v_mul_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mul_elim(lean_object* v_motive__2_340_, lean_object* v_t_341_, lean_object* v_h_342_, lean_object* v_mul_343_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_341_, v_mul_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_div_elim___redArg(lean_object* v_t_345_, lean_object* v_div_346_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_345_, v_div_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_div_elim(lean_object* v_motive__2_348_, lean_object* v_t_349_, lean_object* v_h_350_, lean_object* v_div_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_349_, v_div_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mod_elim___redArg(lean_object* v_t_353_, lean_object* v_mod_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_353_, v_mod_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mod_elim(lean_object* v_motive__2_356_, lean_object* v_t_357_, lean_object* v_h_358_, lean_object* v_mod_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_357_, v_mod_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_pow_elim___redArg(lean_object* v_t_361_, lean_object* v_pow_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_361_, v_pow_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_pow_elim(lean_object* v_motive__2_364_, lean_object* v_t_365_, lean_object* v_h_366_, lean_object* v_pow_367_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_365_, v_pow_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorIdx___impl(lean_object* v_x_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = lean_obj_tag_nat(v_x_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorIdx___impl___boxed(lean_object* v_x_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorIdx___impl(v_x_371_);
lean_dec_ref(v_x_371_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(lean_object* v_t_373_, lean_object* v_k_374_){
_start:
{
if (lean_obj_tag(v_t_373_) == 0)
{
lean_object* v_h_375_; lean_object* v___x_376_; 
v_h_375_ = lean_ctor_get(v_t_373_, 0);
lean_inc(v_h_375_);
lean_dec_ref_known(v_t_373_, 1);
v___x_376_ = lean_apply_1(v_k_374_, v_h_375_);
return v___x_376_;
}
else
{
lean_object* v_hs_377_; lean_object* v_decVars_378_; lean_object* v___x_379_; 
v_hs_377_ = lean_ctor_get(v_t_373_, 0);
lean_inc_ref(v_hs_377_);
v_decVars_378_ = lean_ctor_get(v_t_373_, 1);
lean_inc_ref(v_decVars_378_);
lean_dec_ref_known(v_t_373_, 2);
v___x_379_ = lean_apply_2(v_k_374_, v_hs_377_, v_decVars_378_);
return v___x_379_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim(lean_object* v_motive__6_380_, lean_object* v_ctorIdx_381_, lean_object* v_t_382_, lean_object* v_h_383_, lean_object* v_k_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_382_, v_k_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___boxed(lean_object* v_motive__6_386_, lean_object* v_ctorIdx_387_, lean_object* v_t_388_, lean_object* v_h_389_, lean_object* v_k_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim(v_motive__6_386_, v_ctorIdx_387_, v_t_388_, v_h_389_, v_k_390_);
lean_dec(v_ctorIdx_387_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_dec_elim___redArg(lean_object* v_t_392_, lean_object* v_dec_393_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_392_, v_dec_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_dec_elim(lean_object* v_motive__6_395_, lean_object* v_t_396_, lean_object* v_h_397_, lean_object* v_dec_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_396_, v_dec_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_last_elim___redArg(lean_object* v_t_400_, lean_object* v_last_401_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_400_, v_last_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_last_elim(lean_object* v_motive__6_403_, lean_object* v_t_404_, lean_object* v_h_405_, lean_object* v_last_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_404_, v_last_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorIdx___impl(lean_object* v_x_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = lean_obj_tag_nat(v_x_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorIdx___impl___boxed(lean_object* v_x_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorIdx___impl(v_x_410_);
lean_dec_ref(v_x_410_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(lean_object* v_t_412_, lean_object* v_k_413_){
_start:
{
switch(lean_obj_tag(v_t_412_))
{
case 1:
{
lean_object* v_e_414_; lean_object* v_thm_415_; lean_object* v_d_416_; lean_object* v_a_417_; lean_object* v___x_418_; 
v_e_414_ = lean_ctor_get(v_t_412_, 0);
lean_inc_ref(v_e_414_);
v_thm_415_ = lean_ctor_get(v_t_412_, 1);
lean_inc_ref(v_thm_415_);
v_d_416_ = lean_ctor_get(v_t_412_, 2);
lean_inc(v_d_416_);
v_a_417_ = lean_ctor_get(v_t_412_, 3);
lean_inc_ref(v_a_417_);
lean_dec_ref_known(v_t_412_, 4);
v___x_418_ = lean_apply_4(v_k_413_, v_e_414_, v_thm_415_, v_d_416_, v_a_417_);
return v___x_418_;
}
case 4:
{
lean_object* v_c_419_; lean_object* v_a_420_; lean_object* v___x_421_; 
v_c_419_ = lean_ctor_get(v_t_412_, 0);
lean_inc_ref(v_c_419_);
v_a_420_ = lean_ctor_get(v_t_412_, 1);
lean_inc(v_a_420_);
lean_dec_ref_known(v_t_412_, 2);
v___x_421_ = lean_apply_2(v_k_413_, v_c_419_, v_a_420_);
return v___x_421_;
}
case 5:
{
lean_object* v_c_u2081_422_; lean_object* v_c_u2082_423_; lean_object* v___x_424_; 
v_c_u2081_422_ = lean_ctor_get(v_t_412_, 0);
lean_inc_ref(v_c_u2081_422_);
v_c_u2082_423_ = lean_ctor_get(v_t_412_, 1);
lean_inc_ref(v_c_u2082_423_);
lean_dec_ref_known(v_t_412_, 2);
v___x_424_ = lean_apply_2(v_k_413_, v_c_u2081_422_, v_c_u2082_423_);
return v___x_424_;
}
case 6:
{
lean_object* v_c_u2081_425_; lean_object* v_c_u2082_426_; lean_object* v___x_427_; 
v_c_u2081_425_ = lean_ctor_get(v_t_412_, 0);
lean_inc_ref(v_c_u2081_425_);
v_c_u2082_426_ = lean_ctor_get(v_t_412_, 1);
lean_inc_ref(v_c_u2082_426_);
lean_dec_ref_known(v_t_412_, 2);
v___x_427_ = lean_apply_2(v_k_413_, v_c_u2081_425_, v_c_u2082_426_);
return v___x_427_;
}
case 9:
{
lean_object* v_x_428_; lean_object* v_c_u2081_429_; lean_object* v_c_u2082_430_; lean_object* v___x_431_; 
v_x_428_ = lean_ctor_get(v_t_412_, 0);
lean_inc(v_x_428_);
v_c_u2081_429_ = lean_ctor_get(v_t_412_, 1);
lean_inc_ref(v_c_u2081_429_);
v_c_u2082_430_ = lean_ctor_get(v_t_412_, 2);
lean_inc_ref(v_c_u2082_430_);
lean_dec_ref_known(v_t_412_, 3);
v___x_431_ = lean_apply_3(v_k_413_, v_x_428_, v_c_u2081_429_, v_c_u2082_430_);
return v___x_431_;
}
case 13:
{
lean_object* v_c_432_; lean_object* v_e_433_; lean_object* v_p_434_; lean_object* v___x_435_; 
v_c_432_ = lean_ctor_get(v_t_412_, 0);
lean_inc_ref(v_c_432_);
v_e_433_ = lean_ctor_get(v_t_412_, 1);
lean_inc_ref(v_e_433_);
v_p_434_ = lean_ctor_get(v_t_412_, 2);
lean_inc_ref(v_p_434_);
lean_dec_ref_known(v_t_412_, 3);
v___x_435_ = lean_apply_3(v_k_413_, v_c_432_, v_e_433_, v_p_434_);
return v___x_435_;
}
default: 
{
lean_object* v_e_436_; lean_object* v___x_437_; 
v_e_436_ = lean_ctor_get(v_t_412_, 0);
lean_inc_ref(v_e_436_);
lean_dec_ref(v_t_412_);
v___x_437_ = lean_apply_1(v_k_413_, v_e_436_);
return v___x_437_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim(lean_object* v_motive__7_438_, lean_object* v_ctorIdx_439_, lean_object* v_t_440_, lean_object* v_h_441_, lean_object* v_k_442_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_440_, v_k_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___boxed(lean_object* v_motive__7_444_, lean_object* v_ctorIdx_445_, lean_object* v_t_446_, lean_object* v_h_447_, lean_object* v_k_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim(v_motive__7_444_, v_ctorIdx_445_, v_t_446_, v_h_447_, v_k_448_);
lean_dec(v_ctorIdx_445_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_core_elim___redArg(lean_object* v_t_450_, lean_object* v_core_451_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_450_, v_core_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_core_elim(lean_object* v_motive__7_453_, lean_object* v_t_454_, lean_object* v_h_455_, lean_object* v_core_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_454_, v_core_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_coreOfNat_elim___redArg(lean_object* v_t_458_, lean_object* v_coreOfNat_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_458_, v_coreOfNat_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_coreOfNat_elim(lean_object* v_motive__7_461_, lean_object* v_t_462_, lean_object* v_h_463_, lean_object* v_coreOfNat_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_462_, v_coreOfNat_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_norm_elim___redArg(lean_object* v_t_466_, lean_object* v_norm_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_466_, v_norm_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_norm_elim(lean_object* v_motive__7_469_, lean_object* v_t_470_, lean_object* v_h_471_, lean_object* v_norm_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_470_, v_norm_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_divCoeffs_elim___redArg(lean_object* v_t_474_, lean_object* v_divCoeffs_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_474_, v_divCoeffs_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_divCoeffs_elim(lean_object* v_motive__7_477_, lean_object* v_t_478_, lean_object* v_h_479_, lean_object* v_divCoeffs_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_478_, v_divCoeffs_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_bmodCoeffs_elim___redArg(lean_object* v_t_482_, lean_object* v_bmodCoeffs_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_482_, v_bmodCoeffs_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_bmodCoeffs_elim(lean_object* v_motive__7_485_, lean_object* v_t_486_, lean_object* v_h_487_, lean_object* v_bmodCoeffs_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_486_, v_bmodCoeffs_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveCombine_elim___redArg(lean_object* v_t_490_, lean_object* v_solveCombine_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_490_, v_solveCombine_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveCombine_elim(lean_object* v_motive__7_493_, lean_object* v_t_494_, lean_object* v_h_495_, lean_object* v_solveCombine_496_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_494_, v_solveCombine_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveElim_elim___redArg(lean_object* v_t_498_, lean_object* v_solveElim_499_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_498_, v_solveElim_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveElim_elim(lean_object* v_motive__7_501_, lean_object* v_t_502_, lean_object* v_h_503_, lean_object* v_solveElim_504_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_502_, v_solveElim_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_elim_elim___redArg(lean_object* v_t_506_, lean_object* v_elim_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_506_, v_elim_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_elim_elim(lean_object* v_motive__7_509_, lean_object* v_t_510_, lean_object* v_h_511_, lean_object* v_elim_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_510_, v_elim_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ofEqZero_elim___redArg(lean_object* v_t_514_, lean_object* v_ofEqZero_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_514_, v_ofEqZero_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ofEqZero_elim(lean_object* v_motive__7_517_, lean_object* v_t_518_, lean_object* v_h_519_, lean_object* v_ofEqZero_520_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_518_, v_ofEqZero_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_subst_elim___redArg(lean_object* v_t_522_, lean_object* v_subst_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_522_, v_subst_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_subst_elim(lean_object* v_motive__7_525_, lean_object* v_t_526_, lean_object* v_h_527_, lean_object* v_subst_528_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_526_, v_subst_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2081_elim___redArg(lean_object* v_t_530_, lean_object* v_cooper_u2081_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_530_, v_cooper_u2081_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2081_elim(lean_object* v_motive__7_533_, lean_object* v_t_534_, lean_object* v_h_535_, lean_object* v_cooper_u2081_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_534_, v_cooper_u2081_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2082_elim___redArg(lean_object* v_t_538_, lean_object* v_cooper_u2082_539_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_538_, v_cooper_u2082_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2082_elim(lean_object* v_motive__7_541_, lean_object* v_t_542_, lean_object* v_h_543_, lean_object* v_cooper_u2082_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_542_, v_cooper_u2082_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_reorder_elim___redArg(lean_object* v_t_546_, lean_object* v_reorder_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_546_, v_reorder_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_reorder_elim(lean_object* v_motive__7_549_, lean_object* v_t_550_, lean_object* v_h_551_, lean_object* v_reorder_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_550_, v_reorder_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_commRingNorm_elim___redArg(lean_object* v_t_554_, lean_object* v_commRingNorm_555_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_554_, v_commRingNorm_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_commRingNorm_elim(lean_object* v_motive__7_557_, lean_object* v_t_558_, lean_object* v_h_559_, lean_object* v_commRingNorm_560_){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_558_, v_commRingNorm_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorIdx___impl(lean_object* v_x_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = lean_obj_tag_nat(v_x_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorIdx___impl___boxed(lean_object* v_x_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorIdx___impl(v_x_564_);
lean_dec_ref(v_x_564_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(lean_object* v_t_566_, lean_object* v_k_567_){
_start:
{
switch(lean_obj_tag(v_t_566_))
{
case 1:
{
lean_object* v_e_568_; lean_object* v_p_569_; lean_object* v___x_570_; 
v_e_568_ = lean_ctor_get(v_t_566_, 0);
lean_inc_ref(v_e_568_);
v_p_569_ = lean_ctor_get(v_t_566_, 1);
lean_inc_ref(v_p_569_);
lean_dec_ref_known(v_t_566_, 2);
v___x_570_ = lean_apply_2(v_k_567_, v_e_568_, v_p_569_);
return v___x_570_;
}
case 2:
{
lean_object* v_e_571_; uint8_t v_pos_572_; lean_object* v_toIntThm_573_; lean_object* v_lhs_574_; lean_object* v_rhs_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v_e_571_ = lean_ctor_get(v_t_566_, 0);
lean_inc_ref(v_e_571_);
v_pos_572_ = lean_ctor_get_uint8(v_t_566_, sizeof(void*)*4);
v_toIntThm_573_ = lean_ctor_get(v_t_566_, 1);
lean_inc_ref(v_toIntThm_573_);
v_lhs_574_ = lean_ctor_get(v_t_566_, 2);
lean_inc_ref(v_lhs_574_);
v_rhs_575_ = lean_ctor_get(v_t_566_, 3);
lean_inc_ref(v_rhs_575_);
lean_dec_ref_known(v_t_566_, 4);
v___x_576_ = lean_box(v_pos_572_);
v___x_577_ = lean_apply_5(v_k_567_, v_e_571_, v___x_576_, v_toIntThm_573_, v_lhs_574_, v_rhs_575_);
return v___x_577_;
}
case 3:
{
lean_object* v_e_578_; uint8_t v_pos_579_; lean_object* v_lhs_580_; lean_object* v_rhs_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v_e_578_ = lean_ctor_get(v_t_566_, 0);
lean_inc_ref(v_e_578_);
v_pos_579_ = lean_ctor_get_uint8(v_t_566_, sizeof(void*)*3);
v_lhs_580_ = lean_ctor_get(v_t_566_, 1);
lean_inc_ref(v_lhs_580_);
v_rhs_581_ = lean_ctor_get(v_t_566_, 2);
lean_inc_ref(v_rhs_581_);
lean_dec_ref_known(v_t_566_, 3);
v___x_582_ = lean_box(v_pos_579_);
v___x_583_ = lean_apply_4(v_k_567_, v_e_578_, v___x_582_, v_lhs_580_, v_rhs_581_);
return v___x_583_;
}
case 5:
{
lean_object* v_h_584_; lean_object* v_lhs_585_; lean_object* v_rhs_586_; lean_object* v___x_587_; 
v_h_584_ = lean_ctor_get(v_t_566_, 0);
lean_inc_ref(v_h_584_);
v_lhs_585_ = lean_ctor_get(v_t_566_, 1);
lean_inc_ref(v_lhs_585_);
v_rhs_586_ = lean_ctor_get(v_t_566_, 2);
lean_inc_ref(v_rhs_586_);
lean_dec_ref_known(v_t_566_, 3);
v___x_587_ = lean_apply_3(v_k_567_, v_h_584_, v_lhs_585_, v_rhs_586_);
return v___x_587_;
}
case 7:
{
lean_object* v_h_588_; lean_object* v___x_589_; 
v_h_588_ = lean_ctor_get(v_t_566_, 0);
lean_inc(v_h_588_);
lean_dec_ref_known(v_t_566_, 1);
v___x_589_ = lean_apply_1(v_k_567_, v_h_588_);
return v___x_589_;
}
case 10:
{
lean_object* v_c_u2081_590_; lean_object* v_c_u2082_591_; lean_object* v___x_592_; 
v_c_u2081_590_ = lean_ctor_get(v_t_566_, 0);
lean_inc_ref(v_c_u2081_590_);
v_c_u2082_591_ = lean_ctor_get(v_t_566_, 1);
lean_inc_ref(v_c_u2082_591_);
lean_dec_ref_known(v_t_566_, 2);
v___x_592_ = lean_apply_2(v_k_567_, v_c_u2081_590_, v_c_u2082_591_);
return v___x_592_;
}
case 11:
{
lean_object* v_c_u2081_593_; lean_object* v_c_u2082_594_; lean_object* v_k_595_; lean_object* v___x_596_; 
v_c_u2081_593_ = lean_ctor_get(v_t_566_, 0);
lean_inc_ref(v_c_u2081_593_);
v_c_u2082_594_ = lean_ctor_get(v_t_566_, 1);
lean_inc_ref(v_c_u2082_594_);
v_k_595_ = lean_ctor_get(v_t_566_, 2);
lean_inc(v_k_595_);
lean_dec_ref_known(v_t_566_, 3);
v___x_596_ = lean_apply_3(v_k_567_, v_c_u2081_593_, v_c_u2082_594_, v_k_595_);
return v___x_596_;
}
case 12:
{
lean_object* v_x_597_; lean_object* v_c_u2081_598_; lean_object* v_c_u2082_599_; lean_object* v___x_600_; 
v_x_597_ = lean_ctor_get(v_t_566_, 0);
lean_inc(v_x_597_);
v_c_u2081_598_ = lean_ctor_get(v_t_566_, 1);
lean_inc_ref(v_c_u2081_598_);
v_c_u2082_599_ = lean_ctor_get(v_t_566_, 2);
lean_inc_ref(v_c_u2082_599_);
lean_dec_ref_known(v_t_566_, 3);
v___x_600_ = lean_apply_3(v_k_567_, v_x_597_, v_c_u2081_598_, v_c_u2082_599_);
return v___x_600_;
}
case 13:
{
lean_object* v_c_u2081_601_; lean_object* v_c_u2082_602_; lean_object* v___x_603_; 
v_c_u2081_601_ = lean_ctor_get(v_t_566_, 0);
lean_inc_ref(v_c_u2081_601_);
v_c_u2082_602_ = lean_ctor_get(v_t_566_, 1);
lean_inc_ref(v_c_u2082_602_);
lean_dec_ref_known(v_t_566_, 2);
v___x_603_ = lean_apply_2(v_k_567_, v_c_u2081_601_, v_c_u2082_602_);
return v___x_603_;
}
case 14:
{
lean_object* v_c_u2081_604_; lean_object* v_decVar_605_; lean_object* v_h_606_; lean_object* v_decVars_607_; lean_object* v___x_608_; 
v_c_u2081_604_ = lean_ctor_get(v_t_566_, 0);
lean_inc_ref(v_c_u2081_604_);
v_decVar_605_ = lean_ctor_get(v_t_566_, 1);
lean_inc(v_decVar_605_);
v_h_606_ = lean_ctor_get(v_t_566_, 2);
lean_inc_ref(v_h_606_);
v_decVars_607_ = lean_ctor_get(v_t_566_, 3);
lean_inc_ref(v_decVars_607_);
lean_dec_ref_known(v_t_566_, 4);
v___x_608_ = lean_apply_4(v_k_567_, v_c_u2081_604_, v_decVar_605_, v_h_606_, v_decVars_607_);
return v___x_608_;
}
case 16:
{
lean_object* v_c_u2081_609_; lean_object* v_c_u2082_610_; lean_object* v_t_611_; lean_object* v_g_612_; lean_object* v___x_613_; 
v_c_u2081_609_ = lean_ctor_get(v_t_566_, 0);
lean_inc_ref(v_c_u2081_609_);
v_c_u2082_610_ = lean_ctor_get(v_t_566_, 1);
lean_inc_ref(v_c_u2082_610_);
v_t_611_ = lean_ctor_get(v_t_566_, 2);
lean_inc(v_t_611_);
v_g_612_ = lean_ctor_get(v_t_566_, 3);
lean_inc(v_g_612_);
lean_dec_ref_known(v_t_566_, 4);
v___x_613_ = lean_apply_4(v_k_567_, v_c_u2081_609_, v_c_u2082_610_, v_t_611_, v_g_612_);
return v___x_613_;
}
case 17:
{
lean_object* v_e_614_; lean_object* v_support_615_; lean_object* v___x_616_; 
v_e_614_ = lean_ctor_get(v_t_566_, 0);
lean_inc_ref(v_e_614_);
v_support_615_ = lean_ctor_get(v_t_566_, 1);
lean_inc_ref(v_support_615_);
lean_dec_ref_known(v_t_566_, 2);
v___x_616_ = lean_apply_2(v_k_567_, v_e_614_, v_support_615_);
return v___x_616_;
}
case 19:
{
lean_object* v_c_617_; lean_object* v_e_618_; lean_object* v_p_619_; lean_object* v___x_620_; 
v_c_617_ = lean_ctor_get(v_t_566_, 0);
lean_inc_ref(v_c_617_);
v_e_618_ = lean_ctor_get(v_t_566_, 1);
lean_inc_ref(v_e_618_);
v_p_619_ = lean_ctor_get(v_t_566_, 2);
lean_inc_ref(v_p_619_);
lean_dec_ref_known(v_t_566_, 3);
v___x_620_ = lean_apply_3(v_k_567_, v_c_617_, v_e_618_, v_p_619_);
return v___x_620_;
}
default: 
{
lean_object* v_e_621_; lean_object* v___x_622_; 
v_e_621_ = lean_ctor_get(v_t_566_, 0);
lean_inc_ref(v_e_621_);
lean_dec_ref(v_t_566_);
v___x_622_ = lean_apply_1(v_k_567_, v_e_621_);
return v___x_622_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim(lean_object* v_motive__9_623_, lean_object* v_ctorIdx_624_, lean_object* v_t_625_, lean_object* v_h_626_, lean_object* v_k_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_625_, v_k_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___boxed(lean_object* v_motive__9_629_, lean_object* v_ctorIdx_630_, lean_object* v_t_631_, lean_object* v_h_632_, lean_object* v_k_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim(v_motive__9_629_, v_ctorIdx_630_, v_t_631_, v_h_632_, v_k_633_);
lean_dec(v_ctorIdx_630_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_core_elim___redArg(lean_object* v_t_635_, lean_object* v_core_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_635_, v_core_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_core_elim(lean_object* v_motive__9_638_, lean_object* v_t_639_, lean_object* v_h_640_, lean_object* v_core_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_639_, v_core_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreNeg_elim___redArg(lean_object* v_t_643_, lean_object* v_coreNeg_644_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_643_, v_coreNeg_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreNeg_elim(lean_object* v_motive__9_646_, lean_object* v_t_647_, lean_object* v_h_648_, lean_object* v_coreNeg_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_647_, v_coreNeg_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreToInt_elim___redArg(lean_object* v_t_651_, lean_object* v_coreToInt_652_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_651_, v_coreToInt_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreToInt_elim(lean_object* v_motive__9_654_, lean_object* v_t_655_, lean_object* v_h_656_, lean_object* v_coreToInt_657_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_655_, v_coreToInt_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreExpr_elim___redArg(lean_object* v_t_659_, lean_object* v_coreExpr_660_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_659_, v_coreExpr_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreExpr_elim(lean_object* v_motive__9_662_, lean_object* v_t_663_, lean_object* v_h_664_, lean_object* v_coreExpr_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_663_, v_coreExpr_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofNatNonneg_elim___redArg(lean_object* v_t_667_, lean_object* v_ofNatNonneg_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_667_, v_ofNatNonneg_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofNatNonneg_elim(lean_object* v_motive__9_670_, lean_object* v_t_671_, lean_object* v_h_672_, lean_object* v_ofNatNonneg_673_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_671_, v_ofNatNonneg_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_hyp_elim___redArg(lean_object* v_t_675_, lean_object* v_hyp_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_675_, v_hyp_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_hyp_elim(lean_object* v_motive__9_678_, lean_object* v_t_679_, lean_object* v_h_680_, lean_object* v_hyp_681_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_679_, v_hyp_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_bound_elim___redArg(lean_object* v_t_683_, lean_object* v_bound_684_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_683_, v_bound_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_bound_elim(lean_object* v_motive__9_686_, lean_object* v_t_687_, lean_object* v_h_688_, lean_object* v_bound_689_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_687_, v_bound_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dec_elim___redArg(lean_object* v_t_691_, lean_object* v_dec_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_691_, v_dec_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dec_elim(lean_object* v_motive__9_694_, lean_object* v_t_695_, lean_object* v_h_696_, lean_object* v_dec_697_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_695_, v_dec_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_norm_elim___redArg(lean_object* v_t_699_, lean_object* v_norm_700_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_699_, v_norm_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_norm_elim(lean_object* v_motive__9_702_, lean_object* v_t_703_, lean_object* v_h_704_, lean_object* v_norm_705_){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_703_, v_norm_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_divCoeffs_elim___redArg(lean_object* v_t_707_, lean_object* v_divCoeffs_708_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_707_, v_divCoeffs_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_divCoeffs_elim(lean_object* v_motive__9_710_, lean_object* v_t_711_, lean_object* v_h_712_, lean_object* v_divCoeffs_713_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_711_, v_divCoeffs_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combine_elim___redArg(lean_object* v_t_715_, lean_object* v_combine_716_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_715_, v_combine_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combine_elim(lean_object* v_motive__9_718_, lean_object* v_t_719_, lean_object* v_h_720_, lean_object* v_combine_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_719_, v_combine_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combineDivCoeffs_elim___redArg(lean_object* v_t_723_, lean_object* v_combineDivCoeffs_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_723_, v_combineDivCoeffs_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combineDivCoeffs_elim(lean_object* v_motive__9_726_, lean_object* v_t_727_, lean_object* v_h_728_, lean_object* v_combineDivCoeffs_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_727_, v_combineDivCoeffs_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_subst_elim___redArg(lean_object* v_t_731_, lean_object* v_subst_732_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_731_, v_subst_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_subst_elim(lean_object* v_motive__9_734_, lean_object* v_t_735_, lean_object* v_h_736_, lean_object* v_subst_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_735_, v_subst_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofLeDiseq_elim___redArg(lean_object* v_t_739_, lean_object* v_ofLeDiseq_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_739_, v_ofLeDiseq_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofLeDiseq_elim(lean_object* v_motive__9_742_, lean_object* v_t_743_, lean_object* v_h_744_, lean_object* v_ofLeDiseq_745_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_743_, v_ofLeDiseq_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofDiseqSplit_elim___redArg(lean_object* v_t_747_, lean_object* v_ofDiseqSplit_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_747_, v_ofDiseqSplit_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofDiseqSplit_elim(lean_object* v_motive__9_750_, lean_object* v_t_751_, lean_object* v_h_752_, lean_object* v_ofDiseqSplit_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_751_, v_ofDiseqSplit_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_cooper_elim___redArg(lean_object* v_t_755_, lean_object* v_cooper_756_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_755_, v_cooper_756_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_cooper_elim(lean_object* v_motive__9_758_, lean_object* v_t_759_, lean_object* v_h_760_, lean_object* v_cooper_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_759_, v_cooper_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dvdTightMod_elim___redArg(lean_object* v_t_763_, lean_object* v_dvdTightMod_764_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_763_, v_dvdTightMod_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dvdTightMod_elim(lean_object* v_motive__9_766_, lean_object* v_t_767_, lean_object* v_h_768_, lean_object* v_dvdTightMod_769_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_767_, v_dvdTightMod_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_orHull_elim___redArg(lean_object* v_t_771_, lean_object* v_orHull_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_771_, v_orHull_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_orHull_elim(lean_object* v_motive__9_774_, lean_object* v_t_775_, lean_object* v_h_776_, lean_object* v_orHull_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_775_, v_orHull_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_reorder_elim___redArg(lean_object* v_t_779_, lean_object* v_reorder_780_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_779_, v_reorder_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_reorder_elim(lean_object* v_motive__9_782_, lean_object* v_t_783_, lean_object* v_h_784_, lean_object* v_reorder_785_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_783_, v_reorder_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_commRingNorm_elim___redArg(lean_object* v_t_787_, lean_object* v_commRingNorm_788_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_787_, v_commRingNorm_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_commRingNorm_elim(lean_object* v_motive__9_790_, lean_object* v_t_791_, lean_object* v_h_792_, lean_object* v_commRingNorm_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_791_, v_commRingNorm_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorIdx___impl(lean_object* v_x_795_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = lean_obj_tag_nat(v_x_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorIdx___impl___boxed(lean_object* v_x_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorIdx___impl(v_x_797_);
lean_dec_ref(v_x_797_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(lean_object* v_t_799_, lean_object* v_k_800_){
_start:
{
switch(lean_obj_tag(v_t_799_))
{
case 0:
{
lean_object* v_a_801_; lean_object* v_zero_802_; lean_object* v___x_803_; 
v_a_801_ = lean_ctor_get(v_t_799_, 0);
lean_inc_ref(v_a_801_);
v_zero_802_ = lean_ctor_get(v_t_799_, 1);
lean_inc_ref(v_zero_802_);
lean_dec_ref_known(v_t_799_, 2);
v___x_803_ = lean_apply_2(v_k_800_, v_a_801_, v_zero_802_);
return v___x_803_;
}
case 1:
{
lean_object* v_a_804_; lean_object* v_b_805_; lean_object* v_p_u2081_806_; lean_object* v_p_u2082_807_; lean_object* v___x_808_; 
v_a_804_ = lean_ctor_get(v_t_799_, 0);
lean_inc_ref(v_a_804_);
v_b_805_ = lean_ctor_get(v_t_799_, 1);
lean_inc_ref(v_b_805_);
v_p_u2081_806_ = lean_ctor_get(v_t_799_, 2);
lean_inc_ref(v_p_u2081_806_);
v_p_u2082_807_ = lean_ctor_get(v_t_799_, 3);
lean_inc_ref(v_p_u2082_807_);
lean_dec_ref_known(v_t_799_, 4);
v___x_808_ = lean_apply_4(v_k_800_, v_a_804_, v_b_805_, v_p_u2081_806_, v_p_u2082_807_);
return v___x_808_;
}
case 2:
{
lean_object* v_a_809_; lean_object* v_b_810_; lean_object* v_toIntThm_811_; lean_object* v_lhs_812_; lean_object* v_rhs_813_; lean_object* v___x_814_; 
v_a_809_ = lean_ctor_get(v_t_799_, 0);
lean_inc_ref(v_a_809_);
v_b_810_ = lean_ctor_get(v_t_799_, 1);
lean_inc_ref(v_b_810_);
v_toIntThm_811_ = lean_ctor_get(v_t_799_, 2);
lean_inc_ref(v_toIntThm_811_);
v_lhs_812_ = lean_ctor_get(v_t_799_, 3);
lean_inc_ref(v_lhs_812_);
v_rhs_813_ = lean_ctor_get(v_t_799_, 4);
lean_inc_ref(v_rhs_813_);
lean_dec_ref_known(v_t_799_, 5);
v___x_814_ = lean_apply_5(v_k_800_, v_a_809_, v_b_810_, v_toIntThm_811_, v_lhs_812_, v_rhs_813_);
return v___x_814_;
}
case 6:
{
lean_object* v_x_815_; lean_object* v_c_u2081_816_; lean_object* v_c_u2082_817_; lean_object* v___x_818_; 
v_x_815_ = lean_ctor_get(v_t_799_, 0);
lean_inc(v_x_815_);
v_c_u2081_816_ = lean_ctor_get(v_t_799_, 1);
lean_inc_ref(v_c_u2081_816_);
v_c_u2082_817_ = lean_ctor_get(v_t_799_, 2);
lean_inc_ref(v_c_u2082_817_);
lean_dec_ref_known(v_t_799_, 3);
v___x_818_ = lean_apply_3(v_k_800_, v_x_815_, v_c_u2081_816_, v_c_u2082_817_);
return v___x_818_;
}
case 8:
{
lean_object* v_c_819_; lean_object* v_e_820_; lean_object* v_p_821_; lean_object* v___x_822_; 
v_c_819_ = lean_ctor_get(v_t_799_, 0);
lean_inc_ref(v_c_819_);
v_e_820_ = lean_ctor_get(v_t_799_, 1);
lean_inc_ref(v_e_820_);
v_p_821_ = lean_ctor_get(v_t_799_, 2);
lean_inc_ref(v_p_821_);
lean_dec_ref_known(v_t_799_, 3);
v___x_822_ = lean_apply_3(v_k_800_, v_c_819_, v_e_820_, v_p_821_);
return v___x_822_;
}
default: 
{
lean_object* v_c_823_; lean_object* v___x_824_; 
v_c_823_ = lean_ctor_get(v_t_799_, 0);
lean_inc_ref(v_c_823_);
lean_dec_ref(v_t_799_);
v___x_824_ = lean_apply_1(v_k_800_, v_c_823_);
return v___x_824_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim(lean_object* v_motive__11_825_, lean_object* v_ctorIdx_826_, lean_object* v_t_827_, lean_object* v_h_828_, lean_object* v_k_829_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_827_, v_k_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___boxed(lean_object* v_motive__11_831_, lean_object* v_ctorIdx_832_, lean_object* v_t_833_, lean_object* v_h_834_, lean_object* v_k_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim(v_motive__11_831_, v_ctorIdx_832_, v_t_833_, v_h_834_, v_k_835_);
lean_dec(v_ctorIdx_832_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core0_elim___redArg(lean_object* v_t_837_, lean_object* v_core0_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_837_, v_core0_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core0_elim(lean_object* v_motive__11_840_, lean_object* v_t_841_, lean_object* v_h_842_, lean_object* v_core0_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_841_, v_core0_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core_elim___redArg(lean_object* v_t_845_, lean_object* v_core_846_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_845_, v_core_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core_elim(lean_object* v_motive__11_848_, lean_object* v_t_849_, lean_object* v_h_850_, lean_object* v_core_851_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_849_, v_core_851_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_coreToInt_elim___redArg(lean_object* v_t_853_, lean_object* v_coreToInt_854_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_853_, v_coreToInt_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_coreToInt_elim(lean_object* v_motive__11_856_, lean_object* v_t_857_, lean_object* v_h_858_, lean_object* v_coreToInt_859_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_857_, v_coreToInt_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_norm_elim___redArg(lean_object* v_t_861_, lean_object* v_norm_862_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_861_, v_norm_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_norm_elim(lean_object* v_motive__11_864_, lean_object* v_t_865_, lean_object* v_h_866_, lean_object* v_norm_867_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_865_, v_norm_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_divCoeffs_elim___redArg(lean_object* v_t_869_, lean_object* v_divCoeffs_870_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_869_, v_divCoeffs_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_divCoeffs_elim(lean_object* v_motive__11_872_, lean_object* v_t_873_, lean_object* v_h_874_, lean_object* v_divCoeffs_875_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_873_, v_divCoeffs_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_neg_elim___redArg(lean_object* v_t_877_, lean_object* v_neg_878_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_877_, v_neg_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_neg_elim(lean_object* v_motive__11_880_, lean_object* v_t_881_, lean_object* v_h_882_, lean_object* v_neg_883_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_881_, v_neg_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_subst_elim___redArg(lean_object* v_t_885_, lean_object* v_subst_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_885_, v_subst_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_subst_elim(lean_object* v_motive__11_888_, lean_object* v_t_889_, lean_object* v_h_890_, lean_object* v_subst_891_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_889_, v_subst_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_reorder_elim___redArg(lean_object* v_t_893_, lean_object* v_reorder_894_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_893_, v_reorder_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_reorder_elim(lean_object* v_motive__11_896_, lean_object* v_t_897_, lean_object* v_h_898_, lean_object* v_reorder_899_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_897_, v_reorder_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_commRingNorm_elim___redArg(lean_object* v_t_901_, lean_object* v_commRingNorm_902_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_901_, v_commRingNorm_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_commRingNorm_elim(lean_object* v_motive__11_904_, lean_object* v_t_905_, lean_object* v_h_906_, lean_object* v_commRingNorm_907_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_905_, v_commRingNorm_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorIdx___impl(lean_object* v_x_909_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = lean_obj_tag_nat(v_x_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorIdx___impl___boxed(lean_object* v_x_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorIdx___impl(v_x_911_);
lean_dec_ref(v_x_911_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(lean_object* v_t_913_, lean_object* v_k_914_){
_start:
{
if (lean_obj_tag(v_t_913_) == 4)
{
lean_object* v_c_u2081_915_; lean_object* v_c_u2082_916_; lean_object* v_c_u2083_917_; lean_object* v___x_918_; 
v_c_u2081_915_ = lean_ctor_get(v_t_913_, 0);
lean_inc_ref(v_c_u2081_915_);
v_c_u2082_916_ = lean_ctor_get(v_t_913_, 1);
lean_inc_ref(v_c_u2082_916_);
v_c_u2083_917_ = lean_ctor_get(v_t_913_, 2);
lean_inc_ref(v_c_u2083_917_);
lean_dec_ref_known(v_t_913_, 3);
v___x_918_ = lean_apply_3(v_k_914_, v_c_u2081_915_, v_c_u2082_916_, v_c_u2083_917_);
return v___x_918_;
}
else
{
lean_object* v_c_919_; lean_object* v___x_920_; 
v_c_919_ = lean_ctor_get(v_t_913_, 0);
lean_inc_ref(v_c_919_);
lean_dec_ref(v_t_913_);
v___x_920_ = lean_apply_1(v_k_914_, v_c_919_);
return v___x_920_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim(lean_object* v_motive__12_921_, lean_object* v_ctorIdx_922_, lean_object* v_t_923_, lean_object* v_h_924_, lean_object* v_k_925_){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_923_, v_k_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___boxed(lean_object* v_motive__12_927_, lean_object* v_ctorIdx_928_, lean_object* v_t_929_, lean_object* v_h_930_, lean_object* v_k_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim(v_motive__12_927_, v_ctorIdx_928_, v_t_929_, v_h_930_, v_k_931_);
lean_dec(v_ctorIdx_928_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_dvd_elim___redArg(lean_object* v_t_933_, lean_object* v_dvd_934_){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_933_, v_dvd_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_dvd_elim(lean_object* v_motive__12_936_, lean_object* v_t_937_, lean_object* v_h_938_, lean_object* v_dvd_939_){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_937_, v_dvd_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_le_elim___redArg(lean_object* v_t_941_, lean_object* v_le_942_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_941_, v_le_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_le_elim(lean_object* v_motive__12_944_, lean_object* v_t_945_, lean_object* v_h_946_, lean_object* v_le_947_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_945_, v_le_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_eq_elim___redArg(lean_object* v_t_949_, lean_object* v_eq_950_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_949_, v_eq_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_eq_elim(lean_object* v_motive__12_952_, lean_object* v_t_953_, lean_object* v_h_954_, lean_object* v_eq_955_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_953_, v_eq_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_diseq_elim___redArg(lean_object* v_t_957_, lean_object* v_diseq_958_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_957_, v_diseq_958_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_diseq_elim(lean_object* v_motive__12_960_, lean_object* v_t_961_, lean_object* v_h_962_, lean_object* v_diseq_963_){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_961_, v_diseq_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_cooper_elim___redArg(lean_object* v_t_965_, lean_object* v_cooper_966_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_965_, v_cooper_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_cooper_elim(lean_object* v_motive__12_968_, lean_object* v_t_969_, lean_object* v_h_970_, lean_object* v_cooper_971_){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_969_, v_cooper_971_);
return v___x_972_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0);
v___x_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_974_, 0, v___x_973_);
return v___x_974_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_978_ = lean_box(0);
v___x_979_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__2));
v___x_980_ = l_Lean_Expr_const___override(v___x_979_, v___x_978_);
return v___x_980_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3);
v___x_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
return v___x_982_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5(void){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_983_ = lean_box(0);
v___x_984_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4);
v___x_985_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0);
v___x_986_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
lean_ctor_set(v___x_986_, 1, v___x_984_);
lean_ctor_set(v___x_986_, 2, v___x_983_);
return v___x_986_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr(void){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5);
return v___x_987_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0(void){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3);
v___x_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
return v___x_989_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1(void){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_990_ = lean_box(0);
v___x_991_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0);
v___x_992_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0);
v___x_993_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0);
v___x_994_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
lean_ctor_set(v___x_994_, 1, v___x_992_);
lean_ctor_set(v___x_994_, 2, v___x_991_);
lean_ctor_set(v___x_994_, 3, v___x_990_);
return v___x_994_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr(void){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1);
return v___x_995_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0(void){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; uint8_t v___x_998_; lean_object* v___x_999_; 
v___x_996_ = lean_box(0);
v___x_997_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5);
v___x_998_ = 0;
v___x_999_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_999_, 0, v___x_997_);
lean_ctor_set(v___x_999_, 1, v___x_997_);
lean_ctor_set(v___x_999_, 2, v___x_996_);
lean_ctor_set_uint8(v___x_999_, sizeof(void*)*3, v___x_998_);
return v___x_999_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred(void){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0);
return v___x_1000_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1(void){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1003_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__0));
v___x_1004_ = lean_unsigned_to_nat(0u);
v___x_1005_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0);
v___x_1006_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
lean_ctor_set(v___x_1006_, 1, v___x_1004_);
lean_ctor_set(v___x_1006_, 2, v___x_1003_);
return v___x_1006_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit(void){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1);
return v___x_1007_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1008_; 
v___x_1008_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1008_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0);
v___x_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg(){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__1);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___boxed(lean_object* v___dummy_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg();
return v_res_1014_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg();
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0(lean_object* v_00_u03b2_1016_){
_start:
{
lean_object* v___x_1017_; 
v___x_1017_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0);
return v___x_1017_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0(void){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1018_ = lean_unsigned_to_nat(32u);
v___x_1019_ = lean_mk_empty_array_with_capacity(v___x_1018_);
v___x_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
return v___x_1020_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1(void){
_start:
{
size_t v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1021_ = ((size_t)5ULL);
v___x_1022_ = lean_unsigned_to_nat(0u);
v___x_1023_ = lean_unsigned_to_nat(32u);
v___x_1024_ = lean_mk_empty_array_with_capacity(v___x_1023_);
v___x_1025_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0);
v___x_1026_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
lean_ctor_set(v___x_1026_, 1, v___x_1024_);
lean_ctor_set(v___x_1026_, 2, v___x_1022_);
lean_ctor_set(v___x_1026_, 3, v___x_1022_);
lean_ctor_set_usize(v___x_1026_, 4, v___x_1021_);
return v___x_1026_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___redArg___closed__0);
v___x_1028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
return v___x_1028_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; uint8_t v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1029_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0);
v___x_1030_ = lean_box(0);
v___x_1031_ = 0;
v___x_1032_ = lean_unsigned_to_nat(0u);
v___x_1033_ = lean_box(0);
v___x_1034_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2);
v___x_1035_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1);
v___x_1036_ = lean_alloc_ctor(0, 22, 2);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
lean_ctor_set(v___x_1036_, 1, v___x_1034_);
lean_ctor_set(v___x_1036_, 2, v___x_1035_);
lean_ctor_set(v___x_1036_, 3, v___x_1034_);
lean_ctor_set(v___x_1036_, 4, v___x_1034_);
lean_ctor_set(v___x_1036_, 5, v___x_1035_);
lean_ctor_set(v___x_1036_, 6, v___x_1035_);
lean_ctor_set(v___x_1036_, 7, v___x_1035_);
lean_ctor_set(v___x_1036_, 8, v___x_1035_);
lean_ctor_set(v___x_1036_, 9, v___x_1035_);
lean_ctor_set(v___x_1036_, 10, v___x_1035_);
lean_ctor_set(v___x_1036_, 11, v___x_1033_);
lean_ctor_set(v___x_1036_, 12, v___x_1035_);
lean_ctor_set(v___x_1036_, 13, v___x_1035_);
lean_ctor_set(v___x_1036_, 14, v___x_1032_);
lean_ctor_set(v___x_1036_, 15, v___x_1032_);
lean_ctor_set(v___x_1036_, 16, v___x_1034_);
lean_ctor_set(v___x_1036_, 17, v___x_1032_);
lean_ctor_set(v___x_1036_, 18, v___x_1030_);
lean_ctor_set(v___x_1036_, 19, v___x_1034_);
lean_ctor_set(v___x_1036_, 20, v___x_1029_);
lean_ctor_set(v___x_1036_, 21, v___x_1034_);
lean_ctor_set_uint8(v___x_1036_, sizeof(void*)*22, v___x_1031_);
lean_ctor_set_uint8(v___x_1036_, sizeof(void*)*22 + 1, v___x_1031_);
return v___x_1036_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default(void){
_start:
{
lean_object* v___x_1037_; 
v___x_1037_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3);
return v___x_1037_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState(void){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default;
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(lean_object* v___x_1039_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1039_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2____boxed(lean_object* v___x_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(v___x_1042_);
return v_res_1044_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1045_; lean_object* v___f_1046_; 
v___x_1045_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3);
v___f_1046_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_1046_, 0, v___x_1045_);
return v___f_1046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_1048_; lean_object* v___x_1049_; 
v___f_1048_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_);
v___x_1049_ = l_Lean_Meta_Grind_registerSolverExtension___redArg(v___f_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2____boxed(lean_object* v_a_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_();
return v_res_1051_;
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
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullAtom_default = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullAtom_default();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullAtom_default);
l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullAtom = _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullAtom();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedOrHullAtom);
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
