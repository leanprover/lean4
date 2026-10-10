// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.Types
// Imports: public import Init.Grind.Ring.CommSolver public import Init.Grind.Ordered.Linarith public import Lean.Meta.Tactic.Grind.Types
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Grind_registerSolverExtension___redArg(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash___closed__0;
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_core_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_core_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_notCore_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_notCore_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_cancelDen_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_cancelDen_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_core_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_core_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_symm_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_symm_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_cancelDen_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_cancelDen_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_core_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_core_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_cancelDen_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_cancelDen_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_core_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_core_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_coreCommRing_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_coreCommRing_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_coreOfNat_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_coreOfNat_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_neg_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_neg_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_coeff_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_coeff_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_subst_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_subst_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_core_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_core_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_notCore_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_notCore_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ring_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ring_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_coreOfNat_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_coreOfNat_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_notCoreOfNat_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_notCoreOfNat_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_combine_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_combine_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_norm_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_norm_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_dec_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_dec_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ofDiseqSplit_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ofDiseqSplit_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_oneGtZero_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_oneGtZero_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ofEq_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ofEq_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ofEqOfNat_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ofEqOfNat_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ringEq_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ringEq_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_subst_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_subst_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_core_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_core_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ring_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ring_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_coreOfNat_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_coreOfNat_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_neg_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_neg_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_subst_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_subst_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_subst1_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_subst1_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_oneNeZero_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_oneNeZero_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_diseq_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_diseq_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_lt_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_lt_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__3;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__1;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__2;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__3;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0(lean_object*);
static const lean_array_object l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__1;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__2;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__3;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedState;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_linearExt;
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash___closed__0(void){
_start:
{
lean_object* v_natZero_1_; lean_object* v_intZero_2_; 
v_natZero_1_ = lean_unsigned_to_nat(0u);
v_intZero_2_ = lean_nat_to_int(v_natZero_1_);
return v_intZero_2_;
}
}
uint64_t l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash(lean_object* v_x_3_){
_start:
{
if (lean_obj_tag(v_x_3_) == 0)
{
uint64_t v___x_4_; 
v___x_4_ = 0ULL;
return v___x_4_;
}
else
{
lean_object* v_k_5_; lean_object* v_v_6_; lean_object* v_p_7_; uint64_t v___x_8_; uint64_t v___y_10_; lean_object* v_intZero_16_; uint8_t v_isNeg_17_; 
v_k_5_ = lean_ctor_get(v_x_3_, 0);
v_v_6_ = lean_ctor_get(v_x_3_, 1);
v_p_7_ = lean_ctor_get(v_x_3_, 2);
v___x_8_ = 1ULL;
v_intZero_16_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash___closed__0, &l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash___closed__0);
v_isNeg_17_ = lean_int_dec_lt(v_k_5_, v_intZero_16_);
if (v_isNeg_17_ == 0)
{
lean_object* v_a_18_; lean_object* v___x_19_; lean_object* v___x_20_; uint64_t v___x_21_; 
v_a_18_ = lean_nat_abs(v_k_5_);
v___x_19_ = lean_unsigned_to_nat(2u);
v___x_20_ = lean_nat_mul(v___x_19_, v_a_18_);
lean_dec(v_a_18_);
v___x_21_ = lean_uint64_of_nat(v___x_20_);
lean_dec(v___x_20_);
v___y_10_ = v___x_21_;
goto v___jp_9_;
}
else
{
lean_object* v_abs_22_; lean_object* v_one_23_; lean_object* v_a_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; uint64_t v___x_28_; 
v_abs_22_ = lean_nat_abs(v_k_5_);
v_one_23_ = lean_unsigned_to_nat(1u);
v_a_24_ = lean_nat_sub(v_abs_22_, v_one_23_);
lean_dec(v_abs_22_);
v___x_25_ = lean_unsigned_to_nat(2u);
v___x_26_ = lean_nat_mul(v___x_25_, v_a_24_);
lean_dec(v_a_24_);
v___x_27_ = lean_nat_add(v___x_26_, v_one_23_);
lean_dec(v___x_26_);
v___x_28_ = lean_uint64_of_nat(v___x_27_);
lean_dec(v___x_27_);
v___y_10_ = v___x_28_;
goto v___jp_9_;
}
v___jp_9_:
{
uint64_t v___x_11_; uint64_t v___x_12_; uint64_t v___x_13_; uint64_t v___x_14_; uint64_t v___x_15_; 
v___x_11_ = lean_uint64_mix_hash(v___x_8_, v___y_10_);
v___x_12_ = lean_uint64_of_nat(v_v_6_);
v___x_13_ = lean_uint64_mix_hash(v___x_11_, v___x_12_);
v___x_14_ = l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash(v_p_7_);
v___x_15_ = lean_uint64_mix_hash(v___x_13_, v___x_14_);
return v___x_15_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3_ = stack[0].m_obj;
uint64_t v_res_29_;
v_res_29_ = l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash(v_x_3_);
stack->m_num = v_res_29_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash___boxed(lean_object* v_x_30_){
_start:
{
uint64_t v_res_31_; lean_object* v_r_32_; 
v_res_31_ = l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash(v_x_30_);
lean_dec(v_x_30_);
v_r_32_ = lean_box_uint64(v_res_31_);
return v_r_32_;
}
}
uint64_t l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean_hash(lean_object* v_x_35_){
_start:
{
switch(lean_obj_tag(v_x_35_))
{
case 0:
{
uint64_t v___x_36_; 
v___x_36_ = 0ULL;
return v___x_36_;
}
case 1:
{
lean_object* v_i_37_; uint64_t v___x_38_; uint64_t v___x_39_; uint64_t v___x_40_; 
v_i_37_ = lean_ctor_get(v_x_35_, 0);
v___x_38_ = 1ULL;
v___x_39_ = lean_uint64_of_nat(v_i_37_);
v___x_40_ = lean_uint64_mix_hash(v___x_38_, v___x_39_);
return v___x_40_;
}
case 2:
{
lean_object* v_a_41_; lean_object* v_b_42_; uint64_t v___x_43_; uint64_t v___x_44_; uint64_t v___x_45_; uint64_t v___x_46_; uint64_t v___x_47_; 
v_a_41_ = lean_ctor_get(v_x_35_, 0);
v_b_42_ = lean_ctor_get(v_x_35_, 1);
v___x_43_ = 2ULL;
v___x_44_ = l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean_hash(v_a_41_);
v___x_45_ = lean_uint64_mix_hash(v___x_43_, v___x_44_);
v___x_46_ = l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean_hash(v_b_42_);
v___x_47_ = lean_uint64_mix_hash(v___x_45_, v___x_46_);
return v___x_47_;
}
case 3:
{
lean_object* v_a_48_; lean_object* v_b_49_; uint64_t v___x_50_; uint64_t v___x_51_; uint64_t v___x_52_; uint64_t v___x_53_; uint64_t v___x_54_; 
v_a_48_ = lean_ctor_get(v_x_35_, 0);
v_b_49_ = lean_ctor_get(v_x_35_, 1);
v___x_50_ = 3ULL;
v___x_51_ = l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean_hash(v_a_48_);
v___x_52_ = lean_uint64_mix_hash(v___x_50_, v___x_51_);
v___x_53_ = l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean_hash(v_b_49_);
v___x_54_ = lean_uint64_mix_hash(v___x_52_, v___x_53_);
return v___x_54_;
}
case 4:
{
lean_object* v_a_55_; uint64_t v___x_56_; uint64_t v___x_57_; uint64_t v___x_58_; 
v_a_55_ = lean_ctor_get(v_x_35_, 0);
v___x_56_ = 4ULL;
v___x_57_ = l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean_hash(v_a_55_);
v___x_58_ = lean_uint64_mix_hash(v___x_56_, v___x_57_);
return v___x_58_;
}
case 5:
{
lean_object* v_k_59_; lean_object* v_a_60_; uint64_t v___x_61_; uint64_t v___x_62_; uint64_t v___x_63_; uint64_t v___x_64_; uint64_t v___x_65_; 
v_k_59_ = lean_ctor_get(v_x_35_, 0);
v_a_60_ = lean_ctor_get(v_x_35_, 1);
v___x_61_ = 5ULL;
v___x_62_ = lean_uint64_of_nat(v_k_59_);
v___x_63_ = lean_uint64_mix_hash(v___x_61_, v___x_62_);
v___x_64_ = l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean_hash(v_a_60_);
v___x_65_ = lean_uint64_mix_hash(v___x_63_, v___x_64_);
return v___x_65_;
}
default: 
{
lean_object* v_k_66_; lean_object* v_a_67_; uint64_t v___x_68_; uint64_t v___y_70_; lean_object* v_intZero_74_; uint8_t v_isNeg_75_; 
v_k_66_ = lean_ctor_get(v_x_35_, 0);
v_a_67_ = lean_ctor_get(v_x_35_, 1);
v___x_68_ = 6ULL;
v_intZero_74_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash___closed__0, &l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash___closed__0);
v_isNeg_75_ = lean_int_dec_lt(v_k_66_, v_intZero_74_);
if (v_isNeg_75_ == 0)
{
lean_object* v_a_76_; lean_object* v___x_77_; lean_object* v___x_78_; uint64_t v___x_79_; 
v_a_76_ = lean_nat_abs(v_k_66_);
v___x_77_ = lean_unsigned_to_nat(2u);
v___x_78_ = lean_nat_mul(v___x_77_, v_a_76_);
lean_dec(v_a_76_);
v___x_79_ = lean_uint64_of_nat(v___x_78_);
lean_dec(v___x_78_);
v___y_70_ = v___x_79_;
goto v___jp_69_;
}
else
{
lean_object* v_abs_80_; lean_object* v_one_81_; lean_object* v_a_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; uint64_t v___x_86_; 
v_abs_80_ = lean_nat_abs(v_k_66_);
v_one_81_ = lean_unsigned_to_nat(1u);
v_a_82_ = lean_nat_sub(v_abs_80_, v_one_81_);
lean_dec(v_abs_80_);
v___x_83_ = lean_unsigned_to_nat(2u);
v___x_84_ = lean_nat_mul(v___x_83_, v_a_82_);
lean_dec(v_a_82_);
v___x_85_ = lean_nat_add(v___x_84_, v_one_81_);
lean_dec(v___x_84_);
v___x_86_ = lean_uint64_of_nat(v___x_85_);
lean_dec(v___x_85_);
v___y_70_ = v___x_86_;
goto v___jp_69_;
}
v___jp_69_:
{
uint64_t v___x_71_; uint64_t v___x_72_; uint64_t v___x_73_; 
v___x_71_ = lean_uint64_mix_hash(v___x_68_, v___y_70_);
v___x_72_ = l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean_hash(v_a_67_);
v___x_73_ = lean_uint64_mix_hash(v___x_71_, v___x_72_);
return v___x_73_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_35_ = stack[0].m_obj;
uint64_t v_res_87_;
v_res_87_ = l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean_hash(v_x_35_);
stack->m_num = v_res_87_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean_hash___boxed(lean_object* v_x_88_){
_start:
{
uint64_t v_res_89_; lean_object* v_r_90_; 
v_res_89_ = l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean_hash(v_x_88_);
lean_dec(v_x_88_);
v_r_90_ = lean_box_uint64(v_res_89_);
return v_r_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorIdx___impl(lean_object* v_x_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lean_obj_tag_nat(v_x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorIdx___impl___boxed(lean_object* v_x_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorIdx___impl(v_x_95_);
lean_dec_ref(v_x_95_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorElim___redArg(lean_object* v_t_97_, lean_object* v_k_98_){
_start:
{
if (lean_obj_tag(v_t_97_) == 2)
{
lean_object* v_c_99_; lean_object* v_val_100_; lean_object* v_x_101_; lean_object* v_n_102_; lean_object* v___x_103_; 
v_c_99_ = lean_ctor_get(v_t_97_, 0);
lean_inc_ref(v_c_99_);
v_val_100_ = lean_ctor_get(v_t_97_, 1);
lean_inc(v_val_100_);
v_x_101_ = lean_ctor_get(v_t_97_, 2);
lean_inc(v_x_101_);
v_n_102_ = lean_ctor_get(v_t_97_, 3);
lean_inc(v_n_102_);
lean_dec_ref_known(v_t_97_, 4);
v___x_103_ = lean_apply_4(v_k_98_, v_c_99_, v_val_100_, v_x_101_, v_n_102_);
return v___x_103_;
}
else
{
lean_object* v_e_104_; lean_object* v_lhs_105_; lean_object* v_rhs_106_; lean_object* v___x_107_; 
v_e_104_ = lean_ctor_get(v_t_97_, 0);
lean_inc_ref(v_e_104_);
v_lhs_105_ = lean_ctor_get(v_t_97_, 1);
lean_inc_ref(v_lhs_105_);
v_rhs_106_ = lean_ctor_get(v_t_97_, 2);
lean_inc_ref(v_rhs_106_);
lean_dec_ref(v_t_97_);
v___x_107_ = lean_apply_3(v_k_98_, v_e_104_, v_lhs_105_, v_rhs_106_);
return v___x_107_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorElim(lean_object* v_motive__2_108_, lean_object* v_ctorIdx_109_, lean_object* v_t_110_, lean_object* v_h_111_, lean_object* v_k_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorElim___redArg(v_t_110_, v_k_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorElim___boxed(lean_object* v_motive__2_114_, lean_object* v_ctorIdx_115_, lean_object* v_t_116_, lean_object* v_h_117_, lean_object* v_k_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorElim(v_motive__2_114_, v_ctorIdx_115_, v_t_116_, v_h_117_, v_k_118_);
lean_dec(v_ctorIdx_115_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_core_elim___redArg(lean_object* v_t_120_, lean_object* v_core_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorElim___redArg(v_t_120_, v_core_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_core_elim(lean_object* v_motive__2_123_, lean_object* v_t_124_, lean_object* v_h_125_, lean_object* v_core_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorElim___redArg(v_t_124_, v_core_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_notCore_elim___redArg(lean_object* v_t_128_, lean_object* v_notCore_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorElim___redArg(v_t_128_, v_notCore_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_notCore_elim(lean_object* v_motive__2_131_, lean_object* v_t_132_, lean_object* v_h_133_, lean_object* v_notCore_134_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorElim___redArg(v_t_132_, v_notCore_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_cancelDen_elim___redArg(lean_object* v_t_136_, lean_object* v_cancelDen_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorElim___redArg(v_t_136_, v_cancelDen_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_cancelDen_elim(lean_object* v_motive__2_139_, lean_object* v_t_140_, lean_object* v_h_141_, lean_object* v_cancelDen_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorElim___redArg(v_t_140_, v_cancelDen_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorIdx___impl(lean_object* v_x_144_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = lean_obj_tag_nat(v_x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorIdx___impl___boxed(lean_object* v_x_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorIdx___impl(v_x_146_);
lean_dec_ref(v_x_146_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___redArg(lean_object* v_t_148_, lean_object* v_k_149_){
_start:
{
switch(lean_obj_tag(v_t_148_))
{
case 0:
{
lean_object* v_a_150_; lean_object* v_b_151_; lean_object* v_ra_152_; lean_object* v_rb_153_; lean_object* v___x_154_; 
v_a_150_ = lean_ctor_get(v_t_148_, 0);
lean_inc_ref(v_a_150_);
v_b_151_ = lean_ctor_get(v_t_148_, 1);
lean_inc_ref(v_b_151_);
v_ra_152_ = lean_ctor_get(v_t_148_, 2);
lean_inc_ref(v_ra_152_);
v_rb_153_ = lean_ctor_get(v_t_148_, 3);
lean_inc_ref(v_rb_153_);
lean_dec_ref_known(v_t_148_, 4);
v___x_154_ = lean_apply_4(v_k_149_, v_a_150_, v_b_151_, v_ra_152_, v_rb_153_);
return v___x_154_;
}
case 1:
{
lean_object* v_c_155_; lean_object* v___x_156_; 
v_c_155_ = lean_ctor_get(v_t_148_, 0);
lean_inc_ref(v_c_155_);
lean_dec_ref_known(v_t_148_, 1);
v___x_156_ = lean_apply_1(v_k_149_, v_c_155_);
return v___x_156_;
}
default: 
{
lean_object* v_c_157_; lean_object* v_val_158_; lean_object* v_x_159_; lean_object* v_n_160_; lean_object* v___x_161_; 
v_c_157_ = lean_ctor_get(v_t_148_, 0);
lean_inc_ref(v_c_157_);
v_val_158_ = lean_ctor_get(v_t_148_, 1);
lean_inc(v_val_158_);
v_x_159_ = lean_ctor_get(v_t_148_, 2);
lean_inc(v_x_159_);
v_n_160_ = lean_ctor_get(v_t_148_, 3);
lean_inc(v_n_160_);
lean_dec_ref_known(v_t_148_, 4);
v___x_161_ = lean_apply_4(v_k_149_, v_c_157_, v_val_158_, v_x_159_, v_n_160_);
return v___x_161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim(lean_object* v_motive__2_162_, lean_object* v_ctorIdx_163_, lean_object* v_t_164_, lean_object* v_h_165_, lean_object* v_k_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___redArg(v_t_164_, v_k_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___boxed(lean_object* v_motive__2_168_, lean_object* v_ctorIdx_169_, lean_object* v_t_170_, lean_object* v_h_171_, lean_object* v_k_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim(v_motive__2_168_, v_ctorIdx_169_, v_t_170_, v_h_171_, v_k_172_);
lean_dec(v_ctorIdx_169_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_core_elim___redArg(lean_object* v_t_174_, lean_object* v_core_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___redArg(v_t_174_, v_core_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_core_elim(lean_object* v_motive__2_177_, lean_object* v_t_178_, lean_object* v_h_179_, lean_object* v_core_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___redArg(v_t_178_, v_core_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_symm_elim___redArg(lean_object* v_t_182_, lean_object* v_symm_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___redArg(v_t_182_, v_symm_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_symm_elim(lean_object* v_motive__2_185_, lean_object* v_t_186_, lean_object* v_h_187_, lean_object* v_symm_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___redArg(v_t_186_, v_symm_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_cancelDen_elim___redArg(lean_object* v_t_190_, lean_object* v_cancelDen_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___redArg(v_t_190_, v_cancelDen_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_cancelDen_elim(lean_object* v_motive__2_193_, lean_object* v_t_194_, lean_object* v_h_195_, lean_object* v_cancelDen_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___redArg(v_t_194_, v_cancelDen_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorIdx___impl(lean_object* v_x_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = lean_obj_tag_nat(v_x_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorIdx___impl___boxed(lean_object* v_x_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorIdx___impl(v_x_200_);
lean_dec_ref(v_x_200_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim___redArg(lean_object* v_t_202_, lean_object* v_k_203_){
_start:
{
if (lean_obj_tag(v_t_202_) == 0)
{
lean_object* v_a_204_; lean_object* v_b_205_; lean_object* v_ra_206_; lean_object* v_rb_207_; lean_object* v___x_208_; 
v_a_204_ = lean_ctor_get(v_t_202_, 0);
lean_inc_ref(v_a_204_);
v_b_205_ = lean_ctor_get(v_t_202_, 1);
lean_inc_ref(v_b_205_);
v_ra_206_ = lean_ctor_get(v_t_202_, 2);
lean_inc_ref(v_ra_206_);
v_rb_207_ = lean_ctor_get(v_t_202_, 3);
lean_inc_ref(v_rb_207_);
lean_dec_ref_known(v_t_202_, 4);
v___x_208_ = lean_apply_4(v_k_203_, v_a_204_, v_b_205_, v_ra_206_, v_rb_207_);
return v___x_208_;
}
else
{
lean_object* v_c_209_; lean_object* v_val_210_; lean_object* v_x_211_; lean_object* v_n_212_; lean_object* v___x_213_; 
v_c_209_ = lean_ctor_get(v_t_202_, 0);
lean_inc_ref(v_c_209_);
v_val_210_ = lean_ctor_get(v_t_202_, 1);
lean_inc(v_val_210_);
v_x_211_ = lean_ctor_get(v_t_202_, 2);
lean_inc(v_x_211_);
v_n_212_ = lean_ctor_get(v_t_202_, 3);
lean_inc(v_n_212_);
lean_dec_ref_known(v_t_202_, 4);
v___x_213_ = lean_apply_4(v_k_203_, v_c_209_, v_val_210_, v_x_211_, v_n_212_);
return v___x_213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim(lean_object* v_motive__2_214_, lean_object* v_ctorIdx_215_, lean_object* v_t_216_, lean_object* v_h_217_, lean_object* v_k_218_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim___redArg(v_t_216_, v_k_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim___boxed(lean_object* v_motive__2_220_, lean_object* v_ctorIdx_221_, lean_object* v_t_222_, lean_object* v_h_223_, lean_object* v_k_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim(v_motive__2_220_, v_ctorIdx_221_, v_t_222_, v_h_223_, v_k_224_);
lean_dec(v_ctorIdx_221_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_core_elim___redArg(lean_object* v_t_226_, lean_object* v_core_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim___redArg(v_t_226_, v_core_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_core_elim(lean_object* v_motive__2_229_, lean_object* v_t_230_, lean_object* v_h_231_, lean_object* v_core_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim___redArg(v_t_230_, v_core_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_cancelDen_elim___redArg(lean_object* v_t_234_, lean_object* v_cancelDen_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim___redArg(v_t_234_, v_cancelDen_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_cancelDen_elim(lean_object* v_motive__2_237_, lean_object* v_t_238_, lean_object* v_h_239_, lean_object* v_cancelDen_240_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim___redArg(v_t_238_, v_cancelDen_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorIdx___impl(lean_object* v_x_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = lean_obj_tag_nat(v_x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorIdx___impl___boxed(lean_object* v_x_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorIdx___impl(v_x_244_);
lean_dec_ref(v_x_244_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(lean_object* v_t_246_, lean_object* v_k_247_){
_start:
{
switch(lean_obj_tag(v_t_246_))
{
case 0:
{
lean_object* v_a_248_; lean_object* v_b_249_; lean_object* v_lhs_250_; lean_object* v_rhs_251_; lean_object* v___x_252_; 
v_a_248_ = lean_ctor_get(v_t_246_, 0);
lean_inc_ref(v_a_248_);
v_b_249_ = lean_ctor_get(v_t_246_, 1);
lean_inc_ref(v_b_249_);
v_lhs_250_ = lean_ctor_get(v_t_246_, 2);
lean_inc(v_lhs_250_);
v_rhs_251_ = lean_ctor_get(v_t_246_, 3);
lean_inc(v_rhs_251_);
lean_dec_ref_known(v_t_246_, 4);
v___x_252_ = lean_apply_4(v_k_247_, v_a_248_, v_b_249_, v_lhs_250_, v_rhs_251_);
return v___x_252_;
}
case 1:
{
lean_object* v_a_253_; lean_object* v_b_254_; lean_object* v_ra_255_; lean_object* v_rb_256_; lean_object* v_p_257_; lean_object* v_lhs_x27_258_; lean_object* v___x_259_; 
v_a_253_ = lean_ctor_get(v_t_246_, 0);
lean_inc_ref(v_a_253_);
v_b_254_ = lean_ctor_get(v_t_246_, 1);
lean_inc_ref(v_b_254_);
v_ra_255_ = lean_ctor_get(v_t_246_, 2);
lean_inc_ref(v_ra_255_);
v_rb_256_ = lean_ctor_get(v_t_246_, 3);
lean_inc_ref(v_rb_256_);
v_p_257_ = lean_ctor_get(v_t_246_, 4);
lean_inc_ref(v_p_257_);
v_lhs_x27_258_ = lean_ctor_get(v_t_246_, 5);
lean_inc(v_lhs_x27_258_);
lean_dec_ref_known(v_t_246_, 6);
v___x_259_ = lean_apply_6(v_k_247_, v_a_253_, v_b_254_, v_ra_255_, v_rb_256_, v_p_257_, v_lhs_x27_258_);
return v___x_259_;
}
case 2:
{
lean_object* v_a_260_; lean_object* v_b_261_; lean_object* v_natStructId_262_; lean_object* v_lhs_263_; lean_object* v_rhs_264_; lean_object* v___x_265_; 
v_a_260_ = lean_ctor_get(v_t_246_, 0);
lean_inc_ref(v_a_260_);
v_b_261_ = lean_ctor_get(v_t_246_, 1);
lean_inc_ref(v_b_261_);
v_natStructId_262_ = lean_ctor_get(v_t_246_, 2);
lean_inc(v_natStructId_262_);
v_lhs_263_ = lean_ctor_get(v_t_246_, 3);
lean_inc(v_lhs_263_);
v_rhs_264_ = lean_ctor_get(v_t_246_, 4);
lean_inc(v_rhs_264_);
lean_dec_ref_known(v_t_246_, 5);
v___x_265_ = lean_apply_5(v_k_247_, v_a_260_, v_b_261_, v_natStructId_262_, v_lhs_263_, v_rhs_264_);
return v___x_265_;
}
case 3:
{
lean_object* v_c_266_; lean_object* v___x_267_; 
v_c_266_ = lean_ctor_get(v_t_246_, 0);
lean_inc_ref(v_c_266_);
lean_dec_ref_known(v_t_246_, 1);
v___x_267_ = lean_apply_1(v_k_247_, v_c_266_);
return v___x_267_;
}
case 4:
{
lean_object* v_k_268_; lean_object* v_c_269_; lean_object* v___x_270_; 
v_k_268_ = lean_ctor_get(v_t_246_, 0);
lean_inc(v_k_268_);
v_c_269_ = lean_ctor_get(v_t_246_, 1);
lean_inc_ref(v_c_269_);
lean_dec_ref_known(v_t_246_, 2);
v___x_270_ = lean_apply_2(v_k_247_, v_k_268_, v_c_269_);
return v___x_270_;
}
default: 
{
lean_object* v_x_271_; lean_object* v_c_u2081_272_; lean_object* v_c_u2082_273_; lean_object* v___x_274_; 
v_x_271_ = lean_ctor_get(v_t_246_, 0);
lean_inc(v_x_271_);
v_c_u2081_272_ = lean_ctor_get(v_t_246_, 1);
lean_inc_ref(v_c_u2081_272_);
v_c_u2082_273_ = lean_ctor_get(v_t_246_, 2);
lean_inc_ref(v_c_u2082_273_);
lean_dec_ref_known(v_t_246_, 3);
v___x_274_ = lean_apply_3(v_k_247_, v_x_271_, v_c_u2081_272_, v_c_u2082_273_);
return v___x_274_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim(lean_object* v_motive__2_275_, lean_object* v_ctorIdx_276_, lean_object* v_t_277_, lean_object* v_h_278_, lean_object* v_k_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_277_, v_k_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___boxed(lean_object* v_motive__2_281_, lean_object* v_ctorIdx_282_, lean_object* v_t_283_, lean_object* v_h_284_, lean_object* v_k_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim(v_motive__2_281_, v_ctorIdx_282_, v_t_283_, v_h_284_, v_k_285_);
lean_dec(v_ctorIdx_282_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_core_elim___redArg(lean_object* v_t_287_, lean_object* v_core_288_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_287_, v_core_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_core_elim(lean_object* v_motive__2_290_, lean_object* v_t_291_, lean_object* v_h_292_, lean_object* v_core_293_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_291_, v_core_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_coreCommRing_elim___redArg(lean_object* v_t_295_, lean_object* v_coreCommRing_296_){
_start:
{
lean_object* v___x_297_; 
v___x_297_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_295_, v_coreCommRing_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_coreCommRing_elim(lean_object* v_motive__2_298_, lean_object* v_t_299_, lean_object* v_h_300_, lean_object* v_coreCommRing_301_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_299_, v_coreCommRing_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_coreOfNat_elim___redArg(lean_object* v_t_303_, lean_object* v_coreOfNat_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_303_, v_coreOfNat_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_coreOfNat_elim(lean_object* v_motive__2_306_, lean_object* v_t_307_, lean_object* v_h_308_, lean_object* v_coreOfNat_309_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_307_, v_coreOfNat_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_neg_elim___redArg(lean_object* v_t_311_, lean_object* v_neg_312_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_311_, v_neg_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_neg_elim(lean_object* v_motive__2_314_, lean_object* v_t_315_, lean_object* v_h_316_, lean_object* v_neg_317_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_315_, v_neg_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_coeff_elim___redArg(lean_object* v_t_319_, lean_object* v_coeff_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_319_, v_coeff_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_coeff_elim(lean_object* v_motive__2_322_, lean_object* v_t_323_, lean_object* v_h_324_, lean_object* v_coeff_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_323_, v_coeff_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_subst_elim___redArg(lean_object* v_t_327_, lean_object* v_subst_328_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_327_, v_subst_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_subst_elim(lean_object* v_motive__2_330_, lean_object* v_t_331_, lean_object* v_h_332_, lean_object* v_subst_333_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_331_, v_subst_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorIdx___impl(lean_object* v_x_335_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = lean_obj_tag_nat(v_x_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorIdx___impl___boxed(lean_object* v_x_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorIdx___impl(v_x_337_);
lean_dec(v_x_337_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(lean_object* v_t_339_, lean_object* v_k_340_){
_start:
{
switch(lean_obj_tag(v_t_339_))
{
case 0:
{
lean_object* v_e_341_; lean_object* v_lhs_342_; lean_object* v_rhs_343_; lean_object* v___x_344_; 
v_e_341_ = lean_ctor_get(v_t_339_, 0);
lean_inc_ref(v_e_341_);
v_lhs_342_ = lean_ctor_get(v_t_339_, 1);
lean_inc(v_lhs_342_);
v_rhs_343_ = lean_ctor_get(v_t_339_, 2);
lean_inc(v_rhs_343_);
lean_dec_ref_known(v_t_339_, 3);
v___x_344_ = lean_apply_3(v_k_340_, v_e_341_, v_lhs_342_, v_rhs_343_);
return v___x_344_;
}
case 1:
{
lean_object* v_e_345_; lean_object* v_lhs_346_; lean_object* v_rhs_347_; lean_object* v___x_348_; 
v_e_345_ = lean_ctor_get(v_t_339_, 0);
lean_inc_ref(v_e_345_);
v_lhs_346_ = lean_ctor_get(v_t_339_, 1);
lean_inc(v_lhs_346_);
v_rhs_347_ = lean_ctor_get(v_t_339_, 2);
lean_inc(v_rhs_347_);
lean_dec_ref_known(v_t_339_, 3);
v___x_348_ = lean_apply_3(v_k_340_, v_e_345_, v_lhs_346_, v_rhs_347_);
return v___x_348_;
}
case 3:
{
lean_object* v_e_349_; lean_object* v_natStructId_350_; lean_object* v_lhs_351_; lean_object* v_rhs_352_; lean_object* v___x_353_; 
v_e_349_ = lean_ctor_get(v_t_339_, 0);
lean_inc_ref(v_e_349_);
v_natStructId_350_ = lean_ctor_get(v_t_339_, 1);
lean_inc(v_natStructId_350_);
v_lhs_351_ = lean_ctor_get(v_t_339_, 2);
lean_inc(v_lhs_351_);
v_rhs_352_ = lean_ctor_get(v_t_339_, 3);
lean_inc(v_rhs_352_);
lean_dec_ref_known(v_t_339_, 4);
v___x_353_ = lean_apply_4(v_k_340_, v_e_349_, v_natStructId_350_, v_lhs_351_, v_rhs_352_);
return v___x_353_;
}
case 4:
{
lean_object* v_e_354_; lean_object* v_natStructId_355_; lean_object* v_lhs_356_; lean_object* v_rhs_357_; lean_object* v___x_358_; 
v_e_354_ = lean_ctor_get(v_t_339_, 0);
lean_inc_ref(v_e_354_);
v_natStructId_355_ = lean_ctor_get(v_t_339_, 1);
lean_inc(v_natStructId_355_);
v_lhs_356_ = lean_ctor_get(v_t_339_, 2);
lean_inc(v_lhs_356_);
v_rhs_357_ = lean_ctor_get(v_t_339_, 3);
lean_inc(v_rhs_357_);
lean_dec_ref_known(v_t_339_, 4);
v___x_358_ = lean_apply_4(v_k_340_, v_e_354_, v_natStructId_355_, v_lhs_356_, v_rhs_357_);
return v___x_358_;
}
case 5:
{
lean_object* v_c_u2081_359_; lean_object* v_c_u2082_360_; lean_object* v___x_361_; 
v_c_u2081_359_ = lean_ctor_get(v_t_339_, 0);
lean_inc_ref(v_c_u2081_359_);
v_c_u2082_360_ = lean_ctor_get(v_t_339_, 1);
lean_inc_ref(v_c_u2082_360_);
lean_dec_ref_known(v_t_339_, 2);
v___x_361_ = lean_apply_2(v_k_340_, v_c_u2081_359_, v_c_u2082_360_);
return v___x_361_;
}
case 7:
{
lean_object* v_h_362_; lean_object* v___x_363_; 
v_h_362_ = lean_ctor_get(v_t_339_, 0);
lean_inc(v_h_362_);
lean_dec_ref_known(v_t_339_, 1);
v___x_363_ = lean_apply_1(v_k_340_, v_h_362_);
return v___x_363_;
}
case 8:
{
lean_object* v_c_u2081_364_; lean_object* v_decVar_365_; lean_object* v_h_366_; lean_object* v_decVars_367_; lean_object* v___x_368_; 
v_c_u2081_364_ = lean_ctor_get(v_t_339_, 0);
lean_inc_ref(v_c_u2081_364_);
v_decVar_365_ = lean_ctor_get(v_t_339_, 1);
lean_inc(v_decVar_365_);
v_h_366_ = lean_ctor_get(v_t_339_, 2);
lean_inc_ref(v_h_366_);
v_decVars_367_ = lean_ctor_get(v_t_339_, 3);
lean_inc_ref(v_decVars_367_);
lean_dec_ref_known(v_t_339_, 4);
v___x_368_ = lean_apply_4(v_k_340_, v_c_u2081_364_, v_decVar_365_, v_h_366_, v_decVars_367_);
return v___x_368_;
}
case 9:
{
return v_k_340_;
}
case 10:
{
lean_object* v_a_369_; lean_object* v_b_370_; lean_object* v_la_371_; lean_object* v_lb_372_; lean_object* v___x_373_; 
v_a_369_ = lean_ctor_get(v_t_339_, 0);
lean_inc_ref(v_a_369_);
v_b_370_ = lean_ctor_get(v_t_339_, 1);
lean_inc_ref(v_b_370_);
v_la_371_ = lean_ctor_get(v_t_339_, 2);
lean_inc(v_la_371_);
v_lb_372_ = lean_ctor_get(v_t_339_, 3);
lean_inc(v_lb_372_);
lean_dec_ref_known(v_t_339_, 4);
v___x_373_ = lean_apply_4(v_k_340_, v_a_369_, v_b_370_, v_la_371_, v_lb_372_);
return v___x_373_;
}
case 11:
{
lean_object* v_a_374_; lean_object* v_b_375_; lean_object* v_natStructId_376_; lean_object* v_la_377_; lean_object* v_lb_378_; lean_object* v___x_379_; 
v_a_374_ = lean_ctor_get(v_t_339_, 0);
lean_inc_ref(v_a_374_);
v_b_375_ = lean_ctor_get(v_t_339_, 1);
lean_inc_ref(v_b_375_);
v_natStructId_376_ = lean_ctor_get(v_t_339_, 2);
lean_inc(v_natStructId_376_);
v_la_377_ = lean_ctor_get(v_t_339_, 3);
lean_inc(v_la_377_);
v_lb_378_ = lean_ctor_get(v_t_339_, 4);
lean_inc(v_lb_378_);
lean_dec_ref_known(v_t_339_, 5);
v___x_379_ = lean_apply_5(v_k_340_, v_a_374_, v_b_375_, v_natStructId_376_, v_la_377_, v_lb_378_);
return v___x_379_;
}
case 13:
{
lean_object* v_x_380_; lean_object* v_c_u2081_381_; lean_object* v_c_u2082_382_; lean_object* v___x_383_; 
v_x_380_ = lean_ctor_get(v_t_339_, 0);
lean_inc(v_x_380_);
v_c_u2081_381_ = lean_ctor_get(v_t_339_, 1);
lean_inc_ref(v_c_u2081_381_);
v_c_u2082_382_ = lean_ctor_get(v_t_339_, 2);
lean_inc_ref(v_c_u2082_382_);
lean_dec_ref_known(v_t_339_, 3);
v___x_383_ = lean_apply_3(v_k_340_, v_x_380_, v_c_u2081_381_, v_c_u2082_382_);
return v___x_383_;
}
default: 
{
lean_object* v_c_384_; lean_object* v_lhs_385_; lean_object* v___x_386_; 
v_c_384_ = lean_ctor_get(v_t_339_, 0);
lean_inc_ref(v_c_384_);
v_lhs_385_ = lean_ctor_get(v_t_339_, 1);
lean_inc(v_lhs_385_);
lean_dec(v_t_339_);
v___x_386_ = lean_apply_2(v_k_340_, v_c_384_, v_lhs_385_);
return v___x_386_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim(lean_object* v_motive__4_387_, lean_object* v_ctorIdx_388_, lean_object* v_t_389_, lean_object* v_h_390_, lean_object* v_k_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_389_, v_k_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___boxed(lean_object* v_motive__4_393_, lean_object* v_ctorIdx_394_, lean_object* v_t_395_, lean_object* v_h_396_, lean_object* v_k_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim(v_motive__4_393_, v_ctorIdx_394_, v_t_395_, v_h_396_, v_k_397_);
lean_dec(v_ctorIdx_394_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_core_elim___redArg(lean_object* v_t_399_, lean_object* v_core_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_399_, v_core_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_core_elim(lean_object* v_motive__4_402_, lean_object* v_t_403_, lean_object* v_h_404_, lean_object* v_core_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_403_, v_core_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_notCore_elim___redArg(lean_object* v_t_407_, lean_object* v_notCore_408_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_407_, v_notCore_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_notCore_elim(lean_object* v_motive__4_410_, lean_object* v_t_411_, lean_object* v_h_412_, lean_object* v_notCore_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_411_, v_notCore_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ring_elim___redArg(lean_object* v_t_415_, lean_object* v_ring_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_415_, v_ring_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ring_elim(lean_object* v_motive__4_418_, lean_object* v_t_419_, lean_object* v_h_420_, lean_object* v_ring_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_419_, v_ring_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_coreOfNat_elim___redArg(lean_object* v_t_423_, lean_object* v_coreOfNat_424_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_423_, v_coreOfNat_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_coreOfNat_elim(lean_object* v_motive__4_426_, lean_object* v_t_427_, lean_object* v_h_428_, lean_object* v_coreOfNat_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_427_, v_coreOfNat_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_notCoreOfNat_elim___redArg(lean_object* v_t_431_, lean_object* v_notCoreOfNat_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_431_, v_notCoreOfNat_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_notCoreOfNat_elim(lean_object* v_motive__4_434_, lean_object* v_t_435_, lean_object* v_h_436_, lean_object* v_notCoreOfNat_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_435_, v_notCoreOfNat_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_combine_elim___redArg(lean_object* v_t_439_, lean_object* v_combine_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_439_, v_combine_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_combine_elim(lean_object* v_motive__4_442_, lean_object* v_t_443_, lean_object* v_h_444_, lean_object* v_combine_445_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_443_, v_combine_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_norm_elim___redArg(lean_object* v_t_447_, lean_object* v_norm_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_447_, v_norm_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_norm_elim(lean_object* v_motive__4_450_, lean_object* v_t_451_, lean_object* v_h_452_, lean_object* v_norm_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_451_, v_norm_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_dec_elim___redArg(lean_object* v_t_455_, lean_object* v_dec_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_455_, v_dec_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_dec_elim(lean_object* v_motive__4_458_, lean_object* v_t_459_, lean_object* v_h_460_, lean_object* v_dec_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_459_, v_dec_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ofDiseqSplit_elim___redArg(lean_object* v_t_463_, lean_object* v_ofDiseqSplit_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_463_, v_ofDiseqSplit_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ofDiseqSplit_elim(lean_object* v_motive__4_466_, lean_object* v_t_467_, lean_object* v_h_468_, lean_object* v_ofDiseqSplit_469_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_467_, v_ofDiseqSplit_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_oneGtZero_elim___redArg(lean_object* v_t_471_, lean_object* v_oneGtZero_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_471_, v_oneGtZero_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_oneGtZero_elim(lean_object* v_motive__4_474_, lean_object* v_t_475_, lean_object* v_h_476_, lean_object* v_oneGtZero_477_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_475_, v_oneGtZero_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ofEq_elim___redArg(lean_object* v_t_479_, lean_object* v_ofEq_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_479_, v_ofEq_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ofEq_elim(lean_object* v_motive__4_482_, lean_object* v_t_483_, lean_object* v_h_484_, lean_object* v_ofEq_485_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_483_, v_ofEq_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ofEqOfNat_elim___redArg(lean_object* v_t_487_, lean_object* v_ofEqOfNat_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_487_, v_ofEqOfNat_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ofEqOfNat_elim(lean_object* v_motive__4_490_, lean_object* v_t_491_, lean_object* v_h_492_, lean_object* v_ofEqOfNat_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_491_, v_ofEqOfNat_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ringEq_elim___redArg(lean_object* v_t_495_, lean_object* v_ringEq_496_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_495_, v_ringEq_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ringEq_elim(lean_object* v_motive__4_498_, lean_object* v_t_499_, lean_object* v_h_500_, lean_object* v_ringEq_501_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_499_, v_ringEq_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_subst_elim___redArg(lean_object* v_t_503_, lean_object* v_subst_504_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_503_, v_subst_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_subst_elim(lean_object* v_motive__4_506_, lean_object* v_t_507_, lean_object* v_h_508_, lean_object* v_subst_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_507_, v_subst_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorIdx___impl(lean_object* v_x_511_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = lean_obj_tag_nat(v_x_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorIdx___impl___boxed(lean_object* v_x_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorIdx___impl(v_x_513_);
lean_dec(v_x_513_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(lean_object* v_t_515_, lean_object* v_k_516_){
_start:
{
switch(lean_obj_tag(v_t_515_))
{
case 0:
{
lean_object* v_a_517_; lean_object* v_b_518_; lean_object* v_lhs_519_; lean_object* v_rhs_520_; lean_object* v___x_521_; 
v_a_517_ = lean_ctor_get(v_t_515_, 0);
lean_inc_ref(v_a_517_);
v_b_518_ = lean_ctor_get(v_t_515_, 1);
lean_inc_ref(v_b_518_);
v_lhs_519_ = lean_ctor_get(v_t_515_, 2);
lean_inc(v_lhs_519_);
v_rhs_520_ = lean_ctor_get(v_t_515_, 3);
lean_inc(v_rhs_520_);
lean_dec_ref_known(v_t_515_, 4);
v___x_521_ = lean_apply_4(v_k_516_, v_a_517_, v_b_518_, v_lhs_519_, v_rhs_520_);
return v___x_521_;
}
case 1:
{
lean_object* v_c_522_; lean_object* v_lhs_523_; lean_object* v___x_524_; 
v_c_522_ = lean_ctor_get(v_t_515_, 0);
lean_inc_ref(v_c_522_);
v_lhs_523_ = lean_ctor_get(v_t_515_, 1);
lean_inc(v_lhs_523_);
lean_dec_ref_known(v_t_515_, 2);
v___x_524_ = lean_apply_2(v_k_516_, v_c_522_, v_lhs_523_);
return v___x_524_;
}
case 2:
{
lean_object* v_a_525_; lean_object* v_b_526_; lean_object* v_natStructId_527_; lean_object* v_lhs_528_; lean_object* v_rhs_529_; lean_object* v___x_530_; 
v_a_525_ = lean_ctor_get(v_t_515_, 0);
lean_inc_ref(v_a_525_);
v_b_526_ = lean_ctor_get(v_t_515_, 1);
lean_inc_ref(v_b_526_);
v_natStructId_527_ = lean_ctor_get(v_t_515_, 2);
lean_inc(v_natStructId_527_);
v_lhs_528_ = lean_ctor_get(v_t_515_, 3);
lean_inc(v_lhs_528_);
v_rhs_529_ = lean_ctor_get(v_t_515_, 4);
lean_inc(v_rhs_529_);
lean_dec_ref_known(v_t_515_, 5);
v___x_530_ = lean_apply_5(v_k_516_, v_a_525_, v_b_526_, v_natStructId_527_, v_lhs_528_, v_rhs_529_);
return v___x_530_;
}
case 3:
{
lean_object* v_c_531_; lean_object* v___x_532_; 
v_c_531_ = lean_ctor_get(v_t_515_, 0);
lean_inc_ref(v_c_531_);
lean_dec_ref_known(v_t_515_, 1);
v___x_532_ = lean_apply_1(v_k_516_, v_c_531_);
return v___x_532_;
}
case 4:
{
lean_object* v_k_u2081_533_; lean_object* v_k_u2082_534_; lean_object* v_c_u2081_535_; lean_object* v_c_u2082_536_; lean_object* v___x_537_; 
v_k_u2081_533_ = lean_ctor_get(v_t_515_, 0);
lean_inc(v_k_u2081_533_);
v_k_u2082_534_ = lean_ctor_get(v_t_515_, 1);
lean_inc(v_k_u2082_534_);
v_c_u2081_535_ = lean_ctor_get(v_t_515_, 2);
lean_inc_ref(v_c_u2081_535_);
v_c_u2082_536_ = lean_ctor_get(v_t_515_, 3);
lean_inc_ref(v_c_u2082_536_);
lean_dec_ref_known(v_t_515_, 4);
v___x_537_ = lean_apply_4(v_k_516_, v_k_u2081_533_, v_k_u2082_534_, v_c_u2081_535_, v_c_u2082_536_);
return v___x_537_;
}
case 5:
{
lean_object* v_k_538_; lean_object* v_c_u2081_539_; lean_object* v_c_u2082_540_; lean_object* v___x_541_; 
v_k_538_ = lean_ctor_get(v_t_515_, 0);
lean_inc(v_k_538_);
v_c_u2081_539_ = lean_ctor_get(v_t_515_, 1);
lean_inc_ref(v_c_u2081_539_);
v_c_u2082_540_ = lean_ctor_get(v_t_515_, 2);
lean_inc_ref(v_c_u2082_540_);
lean_dec_ref_known(v_t_515_, 3);
v___x_541_ = lean_apply_3(v_k_516_, v_k_538_, v_c_u2081_539_, v_c_u2082_540_);
return v___x_541_;
}
default: 
{
return v_k_516_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim(lean_object* v_motive__6_542_, lean_object* v_ctorIdx_543_, lean_object* v_t_544_, lean_object* v_h_545_, lean_object* v_k_546_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_544_, v_k_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___boxed(lean_object* v_motive__6_548_, lean_object* v_ctorIdx_549_, lean_object* v_t_550_, lean_object* v_h_551_, lean_object* v_k_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim(v_motive__6_548_, v_ctorIdx_549_, v_t_550_, v_h_551_, v_k_552_);
lean_dec(v_ctorIdx_549_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_core_elim___redArg(lean_object* v_t_554_, lean_object* v_core_555_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_554_, v_core_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_core_elim(lean_object* v_motive__6_557_, lean_object* v_t_558_, lean_object* v_h_559_, lean_object* v_core_560_){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_558_, v_core_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ring_elim___redArg(lean_object* v_t_562_, lean_object* v_ring_563_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_562_, v_ring_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ring_elim(lean_object* v_motive__6_565_, lean_object* v_t_566_, lean_object* v_h_567_, lean_object* v_ring_568_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_566_, v_ring_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_coreOfNat_elim___redArg(lean_object* v_t_570_, lean_object* v_coreOfNat_571_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_570_, v_coreOfNat_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_coreOfNat_elim(lean_object* v_motive__6_573_, lean_object* v_t_574_, lean_object* v_h_575_, lean_object* v_coreOfNat_576_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_574_, v_coreOfNat_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_neg_elim___redArg(lean_object* v_t_578_, lean_object* v_neg_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_578_, v_neg_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_neg_elim(lean_object* v_motive__6_581_, lean_object* v_t_582_, lean_object* v_h_583_, lean_object* v_neg_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_582_, v_neg_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_subst_elim___redArg(lean_object* v_t_586_, lean_object* v_subst_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_586_, v_subst_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_subst_elim(lean_object* v_motive__6_589_, lean_object* v_t_590_, lean_object* v_h_591_, lean_object* v_subst_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_590_, v_subst_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_subst1_elim___redArg(lean_object* v_t_594_, lean_object* v_subst1_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_594_, v_subst1_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_subst1_elim(lean_object* v_motive__6_597_, lean_object* v_t_598_, lean_object* v_h_599_, lean_object* v_subst1_600_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_598_, v_subst1_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_oneNeZero_elim___redArg(lean_object* v_t_602_, lean_object* v_oneNeZero_603_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_602_, v_oneNeZero_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_oneNeZero_elim(lean_object* v_motive__6_605_, lean_object* v_t_606_, lean_object* v_h_607_, lean_object* v_oneNeZero_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_606_, v_oneNeZero_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorIdx___impl(lean_object* v_x_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = lean_obj_tag_nat(v_x_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorIdx___impl___boxed(lean_object* v_x_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorIdx___impl(v_x_612_);
lean_dec_ref(v_x_612_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorElim___redArg(lean_object* v_t_614_, lean_object* v_k_615_){
_start:
{
lean_object* v_c_616_; lean_object* v___x_617_; 
v_c_616_ = lean_ctor_get(v_t_614_, 0);
lean_inc_ref(v_c_616_);
lean_dec_ref(v_t_614_);
v___x_617_ = lean_apply_1(v_k_615_, v_c_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorElim(lean_object* v_motive__7_618_, lean_object* v_ctorIdx_619_, lean_object* v_t_620_, lean_object* v_h_621_, lean_object* v_k_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorElim___redArg(v_t_620_, v_k_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorElim___boxed(lean_object* v_motive__7_624_, lean_object* v_ctorIdx_625_, lean_object* v_t_626_, lean_object* v_h_627_, lean_object* v_k_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorElim(v_motive__7_624_, v_ctorIdx_625_, v_t_626_, v_h_627_, v_k_628_);
lean_dec(v_ctorIdx_625_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_diseq_elim___redArg(lean_object* v_t_630_, lean_object* v_diseq_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorElim___redArg(v_t_630_, v_diseq_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_diseq_elim(lean_object* v_motive__7_633_, lean_object* v_t_634_, lean_object* v_h_635_, lean_object* v_diseq_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorElim___redArg(v_t_634_, v_diseq_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_lt_elim___redArg(lean_object* v_t_638_, lean_object* v_lt_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorElim___redArg(v_t_638_, v_lt_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_lt_elim(lean_object* v_motive__7_641_, lean_object* v_t_642_, lean_object* v_h_643_, lean_object* v_lt_644_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorElim___redArg(v_t_642_, v_lt_644_);
return v___x_645_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_649_ = lean_box(0);
v___x_650_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__1));
v___x_651_ = l_Lean_Expr_const___override(v___x_650_, v___x_649_);
return v___x_651_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__3(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_652_ = lean_box(0);
v___x_653_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2);
v___x_654_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
lean_ctor_set(v___x_654_, 1, v___x_653_);
lean_ctor_set(v___x_654_, 2, v___x_652_);
lean_ctor_set(v___x_654_, 3, v___x_652_);
return v___x_654_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__4(void){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_655_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__3, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__3);
v___x_656_ = lean_box(0);
v___x_657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
lean_ctor_set(v___x_657_, 1, v___x_655_);
return v___x_657_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr(void){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__4, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__4);
return v___x_658_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__0(void){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_659_ = lean_box(0);
v___x_660_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2);
v___x_661_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
lean_ctor_set(v___x_661_, 2, v___x_659_);
lean_ctor_set(v___x_661_, 3, v___x_659_);
return v___x_661_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__1(void){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_662_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__0, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__0);
v___x_663_ = lean_box(0);
v___x_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
lean_ctor_set(v___x_664_, 1, v___x_662_);
return v___x_664_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr(void){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__1, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__1);
return v___x_665_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__0(void){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_666_ = lean_unsigned_to_nat(32u);
v___x_667_ = lean_mk_empty_array_with_capacity(v___x_666_);
v___x_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
return v___x_668_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__1(void){
_start:
{
size_t v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_669_ = ((size_t)5ULL);
v___x_670_ = lean_unsigned_to_nat(0u);
v___x_671_ = lean_unsigned_to_nat(32u);
v___x_672_ = lean_mk_empty_array_with_capacity(v___x_671_);
v___x_673_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__0, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__0);
v___x_674_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_674_, 0, v___x_673_);
lean_ctor_set(v___x_674_, 1, v___x_672_);
lean_ctor_set(v___x_674_, 2, v___x_670_);
lean_ctor_set(v___x_674_, 3, v___x_670_);
lean_ctor_set_usize(v___x_674_, 4, v___x_669_);
return v___x_674_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__2(void){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_675_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__3(void){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__2, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__2);
v___x_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
return v___x_677_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__4(void){
_start:
{
lean_object* v___x_678_; uint8_t v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_678_ = lean_box(0);
v___x_679_ = 0;
v___x_680_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__3, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__3);
v___x_681_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__1, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__1);
v___x_682_ = lean_box(0);
v___x_683_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2);
v___x_684_ = lean_box(0);
v___x_685_ = lean_unsigned_to_nat(0u);
v___x_686_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v___x_686_, 0, v___x_685_);
lean_ctor_set(v___x_686_, 1, v___x_684_);
lean_ctor_set(v___x_686_, 2, v___x_683_);
lean_ctor_set(v___x_686_, 3, v___x_682_);
lean_ctor_set(v___x_686_, 4, v___x_683_);
lean_ctor_set(v___x_686_, 5, v___x_684_);
lean_ctor_set(v___x_686_, 6, v___x_684_);
lean_ctor_set(v___x_686_, 7, v___x_684_);
lean_ctor_set(v___x_686_, 8, v___x_684_);
lean_ctor_set(v___x_686_, 9, v___x_684_);
lean_ctor_set(v___x_686_, 10, v___x_684_);
lean_ctor_set(v___x_686_, 11, v___x_684_);
lean_ctor_set(v___x_686_, 12, v___x_684_);
lean_ctor_set(v___x_686_, 13, v___x_684_);
lean_ctor_set(v___x_686_, 14, v___x_684_);
lean_ctor_set(v___x_686_, 15, v___x_684_);
lean_ctor_set(v___x_686_, 16, v___x_684_);
lean_ctor_set(v___x_686_, 17, v___x_683_);
lean_ctor_set(v___x_686_, 18, v___x_683_);
lean_ctor_set(v___x_686_, 19, v___x_684_);
lean_ctor_set(v___x_686_, 20, v___x_684_);
lean_ctor_set(v___x_686_, 21, v___x_684_);
lean_ctor_set(v___x_686_, 22, v___x_683_);
lean_ctor_set(v___x_686_, 23, v___x_683_);
lean_ctor_set(v___x_686_, 24, v___x_683_);
lean_ctor_set(v___x_686_, 25, v___x_684_);
lean_ctor_set(v___x_686_, 26, v___x_684_);
lean_ctor_set(v___x_686_, 27, v___x_684_);
lean_ctor_set(v___x_686_, 28, v___x_683_);
lean_ctor_set(v___x_686_, 29, v___x_683_);
lean_ctor_set(v___x_686_, 30, v___x_681_);
lean_ctor_set(v___x_686_, 31, v___x_680_);
lean_ctor_set(v___x_686_, 32, v___x_681_);
lean_ctor_set(v___x_686_, 33, v___x_681_);
lean_ctor_set(v___x_686_, 34, v___x_681_);
lean_ctor_set(v___x_686_, 35, v___x_681_);
lean_ctor_set(v___x_686_, 36, v___x_684_);
lean_ctor_set(v___x_686_, 37, v___x_680_);
lean_ctor_set(v___x_686_, 38, v___x_681_);
lean_ctor_set(v___x_686_, 39, v___x_678_);
lean_ctor_set(v___x_686_, 40, v___x_681_);
lean_ctor_set(v___x_686_, 41, v___x_681_);
lean_ctor_set_uint8(v___x_686_, sizeof(void*)*42, v___x_679_);
return v___x_686_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default(void){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__4, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__4);
return v___x_687_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct(void){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default;
return v___x_688_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__2, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__2);
v___x_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
return v___x_690_;
}
}
lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___redArg(){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___redArg___closed__0);
return v___x_692_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_693_;
v_res_693_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___redArg();
stack->m_obj
 = v_res_693_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___redArg___boxed(lean_object* v___dummy_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___redArg();
return v_res_695_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___redArg();
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0(lean_object* v_00_u03b2_697_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__0);
return v___x_698_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__1(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__2, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__2);
v___x_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_702_, 0, v___x_701_);
return v___x_702_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__2(void){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_703_ = lean_unsigned_to_nat(32u);
v___x_704_ = lean_mk_empty_array_with_capacity(v___x_703_);
v___x_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
return v___x_705_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__3(void){
_start:
{
size_t v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_706_ = ((size_t)5ULL);
v___x_707_ = lean_unsigned_to_nat(0u);
v___x_708_ = lean_unsigned_to_nat(32u);
v___x_709_ = lean_mk_empty_array_with_capacity(v___x_708_);
v___x_710_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__2, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__2);
v___x_711_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_711_, 0, v___x_710_);
lean_ctor_set(v___x_711_, 1, v___x_709_);
lean_ctor_set(v___x_711_, 2, v___x_707_);
lean_ctor_set(v___x_711_, 3, v___x_707_);
lean_ctor_set_usize(v___x_711_, 4, v___x_706_);
return v___x_711_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__4(void){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_712_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__0);
v___x_713_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__3, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__3);
v___x_714_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__1, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__1);
v___x_715_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__0));
v___x_716_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_716_, 0, v___x_715_);
lean_ctor_set(v___x_716_, 1, v___x_714_);
lean_ctor_set(v___x_716_, 2, v___x_714_);
lean_ctor_set(v___x_716_, 3, v___x_713_);
lean_ctor_set(v___x_716_, 4, v___x_712_);
lean_ctor_set(v___x_716_, 5, v___x_715_);
lean_ctor_set(v___x_716_, 6, v___x_714_);
lean_ctor_set(v___x_716_, 7, v___x_714_);
return v___x_716_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default(void){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__4, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__4);
return v___x_717_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState(void){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default;
return v___x_718_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2_(lean_object* v___x_719_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_721_, 0, v___x_719_);
return v___x_721_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_719_ = stack[0].m_obj;
lean_object* v_res_722_;
v_res_722_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2_(v___x_719_);
stack->m_obj
 = v_res_722_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2____boxed(lean_object* v___x_723_, lean_object* v___y_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2_(v___x_723_);
return v_res_725_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_726_; lean_object* v___f_727_; 
v___x_726_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__4, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__4);
v___f_727_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_727_, 0, v___x_726_);
return v___f_727_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_729_; lean_object* v___x_730_; 
v___f_729_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2_);
v___x_730_ = l_Lean_Meta_Grind_registerSolverExtension___redArg(v___f_729_);
return v___x_730_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_731_;
v_res_731_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2_();
stack->m_obj
 = v_res_731_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2____boxed(lean_object* v_a_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2_();
return v_res_733_;
}
}
lean_object* runtime_initialize_Init_Grind_Ring_CommSolver(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ordered_Linarith(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Grind_Ring_CommSolver(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ordered_Linarith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr = _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr);
l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr = _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr);
l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default = _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default);
l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct = _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct);
l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default = _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default);
l_Lean_Meta_Grind_Arith_Linear_instInhabitedState = _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instInhabitedState);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_Arith_Linear_linearExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_linearExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Ring_CommSolver(uint8_t builtin);
lean_object* initialize_Init_Grind_Ordered_Linarith(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Ring_CommSolver(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ordered_Linarith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(builtin);
}
#ifdef __cplusplus
}
#endif
