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
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash(lean_object* v_x_3_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash___boxed(lean_object* v_x_29_){
_start:
{
uint64_t v_res_30_; lean_object* v_r_31_; 
v_res_30_ = l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash(v_x_29_);
lean_dec(v_x_29_);
v_r_31_ = lean_box_uint64(v_res_30_);
return v_r_31_;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean_hash(lean_object* v_x_34_){
_start:
{
switch(lean_obj_tag(v_x_34_))
{
case 0:
{
uint64_t v___x_35_; 
v___x_35_ = 0ULL;
return v___x_35_;
}
case 1:
{
lean_object* v_i_36_; uint64_t v___x_37_; uint64_t v___x_38_; uint64_t v___x_39_; 
v_i_36_ = lean_ctor_get(v_x_34_, 0);
v___x_37_ = 1ULL;
v___x_38_ = lean_uint64_of_nat(v_i_36_);
v___x_39_ = lean_uint64_mix_hash(v___x_37_, v___x_38_);
return v___x_39_;
}
case 2:
{
lean_object* v_a_40_; lean_object* v_b_41_; uint64_t v___x_42_; uint64_t v___x_43_; uint64_t v___x_44_; uint64_t v___x_45_; uint64_t v___x_46_; 
v_a_40_ = lean_ctor_get(v_x_34_, 0);
v_b_41_ = lean_ctor_get(v_x_34_, 1);
v___x_42_ = 2ULL;
v___x_43_ = l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean_hash(v_a_40_);
v___x_44_ = lean_uint64_mix_hash(v___x_42_, v___x_43_);
v___x_45_ = l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean_hash(v_b_41_);
v___x_46_ = lean_uint64_mix_hash(v___x_44_, v___x_45_);
return v___x_46_;
}
case 3:
{
lean_object* v_a_47_; lean_object* v_b_48_; uint64_t v___x_49_; uint64_t v___x_50_; uint64_t v___x_51_; uint64_t v___x_52_; uint64_t v___x_53_; 
v_a_47_ = lean_ctor_get(v_x_34_, 0);
v_b_48_ = lean_ctor_get(v_x_34_, 1);
v___x_49_ = 3ULL;
v___x_50_ = l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean_hash(v_a_47_);
v___x_51_ = lean_uint64_mix_hash(v___x_49_, v___x_50_);
v___x_52_ = l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean_hash(v_b_48_);
v___x_53_ = lean_uint64_mix_hash(v___x_51_, v___x_52_);
return v___x_53_;
}
case 4:
{
lean_object* v_a_54_; uint64_t v___x_55_; uint64_t v___x_56_; uint64_t v___x_57_; 
v_a_54_ = lean_ctor_get(v_x_34_, 0);
v___x_55_ = 4ULL;
v___x_56_ = l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean_hash(v_a_54_);
v___x_57_ = lean_uint64_mix_hash(v___x_55_, v___x_56_);
return v___x_57_;
}
case 5:
{
lean_object* v_k_58_; lean_object* v_a_59_; uint64_t v___x_60_; uint64_t v___x_61_; uint64_t v___x_62_; uint64_t v___x_63_; uint64_t v___x_64_; 
v_k_58_ = lean_ctor_get(v_x_34_, 0);
v_a_59_ = lean_ctor_get(v_x_34_, 1);
v___x_60_ = 5ULL;
v___x_61_ = lean_uint64_of_nat(v_k_58_);
v___x_62_ = lean_uint64_mix_hash(v___x_60_, v___x_61_);
v___x_63_ = l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean_hash(v_a_59_);
v___x_64_ = lean_uint64_mix_hash(v___x_62_, v___x_63_);
return v___x_64_;
}
default: 
{
lean_object* v_k_65_; lean_object* v_a_66_; uint64_t v___x_67_; uint64_t v___y_69_; lean_object* v_intZero_73_; uint8_t v_isNeg_74_; 
v_k_65_ = lean_ctor_get(v_x_34_, 0);
v_a_66_ = lean_ctor_get(v_x_34_, 1);
v___x_67_ = 6ULL;
v_intZero_73_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash___closed__0, &l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_instHashablePoly__lean_hash___closed__0);
v_isNeg_74_ = lean_int_dec_lt(v_k_65_, v_intZero_73_);
if (v_isNeg_74_ == 0)
{
lean_object* v_a_75_; lean_object* v___x_76_; lean_object* v___x_77_; uint64_t v___x_78_; 
v_a_75_ = lean_nat_abs(v_k_65_);
v___x_76_ = lean_unsigned_to_nat(2u);
v___x_77_ = lean_nat_mul(v___x_76_, v_a_75_);
lean_dec(v_a_75_);
v___x_78_ = lean_uint64_of_nat(v___x_77_);
lean_dec(v___x_77_);
v___y_69_ = v___x_78_;
goto v___jp_68_;
}
else
{
lean_object* v_abs_79_; lean_object* v_one_80_; lean_object* v_a_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; uint64_t v___x_85_; 
v_abs_79_ = lean_nat_abs(v_k_65_);
v_one_80_ = lean_unsigned_to_nat(1u);
v_a_81_ = lean_nat_sub(v_abs_79_, v_one_80_);
lean_dec(v_abs_79_);
v___x_82_ = lean_unsigned_to_nat(2u);
v___x_83_ = lean_nat_mul(v___x_82_, v_a_81_);
lean_dec(v_a_81_);
v___x_84_ = lean_nat_add(v___x_83_, v_one_80_);
lean_dec(v___x_83_);
v___x_85_ = lean_uint64_of_nat(v___x_84_);
lean_dec(v___x_84_);
v___y_69_ = v___x_85_;
goto v___jp_68_;
}
v___jp_68_:
{
uint64_t v___x_70_; uint64_t v___x_71_; uint64_t v___x_72_; 
v___x_70_ = lean_uint64_mix_hash(v___x_67_, v___y_69_);
v___x_71_ = l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean_hash(v_a_66_);
v___x_72_ = lean_uint64_mix_hash(v___x_70_, v___x_71_);
return v___x_72_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean_hash___boxed(lean_object* v_x_86_){
_start:
{
uint64_t v_res_87_; lean_object* v_r_88_; 
v_res_87_ = l_Lean_Meta_Grind_Arith_Linear_instHashableExpr__lean_hash(v_x_86_);
lean_dec(v_x_86_);
v_r_88_ = lean_box_uint64(v_res_87_);
return v_r_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorIdx___impl(lean_object* v_x_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = lean_obj_tag_nat(v_x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorIdx___impl___boxed(lean_object* v_x_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorIdx___impl(v_x_93_);
lean_dec_ref(v_x_93_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorElim___redArg(lean_object* v_t_95_, lean_object* v_k_96_){
_start:
{
if (lean_obj_tag(v_t_95_) == 2)
{
lean_object* v_c_97_; lean_object* v_val_98_; lean_object* v_x_99_; lean_object* v_n_100_; lean_object* v___x_101_; 
v_c_97_ = lean_ctor_get(v_t_95_, 0);
lean_inc_ref(v_c_97_);
v_val_98_ = lean_ctor_get(v_t_95_, 1);
lean_inc(v_val_98_);
v_x_99_ = lean_ctor_get(v_t_95_, 2);
lean_inc(v_x_99_);
v_n_100_ = lean_ctor_get(v_t_95_, 3);
lean_inc(v_n_100_);
lean_dec_ref_known(v_t_95_, 4);
v___x_101_ = lean_apply_4(v_k_96_, v_c_97_, v_val_98_, v_x_99_, v_n_100_);
return v___x_101_;
}
else
{
lean_object* v_e_102_; lean_object* v_lhs_103_; lean_object* v_rhs_104_; lean_object* v___x_105_; 
v_e_102_ = lean_ctor_get(v_t_95_, 0);
lean_inc_ref(v_e_102_);
v_lhs_103_ = lean_ctor_get(v_t_95_, 1);
lean_inc_ref(v_lhs_103_);
v_rhs_104_ = lean_ctor_get(v_t_95_, 2);
lean_inc_ref(v_rhs_104_);
lean_dec_ref(v_t_95_);
v___x_105_ = lean_apply_3(v_k_96_, v_e_102_, v_lhs_103_, v_rhs_104_);
return v___x_105_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorElim(lean_object* v_motive__2_106_, lean_object* v_ctorIdx_107_, lean_object* v_t_108_, lean_object* v_h_109_, lean_object* v_k_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorElim___redArg(v_t_108_, v_k_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorElim___boxed(lean_object* v_motive__2_112_, lean_object* v_ctorIdx_113_, lean_object* v_t_114_, lean_object* v_h_115_, lean_object* v_k_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorElim(v_motive__2_112_, v_ctorIdx_113_, v_t_114_, v_h_115_, v_k_116_);
lean_dec(v_ctorIdx_113_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_core_elim___redArg(lean_object* v_t_118_, lean_object* v_core_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorElim___redArg(v_t_118_, v_core_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_core_elim(lean_object* v_motive__2_121_, lean_object* v_t_122_, lean_object* v_h_123_, lean_object* v_core_124_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorElim___redArg(v_t_122_, v_core_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_notCore_elim___redArg(lean_object* v_t_126_, lean_object* v_notCore_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorElim___redArg(v_t_126_, v_notCore_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_notCore_elim(lean_object* v_motive__2_129_, lean_object* v_t_130_, lean_object* v_h_131_, lean_object* v_notCore_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorElim___redArg(v_t_130_, v_notCore_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_cancelDen_elim___redArg(lean_object* v_t_134_, lean_object* v_cancelDen_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorElim___redArg(v_t_134_, v_cancelDen_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_cancelDen_elim(lean_object* v_motive__2_137_, lean_object* v_t_138_, lean_object* v_h_139_, lean_object* v_cancelDen_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorElim___redArg(v_t_138_, v_cancelDen_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorIdx___impl(lean_object* v_x_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = lean_obj_tag_nat(v_x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorIdx___impl___boxed(lean_object* v_x_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorIdx___impl(v_x_144_);
lean_dec_ref(v_x_144_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___redArg(lean_object* v_t_146_, lean_object* v_k_147_){
_start:
{
switch(lean_obj_tag(v_t_146_))
{
case 0:
{
lean_object* v_a_148_; lean_object* v_b_149_; lean_object* v_ra_150_; lean_object* v_rb_151_; lean_object* v___x_152_; 
v_a_148_ = lean_ctor_get(v_t_146_, 0);
lean_inc_ref(v_a_148_);
v_b_149_ = lean_ctor_get(v_t_146_, 1);
lean_inc_ref(v_b_149_);
v_ra_150_ = lean_ctor_get(v_t_146_, 2);
lean_inc_ref(v_ra_150_);
v_rb_151_ = lean_ctor_get(v_t_146_, 3);
lean_inc_ref(v_rb_151_);
lean_dec_ref_known(v_t_146_, 4);
v___x_152_ = lean_apply_4(v_k_147_, v_a_148_, v_b_149_, v_ra_150_, v_rb_151_);
return v___x_152_;
}
case 1:
{
lean_object* v_c_153_; lean_object* v___x_154_; 
v_c_153_ = lean_ctor_get(v_t_146_, 0);
lean_inc_ref(v_c_153_);
lean_dec_ref_known(v_t_146_, 1);
v___x_154_ = lean_apply_1(v_k_147_, v_c_153_);
return v___x_154_;
}
default: 
{
lean_object* v_c_155_; lean_object* v_val_156_; lean_object* v_x_157_; lean_object* v_n_158_; lean_object* v___x_159_; 
v_c_155_ = lean_ctor_get(v_t_146_, 0);
lean_inc_ref(v_c_155_);
v_val_156_ = lean_ctor_get(v_t_146_, 1);
lean_inc(v_val_156_);
v_x_157_ = lean_ctor_get(v_t_146_, 2);
lean_inc(v_x_157_);
v_n_158_ = lean_ctor_get(v_t_146_, 3);
lean_inc(v_n_158_);
lean_dec_ref_known(v_t_146_, 4);
v___x_159_ = lean_apply_4(v_k_147_, v_c_155_, v_val_156_, v_x_157_, v_n_158_);
return v___x_159_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim(lean_object* v_motive__2_160_, lean_object* v_ctorIdx_161_, lean_object* v_t_162_, lean_object* v_h_163_, lean_object* v_k_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___redArg(v_t_162_, v_k_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___boxed(lean_object* v_motive__2_166_, lean_object* v_ctorIdx_167_, lean_object* v_t_168_, lean_object* v_h_169_, lean_object* v_k_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim(v_motive__2_166_, v_ctorIdx_167_, v_t_168_, v_h_169_, v_k_170_);
lean_dec(v_ctorIdx_167_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_core_elim___redArg(lean_object* v_t_172_, lean_object* v_core_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___redArg(v_t_172_, v_core_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_core_elim(lean_object* v_motive__2_175_, lean_object* v_t_176_, lean_object* v_h_177_, lean_object* v_core_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___redArg(v_t_176_, v_core_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_symm_elim___redArg(lean_object* v_t_180_, lean_object* v_symm_181_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___redArg(v_t_180_, v_symm_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_symm_elim(lean_object* v_motive__2_183_, lean_object* v_t_184_, lean_object* v_h_185_, lean_object* v_symm_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___redArg(v_t_184_, v_symm_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_cancelDen_elim___redArg(lean_object* v_t_188_, lean_object* v_cancelDen_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___redArg(v_t_188_, v_cancelDen_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_cancelDen_elim(lean_object* v_motive__2_191_, lean_object* v_t_192_, lean_object* v_h_193_, lean_object* v_cancelDen_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___redArg(v_t_192_, v_cancelDen_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorIdx___impl(lean_object* v_x_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = lean_obj_tag_nat(v_x_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorIdx___impl___boxed(lean_object* v_x_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorIdx___impl(v_x_198_);
lean_dec_ref(v_x_198_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim___redArg(lean_object* v_t_200_, lean_object* v_k_201_){
_start:
{
if (lean_obj_tag(v_t_200_) == 0)
{
lean_object* v_a_202_; lean_object* v_b_203_; lean_object* v_ra_204_; lean_object* v_rb_205_; lean_object* v___x_206_; 
v_a_202_ = lean_ctor_get(v_t_200_, 0);
lean_inc_ref(v_a_202_);
v_b_203_ = lean_ctor_get(v_t_200_, 1);
lean_inc_ref(v_b_203_);
v_ra_204_ = lean_ctor_get(v_t_200_, 2);
lean_inc_ref(v_ra_204_);
v_rb_205_ = lean_ctor_get(v_t_200_, 3);
lean_inc_ref(v_rb_205_);
lean_dec_ref_known(v_t_200_, 4);
v___x_206_ = lean_apply_4(v_k_201_, v_a_202_, v_b_203_, v_ra_204_, v_rb_205_);
return v___x_206_;
}
else
{
lean_object* v_c_207_; lean_object* v_val_208_; lean_object* v_x_209_; lean_object* v_n_210_; lean_object* v___x_211_; 
v_c_207_ = lean_ctor_get(v_t_200_, 0);
lean_inc_ref(v_c_207_);
v_val_208_ = lean_ctor_get(v_t_200_, 1);
lean_inc(v_val_208_);
v_x_209_ = lean_ctor_get(v_t_200_, 2);
lean_inc(v_x_209_);
v_n_210_ = lean_ctor_get(v_t_200_, 3);
lean_inc(v_n_210_);
lean_dec_ref_known(v_t_200_, 4);
v___x_211_ = lean_apply_4(v_k_201_, v_c_207_, v_val_208_, v_x_209_, v_n_210_);
return v___x_211_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim(lean_object* v_motive__2_212_, lean_object* v_ctorIdx_213_, lean_object* v_t_214_, lean_object* v_h_215_, lean_object* v_k_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim___redArg(v_t_214_, v_k_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim___boxed(lean_object* v_motive__2_218_, lean_object* v_ctorIdx_219_, lean_object* v_t_220_, lean_object* v_h_221_, lean_object* v_k_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim(v_motive__2_218_, v_ctorIdx_219_, v_t_220_, v_h_221_, v_k_222_);
lean_dec(v_ctorIdx_219_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_core_elim___redArg(lean_object* v_t_224_, lean_object* v_core_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim___redArg(v_t_224_, v_core_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_core_elim(lean_object* v_motive__2_227_, lean_object* v_t_228_, lean_object* v_h_229_, lean_object* v_core_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim___redArg(v_t_228_, v_core_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_cancelDen_elim___redArg(lean_object* v_t_232_, lean_object* v_cancelDen_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim___redArg(v_t_232_, v_cancelDen_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_cancelDen_elim(lean_object* v_motive__2_235_, lean_object* v_t_236_, lean_object* v_h_237_, lean_object* v_cancelDen_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim___redArg(v_t_236_, v_cancelDen_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorIdx___impl(lean_object* v_x_240_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = lean_obj_tag_nat(v_x_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorIdx___impl___boxed(lean_object* v_x_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorIdx___impl(v_x_242_);
lean_dec_ref(v_x_242_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(lean_object* v_t_244_, lean_object* v_k_245_){
_start:
{
switch(lean_obj_tag(v_t_244_))
{
case 0:
{
lean_object* v_a_246_; lean_object* v_b_247_; lean_object* v_lhs_248_; lean_object* v_rhs_249_; lean_object* v___x_250_; 
v_a_246_ = lean_ctor_get(v_t_244_, 0);
lean_inc_ref(v_a_246_);
v_b_247_ = lean_ctor_get(v_t_244_, 1);
lean_inc_ref(v_b_247_);
v_lhs_248_ = lean_ctor_get(v_t_244_, 2);
lean_inc(v_lhs_248_);
v_rhs_249_ = lean_ctor_get(v_t_244_, 3);
lean_inc(v_rhs_249_);
lean_dec_ref_known(v_t_244_, 4);
v___x_250_ = lean_apply_4(v_k_245_, v_a_246_, v_b_247_, v_lhs_248_, v_rhs_249_);
return v___x_250_;
}
case 1:
{
lean_object* v_a_251_; lean_object* v_b_252_; lean_object* v_ra_253_; lean_object* v_rb_254_; lean_object* v_p_255_; lean_object* v_lhs_x27_256_; lean_object* v___x_257_; 
v_a_251_ = lean_ctor_get(v_t_244_, 0);
lean_inc_ref(v_a_251_);
v_b_252_ = lean_ctor_get(v_t_244_, 1);
lean_inc_ref(v_b_252_);
v_ra_253_ = lean_ctor_get(v_t_244_, 2);
lean_inc_ref(v_ra_253_);
v_rb_254_ = lean_ctor_get(v_t_244_, 3);
lean_inc_ref(v_rb_254_);
v_p_255_ = lean_ctor_get(v_t_244_, 4);
lean_inc_ref(v_p_255_);
v_lhs_x27_256_ = lean_ctor_get(v_t_244_, 5);
lean_inc(v_lhs_x27_256_);
lean_dec_ref_known(v_t_244_, 6);
v___x_257_ = lean_apply_6(v_k_245_, v_a_251_, v_b_252_, v_ra_253_, v_rb_254_, v_p_255_, v_lhs_x27_256_);
return v___x_257_;
}
case 2:
{
lean_object* v_a_258_; lean_object* v_b_259_; lean_object* v_natStructId_260_; lean_object* v_lhs_261_; lean_object* v_rhs_262_; lean_object* v___x_263_; 
v_a_258_ = lean_ctor_get(v_t_244_, 0);
lean_inc_ref(v_a_258_);
v_b_259_ = lean_ctor_get(v_t_244_, 1);
lean_inc_ref(v_b_259_);
v_natStructId_260_ = lean_ctor_get(v_t_244_, 2);
lean_inc(v_natStructId_260_);
v_lhs_261_ = lean_ctor_get(v_t_244_, 3);
lean_inc(v_lhs_261_);
v_rhs_262_ = lean_ctor_get(v_t_244_, 4);
lean_inc(v_rhs_262_);
lean_dec_ref_known(v_t_244_, 5);
v___x_263_ = lean_apply_5(v_k_245_, v_a_258_, v_b_259_, v_natStructId_260_, v_lhs_261_, v_rhs_262_);
return v___x_263_;
}
case 3:
{
lean_object* v_c_264_; lean_object* v___x_265_; 
v_c_264_ = lean_ctor_get(v_t_244_, 0);
lean_inc_ref(v_c_264_);
lean_dec_ref_known(v_t_244_, 1);
v___x_265_ = lean_apply_1(v_k_245_, v_c_264_);
return v___x_265_;
}
case 4:
{
lean_object* v_k_266_; lean_object* v_c_267_; lean_object* v___x_268_; 
v_k_266_ = lean_ctor_get(v_t_244_, 0);
lean_inc(v_k_266_);
v_c_267_ = lean_ctor_get(v_t_244_, 1);
lean_inc_ref(v_c_267_);
lean_dec_ref_known(v_t_244_, 2);
v___x_268_ = lean_apply_2(v_k_245_, v_k_266_, v_c_267_);
return v___x_268_;
}
default: 
{
lean_object* v_x_269_; lean_object* v_c_u2081_270_; lean_object* v_c_u2082_271_; lean_object* v___x_272_; 
v_x_269_ = lean_ctor_get(v_t_244_, 0);
lean_inc(v_x_269_);
v_c_u2081_270_ = lean_ctor_get(v_t_244_, 1);
lean_inc_ref(v_c_u2081_270_);
v_c_u2082_271_ = lean_ctor_get(v_t_244_, 2);
lean_inc_ref(v_c_u2082_271_);
lean_dec_ref_known(v_t_244_, 3);
v___x_272_ = lean_apply_3(v_k_245_, v_x_269_, v_c_u2081_270_, v_c_u2082_271_);
return v___x_272_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim(lean_object* v_motive__2_273_, lean_object* v_ctorIdx_274_, lean_object* v_t_275_, lean_object* v_h_276_, lean_object* v_k_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_275_, v_k_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___boxed(lean_object* v_motive__2_279_, lean_object* v_ctorIdx_280_, lean_object* v_t_281_, lean_object* v_h_282_, lean_object* v_k_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim(v_motive__2_279_, v_ctorIdx_280_, v_t_281_, v_h_282_, v_k_283_);
lean_dec(v_ctorIdx_280_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_core_elim___redArg(lean_object* v_t_285_, lean_object* v_core_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_285_, v_core_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_core_elim(lean_object* v_motive__2_288_, lean_object* v_t_289_, lean_object* v_h_290_, lean_object* v_core_291_){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_289_, v_core_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_coreCommRing_elim___redArg(lean_object* v_t_293_, lean_object* v_coreCommRing_294_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_293_, v_coreCommRing_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_coreCommRing_elim(lean_object* v_motive__2_296_, lean_object* v_t_297_, lean_object* v_h_298_, lean_object* v_coreCommRing_299_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_297_, v_coreCommRing_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_coreOfNat_elim___redArg(lean_object* v_t_301_, lean_object* v_coreOfNat_302_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_301_, v_coreOfNat_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_coreOfNat_elim(lean_object* v_motive__2_304_, lean_object* v_t_305_, lean_object* v_h_306_, lean_object* v_coreOfNat_307_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_305_, v_coreOfNat_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_neg_elim___redArg(lean_object* v_t_309_, lean_object* v_neg_310_){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_309_, v_neg_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_neg_elim(lean_object* v_motive__2_312_, lean_object* v_t_313_, lean_object* v_h_314_, lean_object* v_neg_315_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_313_, v_neg_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_coeff_elim___redArg(lean_object* v_t_317_, lean_object* v_coeff_318_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_317_, v_coeff_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_coeff_elim(lean_object* v_motive__2_320_, lean_object* v_t_321_, lean_object* v_h_322_, lean_object* v_coeff_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_321_, v_coeff_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_subst_elim___redArg(lean_object* v_t_325_, lean_object* v_subst_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_325_, v_subst_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_subst_elim(lean_object* v_motive__2_328_, lean_object* v_t_329_, lean_object* v_h_330_, lean_object* v_subst_331_){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_329_, v_subst_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorIdx___impl(lean_object* v_x_333_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = lean_obj_tag_nat(v_x_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorIdx___impl___boxed(lean_object* v_x_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorIdx___impl(v_x_335_);
lean_dec(v_x_335_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(lean_object* v_t_337_, lean_object* v_k_338_){
_start:
{
switch(lean_obj_tag(v_t_337_))
{
case 0:
{
lean_object* v_e_339_; lean_object* v_lhs_340_; lean_object* v_rhs_341_; lean_object* v___x_342_; 
v_e_339_ = lean_ctor_get(v_t_337_, 0);
lean_inc_ref(v_e_339_);
v_lhs_340_ = lean_ctor_get(v_t_337_, 1);
lean_inc(v_lhs_340_);
v_rhs_341_ = lean_ctor_get(v_t_337_, 2);
lean_inc(v_rhs_341_);
lean_dec_ref_known(v_t_337_, 3);
v___x_342_ = lean_apply_3(v_k_338_, v_e_339_, v_lhs_340_, v_rhs_341_);
return v___x_342_;
}
case 1:
{
lean_object* v_e_343_; lean_object* v_lhs_344_; lean_object* v_rhs_345_; lean_object* v___x_346_; 
v_e_343_ = lean_ctor_get(v_t_337_, 0);
lean_inc_ref(v_e_343_);
v_lhs_344_ = lean_ctor_get(v_t_337_, 1);
lean_inc(v_lhs_344_);
v_rhs_345_ = lean_ctor_get(v_t_337_, 2);
lean_inc(v_rhs_345_);
lean_dec_ref_known(v_t_337_, 3);
v___x_346_ = lean_apply_3(v_k_338_, v_e_343_, v_lhs_344_, v_rhs_345_);
return v___x_346_;
}
case 3:
{
lean_object* v_e_347_; lean_object* v_natStructId_348_; lean_object* v_lhs_349_; lean_object* v_rhs_350_; lean_object* v___x_351_; 
v_e_347_ = lean_ctor_get(v_t_337_, 0);
lean_inc_ref(v_e_347_);
v_natStructId_348_ = lean_ctor_get(v_t_337_, 1);
lean_inc(v_natStructId_348_);
v_lhs_349_ = lean_ctor_get(v_t_337_, 2);
lean_inc(v_lhs_349_);
v_rhs_350_ = lean_ctor_get(v_t_337_, 3);
lean_inc(v_rhs_350_);
lean_dec_ref_known(v_t_337_, 4);
v___x_351_ = lean_apply_4(v_k_338_, v_e_347_, v_natStructId_348_, v_lhs_349_, v_rhs_350_);
return v___x_351_;
}
case 4:
{
lean_object* v_e_352_; lean_object* v_natStructId_353_; lean_object* v_lhs_354_; lean_object* v_rhs_355_; lean_object* v___x_356_; 
v_e_352_ = lean_ctor_get(v_t_337_, 0);
lean_inc_ref(v_e_352_);
v_natStructId_353_ = lean_ctor_get(v_t_337_, 1);
lean_inc(v_natStructId_353_);
v_lhs_354_ = lean_ctor_get(v_t_337_, 2);
lean_inc(v_lhs_354_);
v_rhs_355_ = lean_ctor_get(v_t_337_, 3);
lean_inc(v_rhs_355_);
lean_dec_ref_known(v_t_337_, 4);
v___x_356_ = lean_apply_4(v_k_338_, v_e_352_, v_natStructId_353_, v_lhs_354_, v_rhs_355_);
return v___x_356_;
}
case 5:
{
lean_object* v_c_u2081_357_; lean_object* v_c_u2082_358_; lean_object* v___x_359_; 
v_c_u2081_357_ = lean_ctor_get(v_t_337_, 0);
lean_inc_ref(v_c_u2081_357_);
v_c_u2082_358_ = lean_ctor_get(v_t_337_, 1);
lean_inc_ref(v_c_u2082_358_);
lean_dec_ref_known(v_t_337_, 2);
v___x_359_ = lean_apply_2(v_k_338_, v_c_u2081_357_, v_c_u2082_358_);
return v___x_359_;
}
case 7:
{
lean_object* v_h_360_; lean_object* v___x_361_; 
v_h_360_ = lean_ctor_get(v_t_337_, 0);
lean_inc(v_h_360_);
lean_dec_ref_known(v_t_337_, 1);
v___x_361_ = lean_apply_1(v_k_338_, v_h_360_);
return v___x_361_;
}
case 8:
{
lean_object* v_c_u2081_362_; lean_object* v_decVar_363_; lean_object* v_h_364_; lean_object* v_decVars_365_; lean_object* v___x_366_; 
v_c_u2081_362_ = lean_ctor_get(v_t_337_, 0);
lean_inc_ref(v_c_u2081_362_);
v_decVar_363_ = lean_ctor_get(v_t_337_, 1);
lean_inc(v_decVar_363_);
v_h_364_ = lean_ctor_get(v_t_337_, 2);
lean_inc_ref(v_h_364_);
v_decVars_365_ = lean_ctor_get(v_t_337_, 3);
lean_inc_ref(v_decVars_365_);
lean_dec_ref_known(v_t_337_, 4);
v___x_366_ = lean_apply_4(v_k_338_, v_c_u2081_362_, v_decVar_363_, v_h_364_, v_decVars_365_);
return v___x_366_;
}
case 9:
{
return v_k_338_;
}
case 10:
{
lean_object* v_a_367_; lean_object* v_b_368_; lean_object* v_la_369_; lean_object* v_lb_370_; lean_object* v___x_371_; 
v_a_367_ = lean_ctor_get(v_t_337_, 0);
lean_inc_ref(v_a_367_);
v_b_368_ = lean_ctor_get(v_t_337_, 1);
lean_inc_ref(v_b_368_);
v_la_369_ = lean_ctor_get(v_t_337_, 2);
lean_inc(v_la_369_);
v_lb_370_ = lean_ctor_get(v_t_337_, 3);
lean_inc(v_lb_370_);
lean_dec_ref_known(v_t_337_, 4);
v___x_371_ = lean_apply_4(v_k_338_, v_a_367_, v_b_368_, v_la_369_, v_lb_370_);
return v___x_371_;
}
case 11:
{
lean_object* v_a_372_; lean_object* v_b_373_; lean_object* v_natStructId_374_; lean_object* v_la_375_; lean_object* v_lb_376_; lean_object* v___x_377_; 
v_a_372_ = lean_ctor_get(v_t_337_, 0);
lean_inc_ref(v_a_372_);
v_b_373_ = lean_ctor_get(v_t_337_, 1);
lean_inc_ref(v_b_373_);
v_natStructId_374_ = lean_ctor_get(v_t_337_, 2);
lean_inc(v_natStructId_374_);
v_la_375_ = lean_ctor_get(v_t_337_, 3);
lean_inc(v_la_375_);
v_lb_376_ = lean_ctor_get(v_t_337_, 4);
lean_inc(v_lb_376_);
lean_dec_ref_known(v_t_337_, 5);
v___x_377_ = lean_apply_5(v_k_338_, v_a_372_, v_b_373_, v_natStructId_374_, v_la_375_, v_lb_376_);
return v___x_377_;
}
case 13:
{
lean_object* v_x_378_; lean_object* v_c_u2081_379_; lean_object* v_c_u2082_380_; lean_object* v___x_381_; 
v_x_378_ = lean_ctor_get(v_t_337_, 0);
lean_inc(v_x_378_);
v_c_u2081_379_ = lean_ctor_get(v_t_337_, 1);
lean_inc_ref(v_c_u2081_379_);
v_c_u2082_380_ = lean_ctor_get(v_t_337_, 2);
lean_inc_ref(v_c_u2082_380_);
lean_dec_ref_known(v_t_337_, 3);
v___x_381_ = lean_apply_3(v_k_338_, v_x_378_, v_c_u2081_379_, v_c_u2082_380_);
return v___x_381_;
}
default: 
{
lean_object* v_c_382_; lean_object* v_lhs_383_; lean_object* v___x_384_; 
v_c_382_ = lean_ctor_get(v_t_337_, 0);
lean_inc_ref(v_c_382_);
v_lhs_383_ = lean_ctor_get(v_t_337_, 1);
lean_inc(v_lhs_383_);
lean_dec(v_t_337_);
v___x_384_ = lean_apply_2(v_k_338_, v_c_382_, v_lhs_383_);
return v___x_384_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim(lean_object* v_motive__4_385_, lean_object* v_ctorIdx_386_, lean_object* v_t_387_, lean_object* v_h_388_, lean_object* v_k_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_387_, v_k_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___boxed(lean_object* v_motive__4_391_, lean_object* v_ctorIdx_392_, lean_object* v_t_393_, lean_object* v_h_394_, lean_object* v_k_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim(v_motive__4_391_, v_ctorIdx_392_, v_t_393_, v_h_394_, v_k_395_);
lean_dec(v_ctorIdx_392_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_core_elim___redArg(lean_object* v_t_397_, lean_object* v_core_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_397_, v_core_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_core_elim(lean_object* v_motive__4_400_, lean_object* v_t_401_, lean_object* v_h_402_, lean_object* v_core_403_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_401_, v_core_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_notCore_elim___redArg(lean_object* v_t_405_, lean_object* v_notCore_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_405_, v_notCore_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_notCore_elim(lean_object* v_motive__4_408_, lean_object* v_t_409_, lean_object* v_h_410_, lean_object* v_notCore_411_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_409_, v_notCore_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ring_elim___redArg(lean_object* v_t_413_, lean_object* v_ring_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_413_, v_ring_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ring_elim(lean_object* v_motive__4_416_, lean_object* v_t_417_, lean_object* v_h_418_, lean_object* v_ring_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_417_, v_ring_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_coreOfNat_elim___redArg(lean_object* v_t_421_, lean_object* v_coreOfNat_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_421_, v_coreOfNat_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_coreOfNat_elim(lean_object* v_motive__4_424_, lean_object* v_t_425_, lean_object* v_h_426_, lean_object* v_coreOfNat_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_425_, v_coreOfNat_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_notCoreOfNat_elim___redArg(lean_object* v_t_429_, lean_object* v_notCoreOfNat_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_429_, v_notCoreOfNat_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_notCoreOfNat_elim(lean_object* v_motive__4_432_, lean_object* v_t_433_, lean_object* v_h_434_, lean_object* v_notCoreOfNat_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_433_, v_notCoreOfNat_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_combine_elim___redArg(lean_object* v_t_437_, lean_object* v_combine_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_437_, v_combine_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_combine_elim(lean_object* v_motive__4_440_, lean_object* v_t_441_, lean_object* v_h_442_, lean_object* v_combine_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_441_, v_combine_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_norm_elim___redArg(lean_object* v_t_445_, lean_object* v_norm_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_445_, v_norm_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_norm_elim(lean_object* v_motive__4_448_, lean_object* v_t_449_, lean_object* v_h_450_, lean_object* v_norm_451_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_449_, v_norm_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_dec_elim___redArg(lean_object* v_t_453_, lean_object* v_dec_454_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_453_, v_dec_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_dec_elim(lean_object* v_motive__4_456_, lean_object* v_t_457_, lean_object* v_h_458_, lean_object* v_dec_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_457_, v_dec_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ofDiseqSplit_elim___redArg(lean_object* v_t_461_, lean_object* v_ofDiseqSplit_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_461_, v_ofDiseqSplit_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ofDiseqSplit_elim(lean_object* v_motive__4_464_, lean_object* v_t_465_, lean_object* v_h_466_, lean_object* v_ofDiseqSplit_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_465_, v_ofDiseqSplit_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_oneGtZero_elim___redArg(lean_object* v_t_469_, lean_object* v_oneGtZero_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_469_, v_oneGtZero_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_oneGtZero_elim(lean_object* v_motive__4_472_, lean_object* v_t_473_, lean_object* v_h_474_, lean_object* v_oneGtZero_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_473_, v_oneGtZero_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ofEq_elim___redArg(lean_object* v_t_477_, lean_object* v_ofEq_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_477_, v_ofEq_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ofEq_elim(lean_object* v_motive__4_480_, lean_object* v_t_481_, lean_object* v_h_482_, lean_object* v_ofEq_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_481_, v_ofEq_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ofEqOfNat_elim___redArg(lean_object* v_t_485_, lean_object* v_ofEqOfNat_486_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_485_, v_ofEqOfNat_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ofEqOfNat_elim(lean_object* v_motive__4_488_, lean_object* v_t_489_, lean_object* v_h_490_, lean_object* v_ofEqOfNat_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_489_, v_ofEqOfNat_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ringEq_elim___redArg(lean_object* v_t_493_, lean_object* v_ringEq_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_493_, v_ringEq_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ringEq_elim(lean_object* v_motive__4_496_, lean_object* v_t_497_, lean_object* v_h_498_, lean_object* v_ringEq_499_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_497_, v_ringEq_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_subst_elim___redArg(lean_object* v_t_501_, lean_object* v_subst_502_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_501_, v_subst_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_subst_elim(lean_object* v_motive__4_504_, lean_object* v_t_505_, lean_object* v_h_506_, lean_object* v_subst_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_505_, v_subst_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorIdx___impl(lean_object* v_x_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = lean_obj_tag_nat(v_x_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorIdx___impl___boxed(lean_object* v_x_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorIdx___impl(v_x_511_);
lean_dec(v_x_511_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(lean_object* v_t_513_, lean_object* v_k_514_){
_start:
{
switch(lean_obj_tag(v_t_513_))
{
case 0:
{
lean_object* v_a_515_; lean_object* v_b_516_; lean_object* v_lhs_517_; lean_object* v_rhs_518_; lean_object* v___x_519_; 
v_a_515_ = lean_ctor_get(v_t_513_, 0);
lean_inc_ref(v_a_515_);
v_b_516_ = lean_ctor_get(v_t_513_, 1);
lean_inc_ref(v_b_516_);
v_lhs_517_ = lean_ctor_get(v_t_513_, 2);
lean_inc(v_lhs_517_);
v_rhs_518_ = lean_ctor_get(v_t_513_, 3);
lean_inc(v_rhs_518_);
lean_dec_ref_known(v_t_513_, 4);
v___x_519_ = lean_apply_4(v_k_514_, v_a_515_, v_b_516_, v_lhs_517_, v_rhs_518_);
return v___x_519_;
}
case 1:
{
lean_object* v_c_520_; lean_object* v_lhs_521_; lean_object* v___x_522_; 
v_c_520_ = lean_ctor_get(v_t_513_, 0);
lean_inc_ref(v_c_520_);
v_lhs_521_ = lean_ctor_get(v_t_513_, 1);
lean_inc(v_lhs_521_);
lean_dec_ref_known(v_t_513_, 2);
v___x_522_ = lean_apply_2(v_k_514_, v_c_520_, v_lhs_521_);
return v___x_522_;
}
case 2:
{
lean_object* v_a_523_; lean_object* v_b_524_; lean_object* v_natStructId_525_; lean_object* v_lhs_526_; lean_object* v_rhs_527_; lean_object* v___x_528_; 
v_a_523_ = lean_ctor_get(v_t_513_, 0);
lean_inc_ref(v_a_523_);
v_b_524_ = lean_ctor_get(v_t_513_, 1);
lean_inc_ref(v_b_524_);
v_natStructId_525_ = lean_ctor_get(v_t_513_, 2);
lean_inc(v_natStructId_525_);
v_lhs_526_ = lean_ctor_get(v_t_513_, 3);
lean_inc(v_lhs_526_);
v_rhs_527_ = lean_ctor_get(v_t_513_, 4);
lean_inc(v_rhs_527_);
lean_dec_ref_known(v_t_513_, 5);
v___x_528_ = lean_apply_5(v_k_514_, v_a_523_, v_b_524_, v_natStructId_525_, v_lhs_526_, v_rhs_527_);
return v___x_528_;
}
case 3:
{
lean_object* v_c_529_; lean_object* v___x_530_; 
v_c_529_ = lean_ctor_get(v_t_513_, 0);
lean_inc_ref(v_c_529_);
lean_dec_ref_known(v_t_513_, 1);
v___x_530_ = lean_apply_1(v_k_514_, v_c_529_);
return v___x_530_;
}
case 4:
{
lean_object* v_k_u2081_531_; lean_object* v_k_u2082_532_; lean_object* v_c_u2081_533_; lean_object* v_c_u2082_534_; lean_object* v___x_535_; 
v_k_u2081_531_ = lean_ctor_get(v_t_513_, 0);
lean_inc(v_k_u2081_531_);
v_k_u2082_532_ = lean_ctor_get(v_t_513_, 1);
lean_inc(v_k_u2082_532_);
v_c_u2081_533_ = lean_ctor_get(v_t_513_, 2);
lean_inc_ref(v_c_u2081_533_);
v_c_u2082_534_ = lean_ctor_get(v_t_513_, 3);
lean_inc_ref(v_c_u2082_534_);
lean_dec_ref_known(v_t_513_, 4);
v___x_535_ = lean_apply_4(v_k_514_, v_k_u2081_531_, v_k_u2082_532_, v_c_u2081_533_, v_c_u2082_534_);
return v___x_535_;
}
case 5:
{
lean_object* v_k_536_; lean_object* v_c_u2081_537_; lean_object* v_c_u2082_538_; lean_object* v___x_539_; 
v_k_536_ = lean_ctor_get(v_t_513_, 0);
lean_inc(v_k_536_);
v_c_u2081_537_ = lean_ctor_get(v_t_513_, 1);
lean_inc_ref(v_c_u2081_537_);
v_c_u2082_538_ = lean_ctor_get(v_t_513_, 2);
lean_inc_ref(v_c_u2082_538_);
lean_dec_ref_known(v_t_513_, 3);
v___x_539_ = lean_apply_3(v_k_514_, v_k_536_, v_c_u2081_537_, v_c_u2082_538_);
return v___x_539_;
}
default: 
{
return v_k_514_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim(lean_object* v_motive__6_540_, lean_object* v_ctorIdx_541_, lean_object* v_t_542_, lean_object* v_h_543_, lean_object* v_k_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_542_, v_k_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___boxed(lean_object* v_motive__6_546_, lean_object* v_ctorIdx_547_, lean_object* v_t_548_, lean_object* v_h_549_, lean_object* v_k_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim(v_motive__6_546_, v_ctorIdx_547_, v_t_548_, v_h_549_, v_k_550_);
lean_dec(v_ctorIdx_547_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_core_elim___redArg(lean_object* v_t_552_, lean_object* v_core_553_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_552_, v_core_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_core_elim(lean_object* v_motive__6_555_, lean_object* v_t_556_, lean_object* v_h_557_, lean_object* v_core_558_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_556_, v_core_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ring_elim___redArg(lean_object* v_t_560_, lean_object* v_ring_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_560_, v_ring_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ring_elim(lean_object* v_motive__6_563_, lean_object* v_t_564_, lean_object* v_h_565_, lean_object* v_ring_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_564_, v_ring_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_coreOfNat_elim___redArg(lean_object* v_t_568_, lean_object* v_coreOfNat_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_568_, v_coreOfNat_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_coreOfNat_elim(lean_object* v_motive__6_571_, lean_object* v_t_572_, lean_object* v_h_573_, lean_object* v_coreOfNat_574_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_572_, v_coreOfNat_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_neg_elim___redArg(lean_object* v_t_576_, lean_object* v_neg_577_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_576_, v_neg_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_neg_elim(lean_object* v_motive__6_579_, lean_object* v_t_580_, lean_object* v_h_581_, lean_object* v_neg_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_580_, v_neg_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_subst_elim___redArg(lean_object* v_t_584_, lean_object* v_subst_585_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_584_, v_subst_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_subst_elim(lean_object* v_motive__6_587_, lean_object* v_t_588_, lean_object* v_h_589_, lean_object* v_subst_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_588_, v_subst_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_subst1_elim___redArg(lean_object* v_t_592_, lean_object* v_subst1_593_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_592_, v_subst1_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_subst1_elim(lean_object* v_motive__6_595_, lean_object* v_t_596_, lean_object* v_h_597_, lean_object* v_subst1_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_596_, v_subst1_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_oneNeZero_elim___redArg(lean_object* v_t_600_, lean_object* v_oneNeZero_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_600_, v_oneNeZero_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_oneNeZero_elim(lean_object* v_motive__6_603_, lean_object* v_t_604_, lean_object* v_h_605_, lean_object* v_oneNeZero_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_604_, v_oneNeZero_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorIdx___impl(lean_object* v_x_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = lean_obj_tag_nat(v_x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorIdx___impl___boxed(lean_object* v_x_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorIdx___impl(v_x_610_);
lean_dec_ref(v_x_610_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorElim___redArg(lean_object* v_t_612_, lean_object* v_k_613_){
_start:
{
lean_object* v_c_614_; lean_object* v___x_615_; 
v_c_614_ = lean_ctor_get(v_t_612_, 0);
lean_inc_ref(v_c_614_);
lean_dec_ref(v_t_612_);
v___x_615_ = lean_apply_1(v_k_613_, v_c_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorElim(lean_object* v_motive__7_616_, lean_object* v_ctorIdx_617_, lean_object* v_t_618_, lean_object* v_h_619_, lean_object* v_k_620_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorElim___redArg(v_t_618_, v_k_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorElim___boxed(lean_object* v_motive__7_622_, lean_object* v_ctorIdx_623_, lean_object* v_t_624_, lean_object* v_h_625_, lean_object* v_k_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorElim(v_motive__7_622_, v_ctorIdx_623_, v_t_624_, v_h_625_, v_k_626_);
lean_dec(v_ctorIdx_623_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_diseq_elim___redArg(lean_object* v_t_628_, lean_object* v_diseq_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorElim___redArg(v_t_628_, v_diseq_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_diseq_elim(lean_object* v_motive__7_631_, lean_object* v_t_632_, lean_object* v_h_633_, lean_object* v_diseq_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorElim___redArg(v_t_632_, v_diseq_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_lt_elim___redArg(lean_object* v_t_636_, lean_object* v_lt_637_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorElim___redArg(v_t_636_, v_lt_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_lt_elim(lean_object* v_motive__7_639_, lean_object* v_t_640_, lean_object* v_h_641_, lean_object* v_lt_642_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorElim___redArg(v_t_640_, v_lt_642_);
return v___x_643_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_647_ = lean_box(0);
v___x_648_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__1));
v___x_649_ = l_Lean_Expr_const___override(v___x_648_, v___x_647_);
return v___x_649_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__3(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_650_ = lean_box(0);
v___x_651_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2);
v___x_652_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
lean_ctor_set(v___x_652_, 2, v___x_650_);
lean_ctor_set(v___x_652_, 3, v___x_650_);
return v___x_652_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__4(void){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_653_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__3, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__3);
v___x_654_ = lean_box(0);
v___x_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
lean_ctor_set(v___x_655_, 1, v___x_653_);
return v___x_655_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr(void){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__4, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__4);
return v___x_656_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__0(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_657_ = lean_box(0);
v___x_658_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2);
v___x_659_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
lean_ctor_set(v___x_659_, 2, v___x_657_);
lean_ctor_set(v___x_659_, 3, v___x_657_);
return v___x_659_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__1(void){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_660_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__0, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__0);
v___x_661_ = lean_box(0);
v___x_662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_661_);
lean_ctor_set(v___x_662_, 1, v___x_660_);
return v___x_662_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr(void){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__1, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__1);
return v___x_663_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__0(void){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_664_ = lean_unsigned_to_nat(32u);
v___x_665_ = lean_mk_empty_array_with_capacity(v___x_664_);
v___x_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
return v___x_666_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__1(void){
_start:
{
size_t v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_667_ = ((size_t)5ULL);
v___x_668_ = lean_unsigned_to_nat(0u);
v___x_669_ = lean_unsigned_to_nat(32u);
v___x_670_ = lean_mk_empty_array_with_capacity(v___x_669_);
v___x_671_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__0, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__0);
v___x_672_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_672_, 0, v___x_671_);
lean_ctor_set(v___x_672_, 1, v___x_670_);
lean_ctor_set(v___x_672_, 2, v___x_668_);
lean_ctor_set(v___x_672_, 3, v___x_668_);
lean_ctor_set_usize(v___x_672_, 4, v___x_667_);
return v___x_672_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__2(void){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_673_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__3(void){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__2, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__2);
v___x_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
return v___x_675_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__4(void){
_start:
{
lean_object* v___x_676_; uint8_t v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_676_ = lean_box(0);
v___x_677_ = 0;
v___x_678_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__3, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__3);
v___x_679_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__1, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__1);
v___x_680_ = lean_box(0);
v___x_681_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2);
v___x_682_ = lean_box(0);
v___x_683_ = lean_unsigned_to_nat(0u);
v___x_684_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v___x_684_, 0, v___x_683_);
lean_ctor_set(v___x_684_, 1, v___x_682_);
lean_ctor_set(v___x_684_, 2, v___x_681_);
lean_ctor_set(v___x_684_, 3, v___x_680_);
lean_ctor_set(v___x_684_, 4, v___x_681_);
lean_ctor_set(v___x_684_, 5, v___x_682_);
lean_ctor_set(v___x_684_, 6, v___x_682_);
lean_ctor_set(v___x_684_, 7, v___x_682_);
lean_ctor_set(v___x_684_, 8, v___x_682_);
lean_ctor_set(v___x_684_, 9, v___x_682_);
lean_ctor_set(v___x_684_, 10, v___x_682_);
lean_ctor_set(v___x_684_, 11, v___x_682_);
lean_ctor_set(v___x_684_, 12, v___x_682_);
lean_ctor_set(v___x_684_, 13, v___x_682_);
lean_ctor_set(v___x_684_, 14, v___x_682_);
lean_ctor_set(v___x_684_, 15, v___x_682_);
lean_ctor_set(v___x_684_, 16, v___x_682_);
lean_ctor_set(v___x_684_, 17, v___x_681_);
lean_ctor_set(v___x_684_, 18, v___x_681_);
lean_ctor_set(v___x_684_, 19, v___x_682_);
lean_ctor_set(v___x_684_, 20, v___x_682_);
lean_ctor_set(v___x_684_, 21, v___x_682_);
lean_ctor_set(v___x_684_, 22, v___x_681_);
lean_ctor_set(v___x_684_, 23, v___x_681_);
lean_ctor_set(v___x_684_, 24, v___x_681_);
lean_ctor_set(v___x_684_, 25, v___x_682_);
lean_ctor_set(v___x_684_, 26, v___x_682_);
lean_ctor_set(v___x_684_, 27, v___x_682_);
lean_ctor_set(v___x_684_, 28, v___x_681_);
lean_ctor_set(v___x_684_, 29, v___x_681_);
lean_ctor_set(v___x_684_, 30, v___x_679_);
lean_ctor_set(v___x_684_, 31, v___x_678_);
lean_ctor_set(v___x_684_, 32, v___x_679_);
lean_ctor_set(v___x_684_, 33, v___x_679_);
lean_ctor_set(v___x_684_, 34, v___x_679_);
lean_ctor_set(v___x_684_, 35, v___x_679_);
lean_ctor_set(v___x_684_, 36, v___x_682_);
lean_ctor_set(v___x_684_, 37, v___x_678_);
lean_ctor_set(v___x_684_, 38, v___x_679_);
lean_ctor_set(v___x_684_, 39, v___x_676_);
lean_ctor_set(v___x_684_, 40, v___x_679_);
lean_ctor_set(v___x_684_, 41, v___x_679_);
lean_ctor_set_uint8(v___x_684_, sizeof(void*)*42, v___x_677_);
return v___x_684_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default(void){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__4, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__4);
return v___x_685_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct(void){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default;
return v___x_686_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__2, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__2);
v___x_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___redArg(){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___redArg___closed__0);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___redArg___boxed(lean_object* v___dummy_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___redArg();
return v_res_692_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___redArg();
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0(lean_object* v_00_u03b2_694_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__0);
return v___x_695_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__1(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__2, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__2);
v___x_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
return v___x_699_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__2(void){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_700_ = lean_unsigned_to_nat(32u);
v___x_701_ = lean_mk_empty_array_with_capacity(v___x_700_);
v___x_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_702_, 0, v___x_701_);
return v___x_702_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__3(void){
_start:
{
size_t v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_703_ = ((size_t)5ULL);
v___x_704_ = lean_unsigned_to_nat(0u);
v___x_705_ = lean_unsigned_to_nat(32u);
v___x_706_ = lean_mk_empty_array_with_capacity(v___x_705_);
v___x_707_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__2, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__2);
v___x_708_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_708_, 0, v___x_707_);
lean_ctor_set(v___x_708_, 1, v___x_706_);
lean_ctor_set(v___x_708_, 2, v___x_704_);
lean_ctor_set(v___x_708_, 3, v___x_704_);
lean_ctor_set_usize(v___x_708_, 4, v___x_703_);
return v___x_708_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__4(void){
_start:
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_709_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__0);
v___x_710_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__3, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__3);
v___x_711_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__1, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__1);
v___x_712_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__0));
v___x_713_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
lean_ctor_set(v___x_713_, 1, v___x_711_);
lean_ctor_set(v___x_713_, 2, v___x_711_);
lean_ctor_set(v___x_713_, 3, v___x_710_);
lean_ctor_set(v___x_713_, 4, v___x_709_);
lean_ctor_set(v___x_713_, 5, v___x_712_);
lean_ctor_set(v___x_713_, 6, v___x_711_);
lean_ctor_set(v___x_713_, 7, v___x_711_);
return v___x_713_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default(void){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__4, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__4);
return v___x_714_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState(void){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default;
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2_(lean_object* v___x_716_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_718_, 0, v___x_716_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2____boxed(lean_object* v___x_719_, lean_object* v___y_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2_(v___x_719_);
return v_res_721_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_722_; lean_object* v___f_723_; 
v___x_722_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__4, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__4);
v___f_723_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_723_, 0, v___x_722_);
return v___f_723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_725_; lean_object* v___x_726_; 
v___f_725_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2_);
v___x_726_ = l_Lean_Meta_Grind_registerSolverExtension___redArg(v___f_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2____boxed(lean_object* v_a_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2_();
return v_res_728_;
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
