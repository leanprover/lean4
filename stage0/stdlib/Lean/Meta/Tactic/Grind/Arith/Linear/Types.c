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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Grind_registerSolverExtension___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_core_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_core_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_notCore_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_notCore_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_cancelDen_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_cancelDen_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_core_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_core_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_symm_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_symm_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_cancelDen_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_cancelDen_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_core_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_core_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_cancelDen_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_cancelDen_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorIdx___boxed(lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__1;
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
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__5;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__6;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorIdx(lean_object* v_x_91_){
_start:
{
switch(lean_obj_tag(v_x_91_))
{
case 0:
{
lean_object* v___x_92_; 
v___x_92_ = lean_unsigned_to_nat(0u);
return v___x_92_;
}
case 1:
{
lean_object* v___x_93_; 
v___x_93_ = lean_unsigned_to_nat(1u);
return v___x_93_;
}
default: 
{
lean_object* v___x_94_; 
v___x_94_ = lean_unsigned_to_nat(2u);
return v___x_94_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorIdx___boxed(lean_object* v_x_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstrProof_ctorIdx(v_x_95_);
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
lean_dec_ref(v_t_97_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorIdx(lean_object* v_x_144_){
_start:
{
switch(lean_obj_tag(v_x_144_))
{
case 0:
{
lean_object* v___x_145_; 
v___x_145_ = lean_unsigned_to_nat(0u);
return v___x_145_;
}
case 1:
{
lean_object* v___x_146_; 
v___x_146_ = lean_unsigned_to_nat(1u);
return v___x_146_;
}
default: 
{
lean_object* v___x_147_; 
v___x_147_ = lean_unsigned_to_nat(2u);
return v___x_147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorIdx___boxed(lean_object* v_x_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorIdx(v_x_148_);
lean_dec_ref(v_x_148_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___redArg(lean_object* v_t_150_, lean_object* v_k_151_){
_start:
{
switch(lean_obj_tag(v_t_150_))
{
case 0:
{
lean_object* v_a_152_; lean_object* v_b_153_; lean_object* v_ra_154_; lean_object* v_rb_155_; lean_object* v___x_156_; 
v_a_152_ = lean_ctor_get(v_t_150_, 0);
lean_inc_ref(v_a_152_);
v_b_153_ = lean_ctor_get(v_t_150_, 1);
lean_inc_ref(v_b_153_);
v_ra_154_ = lean_ctor_get(v_t_150_, 2);
lean_inc_ref(v_ra_154_);
v_rb_155_ = lean_ctor_get(v_t_150_, 3);
lean_inc_ref(v_rb_155_);
lean_dec_ref(v_t_150_);
v___x_156_ = lean_apply_4(v_k_151_, v_a_152_, v_b_153_, v_ra_154_, v_rb_155_);
return v___x_156_;
}
case 1:
{
lean_object* v_c_157_; lean_object* v___x_158_; 
v_c_157_ = lean_ctor_get(v_t_150_, 0);
lean_inc_ref(v_c_157_);
lean_dec_ref(v_t_150_);
v___x_158_ = lean_apply_1(v_k_151_, v_c_157_);
return v___x_158_;
}
default: 
{
lean_object* v_c_159_; lean_object* v_val_160_; lean_object* v_x_161_; lean_object* v_n_162_; lean_object* v___x_163_; 
v_c_159_ = lean_ctor_get(v_t_150_, 0);
lean_inc_ref(v_c_159_);
v_val_160_ = lean_ctor_get(v_t_150_, 1);
lean_inc(v_val_160_);
v_x_161_ = lean_ctor_get(v_t_150_, 2);
lean_inc(v_x_161_);
v_n_162_ = lean_ctor_get(v_t_150_, 3);
lean_inc(v_n_162_);
lean_dec_ref(v_t_150_);
v___x_163_ = lean_apply_4(v_k_151_, v_c_159_, v_val_160_, v_x_161_, v_n_162_);
return v___x_163_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim(lean_object* v_motive__2_164_, lean_object* v_ctorIdx_165_, lean_object* v_t_166_, lean_object* v_h_167_, lean_object* v_k_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___redArg(v_t_166_, v_k_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___boxed(lean_object* v_motive__2_170_, lean_object* v_ctorIdx_171_, lean_object* v_t_172_, lean_object* v_h_173_, lean_object* v_k_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim(v_motive__2_170_, v_ctorIdx_171_, v_t_172_, v_h_173_, v_k_174_);
lean_dec(v_ctorIdx_171_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_core_elim___redArg(lean_object* v_t_176_, lean_object* v_core_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___redArg(v_t_176_, v_core_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_core_elim(lean_object* v_motive__2_179_, lean_object* v_t_180_, lean_object* v_h_181_, lean_object* v_core_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___redArg(v_t_180_, v_core_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_symm_elim___redArg(lean_object* v_t_184_, lean_object* v_symm_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___redArg(v_t_184_, v_symm_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_symm_elim(lean_object* v_motive__2_187_, lean_object* v_t_188_, lean_object* v_h_189_, lean_object* v_symm_190_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___redArg(v_t_188_, v_symm_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_cancelDen_elim___redArg(lean_object* v_t_192_, lean_object* v_cancelDen_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___redArg(v_t_192_, v_cancelDen_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_cancelDen_elim(lean_object* v_motive__2_195_, lean_object* v_t_196_, lean_object* v_h_197_, lean_object* v_cancelDen_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstrProof_ctorElim___redArg(v_t_196_, v_cancelDen_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorIdx(lean_object* v_x_200_){
_start:
{
if (lean_obj_tag(v_x_200_) == 0)
{
lean_object* v___x_201_; 
v___x_201_ = lean_unsigned_to_nat(0u);
return v___x_201_;
}
else
{
lean_object* v___x_202_; 
v___x_202_ = lean_unsigned_to_nat(1u);
return v___x_202_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorIdx___boxed(lean_object* v_x_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorIdx(v_x_203_);
lean_dec_ref(v_x_203_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim___redArg(lean_object* v_t_205_, lean_object* v_k_206_){
_start:
{
if (lean_obj_tag(v_t_205_) == 0)
{
lean_object* v_a_207_; lean_object* v_b_208_; lean_object* v_ra_209_; lean_object* v_rb_210_; lean_object* v___x_211_; 
v_a_207_ = lean_ctor_get(v_t_205_, 0);
lean_inc_ref(v_a_207_);
v_b_208_ = lean_ctor_get(v_t_205_, 1);
lean_inc_ref(v_b_208_);
v_ra_209_ = lean_ctor_get(v_t_205_, 2);
lean_inc_ref(v_ra_209_);
v_rb_210_ = lean_ctor_get(v_t_205_, 3);
lean_inc_ref(v_rb_210_);
lean_dec_ref(v_t_205_);
v___x_211_ = lean_apply_4(v_k_206_, v_a_207_, v_b_208_, v_ra_209_, v_rb_210_);
return v___x_211_;
}
else
{
lean_object* v_c_212_; lean_object* v_val_213_; lean_object* v_x_214_; lean_object* v_n_215_; lean_object* v___x_216_; 
v_c_212_ = lean_ctor_get(v_t_205_, 0);
lean_inc_ref(v_c_212_);
v_val_213_ = lean_ctor_get(v_t_205_, 1);
lean_inc(v_val_213_);
v_x_214_ = lean_ctor_get(v_t_205_, 2);
lean_inc(v_x_214_);
v_n_215_ = lean_ctor_get(v_t_205_, 3);
lean_inc(v_n_215_);
lean_dec_ref(v_t_205_);
v___x_216_ = lean_apply_4(v_k_206_, v_c_212_, v_val_213_, v_x_214_, v_n_215_);
return v___x_216_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim(lean_object* v_motive__2_217_, lean_object* v_ctorIdx_218_, lean_object* v_t_219_, lean_object* v_h_220_, lean_object* v_k_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim___redArg(v_t_219_, v_k_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim___boxed(lean_object* v_motive__2_223_, lean_object* v_ctorIdx_224_, lean_object* v_t_225_, lean_object* v_h_226_, lean_object* v_k_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim(v_motive__2_223_, v_ctorIdx_224_, v_t_225_, v_h_226_, v_k_227_);
lean_dec(v_ctorIdx_224_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_core_elim___redArg(lean_object* v_t_229_, lean_object* v_core_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim___redArg(v_t_229_, v_core_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_core_elim(lean_object* v_motive__2_232_, lean_object* v_t_233_, lean_object* v_h_234_, lean_object* v_core_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim___redArg(v_t_233_, v_core_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_cancelDen_elim___redArg(lean_object* v_t_237_, lean_object* v_cancelDen_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim___redArg(v_t_237_, v_cancelDen_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_cancelDen_elim(lean_object* v_motive__2_240_, lean_object* v_t_241_, lean_object* v_h_242_, lean_object* v_cancelDen_243_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstrProof_ctorElim___redArg(v_t_241_, v_cancelDen_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorIdx(lean_object* v_x_245_){
_start:
{
switch(lean_obj_tag(v_x_245_))
{
case 0:
{
lean_object* v___x_246_; 
v___x_246_ = lean_unsigned_to_nat(0u);
return v___x_246_;
}
case 1:
{
lean_object* v___x_247_; 
v___x_247_ = lean_unsigned_to_nat(1u);
return v___x_247_;
}
case 2:
{
lean_object* v___x_248_; 
v___x_248_ = lean_unsigned_to_nat(2u);
return v___x_248_;
}
case 3:
{
lean_object* v___x_249_; 
v___x_249_ = lean_unsigned_to_nat(3u);
return v___x_249_;
}
case 4:
{
lean_object* v___x_250_; 
v___x_250_ = lean_unsigned_to_nat(4u);
return v___x_250_;
}
default: 
{
lean_object* v___x_251_; 
v___x_251_ = lean_unsigned_to_nat(5u);
return v___x_251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorIdx___boxed(lean_object* v_x_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorIdx(v_x_252_);
lean_dec_ref(v_x_252_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(lean_object* v_t_254_, lean_object* v_k_255_){
_start:
{
switch(lean_obj_tag(v_t_254_))
{
case 0:
{
lean_object* v_a_256_; lean_object* v_b_257_; lean_object* v_lhs_258_; lean_object* v_rhs_259_; lean_object* v___x_260_; 
v_a_256_ = lean_ctor_get(v_t_254_, 0);
lean_inc_ref(v_a_256_);
v_b_257_ = lean_ctor_get(v_t_254_, 1);
lean_inc_ref(v_b_257_);
v_lhs_258_ = lean_ctor_get(v_t_254_, 2);
lean_inc(v_lhs_258_);
v_rhs_259_ = lean_ctor_get(v_t_254_, 3);
lean_inc(v_rhs_259_);
lean_dec_ref(v_t_254_);
v___x_260_ = lean_apply_4(v_k_255_, v_a_256_, v_b_257_, v_lhs_258_, v_rhs_259_);
return v___x_260_;
}
case 1:
{
lean_object* v_a_261_; lean_object* v_b_262_; lean_object* v_ra_263_; lean_object* v_rb_264_; lean_object* v_p_265_; lean_object* v_lhs_x27_266_; lean_object* v___x_267_; 
v_a_261_ = lean_ctor_get(v_t_254_, 0);
lean_inc_ref(v_a_261_);
v_b_262_ = lean_ctor_get(v_t_254_, 1);
lean_inc_ref(v_b_262_);
v_ra_263_ = lean_ctor_get(v_t_254_, 2);
lean_inc_ref(v_ra_263_);
v_rb_264_ = lean_ctor_get(v_t_254_, 3);
lean_inc_ref(v_rb_264_);
v_p_265_ = lean_ctor_get(v_t_254_, 4);
lean_inc_ref(v_p_265_);
v_lhs_x27_266_ = lean_ctor_get(v_t_254_, 5);
lean_inc(v_lhs_x27_266_);
lean_dec_ref(v_t_254_);
v___x_267_ = lean_apply_6(v_k_255_, v_a_261_, v_b_262_, v_ra_263_, v_rb_264_, v_p_265_, v_lhs_x27_266_);
return v___x_267_;
}
case 2:
{
lean_object* v_a_268_; lean_object* v_b_269_; lean_object* v_natStructId_270_; lean_object* v_lhs_271_; lean_object* v_rhs_272_; lean_object* v___x_273_; 
v_a_268_ = lean_ctor_get(v_t_254_, 0);
lean_inc_ref(v_a_268_);
v_b_269_ = lean_ctor_get(v_t_254_, 1);
lean_inc_ref(v_b_269_);
v_natStructId_270_ = lean_ctor_get(v_t_254_, 2);
lean_inc(v_natStructId_270_);
v_lhs_271_ = lean_ctor_get(v_t_254_, 3);
lean_inc(v_lhs_271_);
v_rhs_272_ = lean_ctor_get(v_t_254_, 4);
lean_inc(v_rhs_272_);
lean_dec_ref(v_t_254_);
v___x_273_ = lean_apply_5(v_k_255_, v_a_268_, v_b_269_, v_natStructId_270_, v_lhs_271_, v_rhs_272_);
return v___x_273_;
}
case 3:
{
lean_object* v_c_274_; lean_object* v___x_275_; 
v_c_274_ = lean_ctor_get(v_t_254_, 0);
lean_inc_ref(v_c_274_);
lean_dec_ref(v_t_254_);
v___x_275_ = lean_apply_1(v_k_255_, v_c_274_);
return v___x_275_;
}
case 4:
{
lean_object* v_k_276_; lean_object* v_c_277_; lean_object* v___x_278_; 
v_k_276_ = lean_ctor_get(v_t_254_, 0);
lean_inc(v_k_276_);
v_c_277_ = lean_ctor_get(v_t_254_, 1);
lean_inc_ref(v_c_277_);
lean_dec_ref(v_t_254_);
v___x_278_ = lean_apply_2(v_k_255_, v_k_276_, v_c_277_);
return v___x_278_;
}
default: 
{
lean_object* v_x_279_; lean_object* v_c_u2081_280_; lean_object* v_c_u2082_281_; lean_object* v___x_282_; 
v_x_279_ = lean_ctor_get(v_t_254_, 0);
lean_inc(v_x_279_);
v_c_u2081_280_ = lean_ctor_get(v_t_254_, 1);
lean_inc_ref(v_c_u2081_280_);
v_c_u2082_281_ = lean_ctor_get(v_t_254_, 2);
lean_inc_ref(v_c_u2082_281_);
lean_dec_ref(v_t_254_);
v___x_282_ = lean_apply_3(v_k_255_, v_x_279_, v_c_u2081_280_, v_c_u2082_281_);
return v___x_282_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim(lean_object* v_motive__2_283_, lean_object* v_ctorIdx_284_, lean_object* v_t_285_, lean_object* v_h_286_, lean_object* v_k_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_285_, v_k_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___boxed(lean_object* v_motive__2_289_, lean_object* v_ctorIdx_290_, lean_object* v_t_291_, lean_object* v_h_292_, lean_object* v_k_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim(v_motive__2_289_, v_ctorIdx_290_, v_t_291_, v_h_292_, v_k_293_);
lean_dec(v_ctorIdx_290_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_core_elim___redArg(lean_object* v_t_295_, lean_object* v_core_296_){
_start:
{
lean_object* v___x_297_; 
v___x_297_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_295_, v_core_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_core_elim(lean_object* v_motive__2_298_, lean_object* v_t_299_, lean_object* v_h_300_, lean_object* v_core_301_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_299_, v_core_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_coreCommRing_elim___redArg(lean_object* v_t_303_, lean_object* v_coreCommRing_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_303_, v_coreCommRing_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_coreCommRing_elim(lean_object* v_motive__2_306_, lean_object* v_t_307_, lean_object* v_h_308_, lean_object* v_coreCommRing_309_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_307_, v_coreCommRing_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_coreOfNat_elim___redArg(lean_object* v_t_311_, lean_object* v_coreOfNat_312_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_311_, v_coreOfNat_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_coreOfNat_elim(lean_object* v_motive__2_314_, lean_object* v_t_315_, lean_object* v_h_316_, lean_object* v_coreOfNat_317_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_315_, v_coreOfNat_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_neg_elim___redArg(lean_object* v_t_319_, lean_object* v_neg_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_319_, v_neg_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_neg_elim(lean_object* v_motive__2_322_, lean_object* v_t_323_, lean_object* v_h_324_, lean_object* v_neg_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_323_, v_neg_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_coeff_elim___redArg(lean_object* v_t_327_, lean_object* v_coeff_328_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_327_, v_coeff_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_coeff_elim(lean_object* v_motive__2_330_, lean_object* v_t_331_, lean_object* v_h_332_, lean_object* v_coeff_333_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_331_, v_coeff_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_subst_elim___redArg(lean_object* v_t_335_, lean_object* v_subst_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_335_, v_subst_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_subst_elim(lean_object* v_motive__2_338_, lean_object* v_t_339_, lean_object* v_h_340_, lean_object* v_subst_341_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_Lean_Meta_Grind_Arith_Linear_EqCnstrProof_ctorElim___redArg(v_t_339_, v_subst_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorIdx(lean_object* v_x_343_){
_start:
{
switch(lean_obj_tag(v_x_343_))
{
case 0:
{
lean_object* v___x_344_; 
v___x_344_ = lean_unsigned_to_nat(0u);
return v___x_344_;
}
case 1:
{
lean_object* v___x_345_; 
v___x_345_ = lean_unsigned_to_nat(1u);
return v___x_345_;
}
case 2:
{
lean_object* v___x_346_; 
v___x_346_ = lean_unsigned_to_nat(2u);
return v___x_346_;
}
case 3:
{
lean_object* v___x_347_; 
v___x_347_ = lean_unsigned_to_nat(3u);
return v___x_347_;
}
case 4:
{
lean_object* v___x_348_; 
v___x_348_ = lean_unsigned_to_nat(4u);
return v___x_348_;
}
case 5:
{
lean_object* v___x_349_; 
v___x_349_ = lean_unsigned_to_nat(5u);
return v___x_349_;
}
case 6:
{
lean_object* v___x_350_; 
v___x_350_ = lean_unsigned_to_nat(6u);
return v___x_350_;
}
case 7:
{
lean_object* v___x_351_; 
v___x_351_ = lean_unsigned_to_nat(7u);
return v___x_351_;
}
case 8:
{
lean_object* v___x_352_; 
v___x_352_ = lean_unsigned_to_nat(8u);
return v___x_352_;
}
case 9:
{
lean_object* v___x_353_; 
v___x_353_ = lean_unsigned_to_nat(9u);
return v___x_353_;
}
case 10:
{
lean_object* v___x_354_; 
v___x_354_ = lean_unsigned_to_nat(10u);
return v___x_354_;
}
case 11:
{
lean_object* v___x_355_; 
v___x_355_ = lean_unsigned_to_nat(11u);
return v___x_355_;
}
case 12:
{
lean_object* v___x_356_; 
v___x_356_ = lean_unsigned_to_nat(12u);
return v___x_356_;
}
default: 
{
lean_object* v___x_357_; 
v___x_357_ = lean_unsigned_to_nat(13u);
return v___x_357_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorIdx___boxed(lean_object* v_x_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorIdx(v_x_358_);
lean_dec(v_x_358_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(lean_object* v_t_360_, lean_object* v_k_361_){
_start:
{
switch(lean_obj_tag(v_t_360_))
{
case 0:
{
lean_object* v_e_362_; lean_object* v_lhs_363_; lean_object* v_rhs_364_; lean_object* v___x_365_; 
v_e_362_ = lean_ctor_get(v_t_360_, 0);
lean_inc_ref(v_e_362_);
v_lhs_363_ = lean_ctor_get(v_t_360_, 1);
lean_inc(v_lhs_363_);
v_rhs_364_ = lean_ctor_get(v_t_360_, 2);
lean_inc(v_rhs_364_);
lean_dec_ref(v_t_360_);
v___x_365_ = lean_apply_3(v_k_361_, v_e_362_, v_lhs_363_, v_rhs_364_);
return v___x_365_;
}
case 1:
{
lean_object* v_e_366_; lean_object* v_lhs_367_; lean_object* v_rhs_368_; lean_object* v___x_369_; 
v_e_366_ = lean_ctor_get(v_t_360_, 0);
lean_inc_ref(v_e_366_);
v_lhs_367_ = lean_ctor_get(v_t_360_, 1);
lean_inc(v_lhs_367_);
v_rhs_368_ = lean_ctor_get(v_t_360_, 2);
lean_inc(v_rhs_368_);
lean_dec_ref(v_t_360_);
v___x_369_ = lean_apply_3(v_k_361_, v_e_366_, v_lhs_367_, v_rhs_368_);
return v___x_369_;
}
case 3:
{
lean_object* v_e_370_; lean_object* v_natStructId_371_; lean_object* v_lhs_372_; lean_object* v_rhs_373_; lean_object* v___x_374_; 
v_e_370_ = lean_ctor_get(v_t_360_, 0);
lean_inc_ref(v_e_370_);
v_natStructId_371_ = lean_ctor_get(v_t_360_, 1);
lean_inc(v_natStructId_371_);
v_lhs_372_ = lean_ctor_get(v_t_360_, 2);
lean_inc(v_lhs_372_);
v_rhs_373_ = lean_ctor_get(v_t_360_, 3);
lean_inc(v_rhs_373_);
lean_dec_ref(v_t_360_);
v___x_374_ = lean_apply_4(v_k_361_, v_e_370_, v_natStructId_371_, v_lhs_372_, v_rhs_373_);
return v___x_374_;
}
case 4:
{
lean_object* v_e_375_; lean_object* v_natStructId_376_; lean_object* v_lhs_377_; lean_object* v_rhs_378_; lean_object* v___x_379_; 
v_e_375_ = lean_ctor_get(v_t_360_, 0);
lean_inc_ref(v_e_375_);
v_natStructId_376_ = lean_ctor_get(v_t_360_, 1);
lean_inc(v_natStructId_376_);
v_lhs_377_ = lean_ctor_get(v_t_360_, 2);
lean_inc(v_lhs_377_);
v_rhs_378_ = lean_ctor_get(v_t_360_, 3);
lean_inc(v_rhs_378_);
lean_dec_ref(v_t_360_);
v___x_379_ = lean_apply_4(v_k_361_, v_e_375_, v_natStructId_376_, v_lhs_377_, v_rhs_378_);
return v___x_379_;
}
case 5:
{
lean_object* v_c_u2081_380_; lean_object* v_c_u2082_381_; lean_object* v___x_382_; 
v_c_u2081_380_ = lean_ctor_get(v_t_360_, 0);
lean_inc_ref(v_c_u2081_380_);
v_c_u2082_381_ = lean_ctor_get(v_t_360_, 1);
lean_inc_ref(v_c_u2082_381_);
lean_dec_ref(v_t_360_);
v___x_382_ = lean_apply_2(v_k_361_, v_c_u2081_380_, v_c_u2082_381_);
return v___x_382_;
}
case 7:
{
lean_object* v_h_383_; lean_object* v___x_384_; 
v_h_383_ = lean_ctor_get(v_t_360_, 0);
lean_inc(v_h_383_);
lean_dec_ref(v_t_360_);
v___x_384_ = lean_apply_1(v_k_361_, v_h_383_);
return v___x_384_;
}
case 8:
{
lean_object* v_c_u2081_385_; lean_object* v_decVar_386_; lean_object* v_h_387_; lean_object* v_decVars_388_; lean_object* v___x_389_; 
v_c_u2081_385_ = lean_ctor_get(v_t_360_, 0);
lean_inc_ref(v_c_u2081_385_);
v_decVar_386_ = lean_ctor_get(v_t_360_, 1);
lean_inc(v_decVar_386_);
v_h_387_ = lean_ctor_get(v_t_360_, 2);
lean_inc_ref(v_h_387_);
v_decVars_388_ = lean_ctor_get(v_t_360_, 3);
lean_inc_ref(v_decVars_388_);
lean_dec_ref(v_t_360_);
v___x_389_ = lean_apply_4(v_k_361_, v_c_u2081_385_, v_decVar_386_, v_h_387_, v_decVars_388_);
return v___x_389_;
}
case 9:
{
return v_k_361_;
}
case 10:
{
lean_object* v_a_390_; lean_object* v_b_391_; lean_object* v_la_392_; lean_object* v_lb_393_; lean_object* v___x_394_; 
v_a_390_ = lean_ctor_get(v_t_360_, 0);
lean_inc_ref(v_a_390_);
v_b_391_ = lean_ctor_get(v_t_360_, 1);
lean_inc_ref(v_b_391_);
v_la_392_ = lean_ctor_get(v_t_360_, 2);
lean_inc(v_la_392_);
v_lb_393_ = lean_ctor_get(v_t_360_, 3);
lean_inc(v_lb_393_);
lean_dec_ref(v_t_360_);
v___x_394_ = lean_apply_4(v_k_361_, v_a_390_, v_b_391_, v_la_392_, v_lb_393_);
return v___x_394_;
}
case 11:
{
lean_object* v_a_395_; lean_object* v_b_396_; lean_object* v_natStructId_397_; lean_object* v_la_398_; lean_object* v_lb_399_; lean_object* v___x_400_; 
v_a_395_ = lean_ctor_get(v_t_360_, 0);
lean_inc_ref(v_a_395_);
v_b_396_ = lean_ctor_get(v_t_360_, 1);
lean_inc_ref(v_b_396_);
v_natStructId_397_ = lean_ctor_get(v_t_360_, 2);
lean_inc(v_natStructId_397_);
v_la_398_ = lean_ctor_get(v_t_360_, 3);
lean_inc(v_la_398_);
v_lb_399_ = lean_ctor_get(v_t_360_, 4);
lean_inc(v_lb_399_);
lean_dec_ref(v_t_360_);
v___x_400_ = lean_apply_5(v_k_361_, v_a_395_, v_b_396_, v_natStructId_397_, v_la_398_, v_lb_399_);
return v___x_400_;
}
case 13:
{
lean_object* v_x_401_; lean_object* v_c_u2081_402_; lean_object* v_c_u2082_403_; lean_object* v___x_404_; 
v_x_401_ = lean_ctor_get(v_t_360_, 0);
lean_inc(v_x_401_);
v_c_u2081_402_ = lean_ctor_get(v_t_360_, 1);
lean_inc_ref(v_c_u2081_402_);
v_c_u2082_403_ = lean_ctor_get(v_t_360_, 2);
lean_inc_ref(v_c_u2082_403_);
lean_dec_ref(v_t_360_);
v___x_404_ = lean_apply_3(v_k_361_, v_x_401_, v_c_u2081_402_, v_c_u2082_403_);
return v___x_404_;
}
default: 
{
lean_object* v_c_405_; lean_object* v_lhs_406_; lean_object* v___x_407_; 
v_c_405_ = lean_ctor_get(v_t_360_, 0);
lean_inc_ref(v_c_405_);
v_lhs_406_ = lean_ctor_get(v_t_360_, 1);
lean_inc(v_lhs_406_);
lean_dec(v_t_360_);
v___x_407_ = lean_apply_2(v_k_361_, v_c_405_, v_lhs_406_);
return v___x_407_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim(lean_object* v_motive__4_408_, lean_object* v_ctorIdx_409_, lean_object* v_t_410_, lean_object* v_h_411_, lean_object* v_k_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_410_, v_k_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___boxed(lean_object* v_motive__4_414_, lean_object* v_ctorIdx_415_, lean_object* v_t_416_, lean_object* v_h_417_, lean_object* v_k_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim(v_motive__4_414_, v_ctorIdx_415_, v_t_416_, v_h_417_, v_k_418_);
lean_dec(v_ctorIdx_415_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_core_elim___redArg(lean_object* v_t_420_, lean_object* v_core_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_420_, v_core_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_core_elim(lean_object* v_motive__4_423_, lean_object* v_t_424_, lean_object* v_h_425_, lean_object* v_core_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_424_, v_core_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_notCore_elim___redArg(lean_object* v_t_428_, lean_object* v_notCore_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_428_, v_notCore_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_notCore_elim(lean_object* v_motive__4_431_, lean_object* v_t_432_, lean_object* v_h_433_, lean_object* v_notCore_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_432_, v_notCore_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ring_elim___redArg(lean_object* v_t_436_, lean_object* v_ring_437_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_436_, v_ring_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ring_elim(lean_object* v_motive__4_439_, lean_object* v_t_440_, lean_object* v_h_441_, lean_object* v_ring_442_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_440_, v_ring_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_coreOfNat_elim___redArg(lean_object* v_t_444_, lean_object* v_coreOfNat_445_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_444_, v_coreOfNat_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_coreOfNat_elim(lean_object* v_motive__4_447_, lean_object* v_t_448_, lean_object* v_h_449_, lean_object* v_coreOfNat_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_448_, v_coreOfNat_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_notCoreOfNat_elim___redArg(lean_object* v_t_452_, lean_object* v_notCoreOfNat_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_452_, v_notCoreOfNat_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_notCoreOfNat_elim(lean_object* v_motive__4_455_, lean_object* v_t_456_, lean_object* v_h_457_, lean_object* v_notCoreOfNat_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_456_, v_notCoreOfNat_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_combine_elim___redArg(lean_object* v_t_460_, lean_object* v_combine_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_460_, v_combine_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_combine_elim(lean_object* v_motive__4_463_, lean_object* v_t_464_, lean_object* v_h_465_, lean_object* v_combine_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_464_, v_combine_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_norm_elim___redArg(lean_object* v_t_468_, lean_object* v_norm_469_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_468_, v_norm_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_norm_elim(lean_object* v_motive__4_471_, lean_object* v_t_472_, lean_object* v_h_473_, lean_object* v_norm_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_472_, v_norm_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_dec_elim___redArg(lean_object* v_t_476_, lean_object* v_dec_477_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_476_, v_dec_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_dec_elim(lean_object* v_motive__4_479_, lean_object* v_t_480_, lean_object* v_h_481_, lean_object* v_dec_482_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_480_, v_dec_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ofDiseqSplit_elim___redArg(lean_object* v_t_484_, lean_object* v_ofDiseqSplit_485_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_484_, v_ofDiseqSplit_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ofDiseqSplit_elim(lean_object* v_motive__4_487_, lean_object* v_t_488_, lean_object* v_h_489_, lean_object* v_ofDiseqSplit_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_488_, v_ofDiseqSplit_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_oneGtZero_elim___redArg(lean_object* v_t_492_, lean_object* v_oneGtZero_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_492_, v_oneGtZero_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_oneGtZero_elim(lean_object* v_motive__4_495_, lean_object* v_t_496_, lean_object* v_h_497_, lean_object* v_oneGtZero_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_496_, v_oneGtZero_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ofEq_elim___redArg(lean_object* v_t_500_, lean_object* v_ofEq_501_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_500_, v_ofEq_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ofEq_elim(lean_object* v_motive__4_503_, lean_object* v_t_504_, lean_object* v_h_505_, lean_object* v_ofEq_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_504_, v_ofEq_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ofEqOfNat_elim___redArg(lean_object* v_t_508_, lean_object* v_ofEqOfNat_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_508_, v_ofEqOfNat_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ofEqOfNat_elim(lean_object* v_motive__4_511_, lean_object* v_t_512_, lean_object* v_h_513_, lean_object* v_ofEqOfNat_514_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_512_, v_ofEqOfNat_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ringEq_elim___redArg(lean_object* v_t_516_, lean_object* v_ringEq_517_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_516_, v_ringEq_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ringEq_elim(lean_object* v_motive__4_519_, lean_object* v_t_520_, lean_object* v_h_521_, lean_object* v_ringEq_522_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_520_, v_ringEq_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_subst_elim___redArg(lean_object* v_t_524_, lean_object* v_subst_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_524_, v_subst_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_subst_elim(lean_object* v_motive__4_527_, lean_object* v_t_528_, lean_object* v_h_529_, lean_object* v_subst_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstrProof_ctorElim___redArg(v_t_528_, v_subst_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorIdx(lean_object* v_x_532_){
_start:
{
switch(lean_obj_tag(v_x_532_))
{
case 0:
{
lean_object* v___x_533_; 
v___x_533_ = lean_unsigned_to_nat(0u);
return v___x_533_;
}
case 1:
{
lean_object* v___x_534_; 
v___x_534_ = lean_unsigned_to_nat(1u);
return v___x_534_;
}
case 2:
{
lean_object* v___x_535_; 
v___x_535_ = lean_unsigned_to_nat(2u);
return v___x_535_;
}
case 3:
{
lean_object* v___x_536_; 
v___x_536_ = lean_unsigned_to_nat(3u);
return v___x_536_;
}
case 4:
{
lean_object* v___x_537_; 
v___x_537_ = lean_unsigned_to_nat(4u);
return v___x_537_;
}
case 5:
{
lean_object* v___x_538_; 
v___x_538_ = lean_unsigned_to_nat(5u);
return v___x_538_;
}
default: 
{
lean_object* v___x_539_; 
v___x_539_ = lean_unsigned_to_nat(6u);
return v___x_539_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorIdx___boxed(lean_object* v_x_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorIdx(v_x_540_);
lean_dec(v_x_540_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(lean_object* v_t_542_, lean_object* v_k_543_){
_start:
{
switch(lean_obj_tag(v_t_542_))
{
case 0:
{
lean_object* v_a_544_; lean_object* v_b_545_; lean_object* v_lhs_546_; lean_object* v_rhs_547_; lean_object* v___x_548_; 
v_a_544_ = lean_ctor_get(v_t_542_, 0);
lean_inc_ref(v_a_544_);
v_b_545_ = lean_ctor_get(v_t_542_, 1);
lean_inc_ref(v_b_545_);
v_lhs_546_ = lean_ctor_get(v_t_542_, 2);
lean_inc(v_lhs_546_);
v_rhs_547_ = lean_ctor_get(v_t_542_, 3);
lean_inc(v_rhs_547_);
lean_dec_ref(v_t_542_);
v___x_548_ = lean_apply_4(v_k_543_, v_a_544_, v_b_545_, v_lhs_546_, v_rhs_547_);
return v___x_548_;
}
case 1:
{
lean_object* v_c_549_; lean_object* v_lhs_550_; lean_object* v___x_551_; 
v_c_549_ = lean_ctor_get(v_t_542_, 0);
lean_inc_ref(v_c_549_);
v_lhs_550_ = lean_ctor_get(v_t_542_, 1);
lean_inc(v_lhs_550_);
lean_dec_ref(v_t_542_);
v___x_551_ = lean_apply_2(v_k_543_, v_c_549_, v_lhs_550_);
return v___x_551_;
}
case 2:
{
lean_object* v_a_552_; lean_object* v_b_553_; lean_object* v_natStructId_554_; lean_object* v_lhs_555_; lean_object* v_rhs_556_; lean_object* v___x_557_; 
v_a_552_ = lean_ctor_get(v_t_542_, 0);
lean_inc_ref(v_a_552_);
v_b_553_ = lean_ctor_get(v_t_542_, 1);
lean_inc_ref(v_b_553_);
v_natStructId_554_ = lean_ctor_get(v_t_542_, 2);
lean_inc(v_natStructId_554_);
v_lhs_555_ = lean_ctor_get(v_t_542_, 3);
lean_inc(v_lhs_555_);
v_rhs_556_ = lean_ctor_get(v_t_542_, 4);
lean_inc(v_rhs_556_);
lean_dec_ref(v_t_542_);
v___x_557_ = lean_apply_5(v_k_543_, v_a_552_, v_b_553_, v_natStructId_554_, v_lhs_555_, v_rhs_556_);
return v___x_557_;
}
case 3:
{
lean_object* v_c_558_; lean_object* v___x_559_; 
v_c_558_ = lean_ctor_get(v_t_542_, 0);
lean_inc_ref(v_c_558_);
lean_dec_ref(v_t_542_);
v___x_559_ = lean_apply_1(v_k_543_, v_c_558_);
return v___x_559_;
}
case 4:
{
lean_object* v_k_u2081_560_; lean_object* v_k_u2082_561_; lean_object* v_c_u2081_562_; lean_object* v_c_u2082_563_; lean_object* v___x_564_; 
v_k_u2081_560_ = lean_ctor_get(v_t_542_, 0);
lean_inc(v_k_u2081_560_);
v_k_u2082_561_ = lean_ctor_get(v_t_542_, 1);
lean_inc(v_k_u2082_561_);
v_c_u2081_562_ = lean_ctor_get(v_t_542_, 2);
lean_inc_ref(v_c_u2081_562_);
v_c_u2082_563_ = lean_ctor_get(v_t_542_, 3);
lean_inc_ref(v_c_u2082_563_);
lean_dec_ref(v_t_542_);
v___x_564_ = lean_apply_4(v_k_543_, v_k_u2081_560_, v_k_u2082_561_, v_c_u2081_562_, v_c_u2082_563_);
return v___x_564_;
}
case 5:
{
lean_object* v_k_565_; lean_object* v_c_u2081_566_; lean_object* v_c_u2082_567_; lean_object* v___x_568_; 
v_k_565_ = lean_ctor_get(v_t_542_, 0);
lean_inc(v_k_565_);
v_c_u2081_566_ = lean_ctor_get(v_t_542_, 1);
lean_inc_ref(v_c_u2081_566_);
v_c_u2082_567_ = lean_ctor_get(v_t_542_, 2);
lean_inc_ref(v_c_u2082_567_);
lean_dec_ref(v_t_542_);
v___x_568_ = lean_apply_3(v_k_543_, v_k_565_, v_c_u2081_566_, v_c_u2082_567_);
return v___x_568_;
}
default: 
{
return v_k_543_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim(lean_object* v_motive__6_569_, lean_object* v_ctorIdx_570_, lean_object* v_t_571_, lean_object* v_h_572_, lean_object* v_k_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_571_, v_k_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___boxed(lean_object* v_motive__6_575_, lean_object* v_ctorIdx_576_, lean_object* v_t_577_, lean_object* v_h_578_, lean_object* v_k_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim(v_motive__6_575_, v_ctorIdx_576_, v_t_577_, v_h_578_, v_k_579_);
lean_dec(v_ctorIdx_576_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_core_elim___redArg(lean_object* v_t_581_, lean_object* v_core_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_581_, v_core_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_core_elim(lean_object* v_motive__6_584_, lean_object* v_t_585_, lean_object* v_h_586_, lean_object* v_core_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_585_, v_core_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ring_elim___redArg(lean_object* v_t_589_, lean_object* v_ring_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_589_, v_ring_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ring_elim(lean_object* v_motive__6_592_, lean_object* v_t_593_, lean_object* v_h_594_, lean_object* v_ring_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_593_, v_ring_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_coreOfNat_elim___redArg(lean_object* v_t_597_, lean_object* v_coreOfNat_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_597_, v_coreOfNat_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_coreOfNat_elim(lean_object* v_motive__6_600_, lean_object* v_t_601_, lean_object* v_h_602_, lean_object* v_coreOfNat_603_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_601_, v_coreOfNat_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_neg_elim___redArg(lean_object* v_t_605_, lean_object* v_neg_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_605_, v_neg_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_neg_elim(lean_object* v_motive__6_608_, lean_object* v_t_609_, lean_object* v_h_610_, lean_object* v_neg_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_609_, v_neg_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_subst_elim___redArg(lean_object* v_t_613_, lean_object* v_subst_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_613_, v_subst_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_subst_elim(lean_object* v_motive__6_616_, lean_object* v_t_617_, lean_object* v_h_618_, lean_object* v_subst_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_617_, v_subst_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_subst1_elim___redArg(lean_object* v_t_621_, lean_object* v_subst1_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_621_, v_subst1_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_subst1_elim(lean_object* v_motive__6_624_, lean_object* v_t_625_, lean_object* v_h_626_, lean_object* v_subst1_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_625_, v_subst1_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_oneNeZero_elim___redArg(lean_object* v_t_629_, lean_object* v_oneNeZero_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_629_, v_oneNeZero_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_oneNeZero_elim(lean_object* v_motive__6_632_, lean_object* v_t_633_, lean_object* v_h_634_, lean_object* v_oneNeZero_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstrProof_ctorElim___redArg(v_t_633_, v_oneNeZero_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorIdx(lean_object* v_x_637_){
_start:
{
if (lean_obj_tag(v_x_637_) == 0)
{
lean_object* v___x_638_; 
v___x_638_ = lean_unsigned_to_nat(0u);
return v___x_638_;
}
else
{
lean_object* v___x_639_; 
v___x_639_ = lean_unsigned_to_nat(1u);
return v___x_639_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorIdx___boxed(lean_object* v_x_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorIdx(v_x_640_);
lean_dec_ref(v_x_640_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorElim___redArg(lean_object* v_t_642_, lean_object* v_k_643_){
_start:
{
lean_object* v_c_644_; lean_object* v___x_645_; 
v_c_644_ = lean_ctor_get(v_t_642_, 0);
lean_inc_ref(v_c_644_);
lean_dec_ref(v_t_642_);
v___x_645_ = lean_apply_1(v_k_643_, v_c_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorElim(lean_object* v_motive__7_646_, lean_object* v_ctorIdx_647_, lean_object* v_t_648_, lean_object* v_h_649_, lean_object* v_k_650_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorElim___redArg(v_t_648_, v_k_650_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorElim___boxed(lean_object* v_motive__7_652_, lean_object* v_ctorIdx_653_, lean_object* v_t_654_, lean_object* v_h_655_, lean_object* v_k_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorElim(v_motive__7_652_, v_ctorIdx_653_, v_t_654_, v_h_655_, v_k_656_);
lean_dec(v_ctorIdx_653_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_diseq_elim___redArg(lean_object* v_t_658_, lean_object* v_diseq_659_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorElim___redArg(v_t_658_, v_diseq_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_diseq_elim(lean_object* v_motive__7_661_, lean_object* v_t_662_, lean_object* v_h_663_, lean_object* v_diseq_664_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorElim___redArg(v_t_662_, v_diseq_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_lt_elim___redArg(lean_object* v_t_666_, lean_object* v_lt_667_){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorElim___redArg(v_t_666_, v_lt_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_UnsatProof_lt_elim(lean_object* v_motive__7_669_, lean_object* v_t_670_, lean_object* v_h_671_, lean_object* v_lt_672_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l_Lean_Meta_Grind_Arith_Linear_UnsatProof_ctorElim___redArg(v_t_670_, v_lt_672_);
return v___x_673_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_677_ = lean_box(0);
v___x_678_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__1));
v___x_679_ = l_Lean_Expr_const___override(v___x_678_, v___x_677_);
return v___x_679_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__3(void){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_680_ = lean_box(0);
v___x_681_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2);
v___x_682_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
lean_ctor_set(v___x_682_, 2, v___x_680_);
lean_ctor_set(v___x_682_, 3, v___x_680_);
return v___x_682_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__4(void){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_683_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__3, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__3);
v___x_684_ = lean_box(0);
v___x_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_685_, 0, v___x_684_);
lean_ctor_set(v___x_685_, 1, v___x_683_);
return v___x_685_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr(void){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__4, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__4);
return v___x_686_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__0(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_687_ = lean_box(0);
v___x_688_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2);
v___x_689_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
lean_ctor_set(v___x_689_, 2, v___x_687_);
lean_ctor_set(v___x_689_, 3, v___x_687_);
return v___x_689_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__1(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_690_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__0, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__0);
v___x_691_ = lean_box(0);
v___x_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
lean_ctor_set(v___x_692_, 1, v___x_690_);
return v___x_692_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr(void){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__1, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedEqCnstr___closed__1);
return v___x_693_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__0(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_694_ = lean_unsigned_to_nat(32u);
v___x_695_ = lean_mk_empty_array_with_capacity(v___x_694_);
v___x_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
return v___x_696_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__1(void){
_start:
{
size_t v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_697_ = ((size_t)5ULL);
v___x_698_ = lean_unsigned_to_nat(0u);
v___x_699_ = lean_unsigned_to_nat(32u);
v___x_700_ = lean_mk_empty_array_with_capacity(v___x_699_);
v___x_701_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__0, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__0);
v___x_702_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_702_, 0, v___x_701_);
lean_ctor_set(v___x_702_, 1, v___x_700_);
lean_ctor_set(v___x_702_, 2, v___x_698_);
lean_ctor_set(v___x_702_, 3, v___x_698_);
lean_ctor_set_usize(v___x_702_, 4, v___x_697_);
return v___x_702_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__2(void){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_703_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__3(void){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__2, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__2);
v___x_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
return v___x_705_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__4(void){
_start:
{
lean_object* v___x_706_; uint8_t v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_706_ = lean_box(0);
v___x_707_ = 0;
v___x_708_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__3, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__3);
v___x_709_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__1, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__1);
v___x_710_ = lean_box(0);
v___x_711_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedDiseqCnstr___closed__2);
v___x_712_ = lean_box(0);
v___x_713_ = lean_unsigned_to_nat(0u);
v___x_714_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v___x_714_, 0, v___x_713_);
lean_ctor_set(v___x_714_, 1, v___x_712_);
lean_ctor_set(v___x_714_, 2, v___x_711_);
lean_ctor_set(v___x_714_, 3, v___x_710_);
lean_ctor_set(v___x_714_, 4, v___x_711_);
lean_ctor_set(v___x_714_, 5, v___x_712_);
lean_ctor_set(v___x_714_, 6, v___x_712_);
lean_ctor_set(v___x_714_, 7, v___x_712_);
lean_ctor_set(v___x_714_, 8, v___x_712_);
lean_ctor_set(v___x_714_, 9, v___x_712_);
lean_ctor_set(v___x_714_, 10, v___x_712_);
lean_ctor_set(v___x_714_, 11, v___x_712_);
lean_ctor_set(v___x_714_, 12, v___x_712_);
lean_ctor_set(v___x_714_, 13, v___x_712_);
lean_ctor_set(v___x_714_, 14, v___x_712_);
lean_ctor_set(v___x_714_, 15, v___x_712_);
lean_ctor_set(v___x_714_, 16, v___x_712_);
lean_ctor_set(v___x_714_, 17, v___x_711_);
lean_ctor_set(v___x_714_, 18, v___x_711_);
lean_ctor_set(v___x_714_, 19, v___x_712_);
lean_ctor_set(v___x_714_, 20, v___x_712_);
lean_ctor_set(v___x_714_, 21, v___x_712_);
lean_ctor_set(v___x_714_, 22, v___x_711_);
lean_ctor_set(v___x_714_, 23, v___x_711_);
lean_ctor_set(v___x_714_, 24, v___x_711_);
lean_ctor_set(v___x_714_, 25, v___x_712_);
lean_ctor_set(v___x_714_, 26, v___x_712_);
lean_ctor_set(v___x_714_, 27, v___x_712_);
lean_ctor_set(v___x_714_, 28, v___x_711_);
lean_ctor_set(v___x_714_, 29, v___x_711_);
lean_ctor_set(v___x_714_, 30, v___x_709_);
lean_ctor_set(v___x_714_, 31, v___x_708_);
lean_ctor_set(v___x_714_, 32, v___x_709_);
lean_ctor_set(v___x_714_, 33, v___x_709_);
lean_ctor_set(v___x_714_, 34, v___x_709_);
lean_ctor_set(v___x_714_, 35, v___x_709_);
lean_ctor_set(v___x_714_, 36, v___x_712_);
lean_ctor_set(v___x_714_, 37, v___x_708_);
lean_ctor_set(v___x_714_, 38, v___x_709_);
lean_ctor_set(v___x_714_, 39, v___x_706_);
lean_ctor_set(v___x_714_, 40, v___x_709_);
lean_ctor_set(v___x_714_, 41, v___x_709_);
lean_ctor_set_uint8(v___x_714_, sizeof(void*)*42, v___x_707_);
return v___x_714_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default(void){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__4, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default___closed__4);
return v___x_715_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct(void){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default;
return v___x_716_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_717_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__1(void){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__0);
v___x_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0(lean_object* v_00_u03b2_720_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0___closed__1);
return v___x_721_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__1(void){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_724_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__2(void){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_725_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__1, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__1);
v___x_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
return v___x_726_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__3(void){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_727_ = lean_unsigned_to_nat(32u);
v___x_728_ = lean_mk_empty_array_with_capacity(v___x_727_);
v___x_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
return v___x_729_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__4(void){
_start:
{
size_t v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_730_ = ((size_t)5ULL);
v___x_731_ = lean_unsigned_to_nat(0u);
v___x_732_ = lean_unsigned_to_nat(32u);
v___x_733_ = lean_mk_empty_array_with_capacity(v___x_732_);
v___x_734_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__3, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__3);
v___x_735_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_735_, 0, v___x_734_);
lean_ctor_set(v___x_735_, 1, v___x_733_);
lean_ctor_set(v___x_735_, 2, v___x_731_);
lean_ctor_set(v___x_735_, 3, v___x_731_);
lean_ctor_set_usize(v___x_735_, 4, v___x_730_);
return v___x_735_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__5(void){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Linear_instInhabitedState_default_spec__0(lean_box(0));
return v___x_736_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__6(void){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_737_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__5, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__5);
v___x_738_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__4, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__4);
v___x_739_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__2, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__2);
v___x_740_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__0));
v___x_741_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
lean_ctor_set(v___x_741_, 1, v___x_739_);
lean_ctor_set(v___x_741_, 2, v___x_739_);
lean_ctor_set(v___x_741_, 3, v___x_738_);
lean_ctor_set(v___x_741_, 4, v___x_737_);
lean_ctor_set(v___x_741_, 5, v___x_740_);
lean_ctor_set(v___x_741_, 6, v___x_739_);
lean_ctor_set(v___x_741_, 7, v___x_739_);
return v___x_741_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default(void){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__6, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__6);
return v___x_742_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState(void){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default;
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2_(lean_object* v___x_744_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_746_, 0, v___x_744_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2____boxed(lean_object* v___x_747_, lean_object* v___y_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2_(v___x_747_);
return v_res_749_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_750_; lean_object* v___f_751_; 
v___x_750_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__6, &l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedState_default___closed__6);
v___f_751_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_751_, 0, v___x_750_);
return v___f_751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_753_; lean_object* v___x_754_; 
v___f_753_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2_);
v___x_754_ = l_Lean_Meta_Grind_registerSolverExtension___redArg(v___f_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2____boxed(lean_object* v_a_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Types_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_Types_874591972____hygCtx___hyg_2_();
return v_res_756_;
}
}
lean_object* runtime_initialize_Init_Grind_Ring_CommSolver(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ordered_Linarith(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
