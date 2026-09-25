// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.Types
// Imports: public import Init.Grind.Ring.CommSemiringAdapter public import Lean.Meta.Tactic.Grind.Types public import Lean.Meta.Sym.Arith.Types import Lean.Meta.Sym.Arith.Poly
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_rightpad___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerSolverExtension___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_getState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
extern lean_object* l_Lean_Grind_CommRing_instInhabitedExpr_default;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Grind_CommRing_instInhabitedPoly_default;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_degree(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_core_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_core_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_coreS_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_coreS_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_superpose_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_superpose_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_simp_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_simp_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_mul_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_mul_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_div_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_div_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_gcd_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_gcd_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_numEq0_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_numEq0_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__2;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstr___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstr;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_input_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_input_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_step_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_step_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_normEq0_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_normEq0_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_p(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_p___boxed(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__1;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__2;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__3;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__1;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState;
static const lean_array_object l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_ringExt;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_get_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_get_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_modify_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_modify_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_modify_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_modify_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_padAndModify___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_padAndModify___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_padAndModify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_padAndModify___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_State_getRing___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_getRing___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_getRing(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_getRing___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_modifyRing(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_modifyRing___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_getSemiring(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_getSemiring___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_modifySemiring(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_modifySemiring___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_getNCRing(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_getNCRing___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_modifyNCRing(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_modifyNCRing___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_getNCSemiring(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_getNCSemiring___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_modifyNCSemiring(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_modifyNCSemiring___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
case 3:
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
case 4:
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(4u);
return v___x_6_;
}
case 5:
{
lean_object* v___x_7_; 
v___x_7_ = lean_unsigned_to_nat(5u);
return v___x_7_;
}
case 6:
{
lean_object* v___x_8_; 
v___x_8_ = lean_unsigned_to_nat(6u);
return v___x_8_;
}
default: 
{
lean_object* v___x_9_; 
v___x_9_ = lean_unsigned_to_nat(7u);
return v___x_9_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorIdx___boxed(lean_object* v_x_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorIdx(v_x_10_);
lean_dec_ref(v_x_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(lean_object* v_t_12_, lean_object* v_k_13_){
_start:
{
switch(lean_obj_tag(v_t_12_))
{
case 0:
{
lean_object* v_a_14_; lean_object* v_b_15_; lean_object* v_ra_16_; lean_object* v_rb_17_; lean_object* v___x_18_; 
v_a_14_ = lean_ctor_get(v_t_12_, 0);
lean_inc_ref(v_a_14_);
v_b_15_ = lean_ctor_get(v_t_12_, 1);
lean_inc_ref(v_b_15_);
v_ra_16_ = lean_ctor_get(v_t_12_, 2);
lean_inc_ref(v_ra_16_);
v_rb_17_ = lean_ctor_get(v_t_12_, 3);
lean_inc_ref(v_rb_17_);
lean_dec_ref_known(v_t_12_, 4);
v___x_18_ = lean_apply_4(v_k_13_, v_a_14_, v_b_15_, v_ra_16_, v_rb_17_);
return v___x_18_;
}
case 1:
{
lean_object* v_a_19_; lean_object* v_b_20_; lean_object* v_sa_21_; lean_object* v_sb_22_; lean_object* v_ra_23_; lean_object* v_rb_24_; lean_object* v___x_25_; 
v_a_19_ = lean_ctor_get(v_t_12_, 0);
lean_inc_ref(v_a_19_);
v_b_20_ = lean_ctor_get(v_t_12_, 1);
lean_inc_ref(v_b_20_);
v_sa_21_ = lean_ctor_get(v_t_12_, 2);
lean_inc_ref(v_sa_21_);
v_sb_22_ = lean_ctor_get(v_t_12_, 3);
lean_inc_ref(v_sb_22_);
v_ra_23_ = lean_ctor_get(v_t_12_, 4);
lean_inc_ref(v_ra_23_);
v_rb_24_ = lean_ctor_get(v_t_12_, 5);
lean_inc_ref(v_rb_24_);
lean_dec_ref_known(v_t_12_, 6);
v___x_25_ = lean_apply_6(v_k_13_, v_a_19_, v_b_20_, v_sa_21_, v_sb_22_, v_ra_23_, v_rb_24_);
return v___x_25_;
}
case 2:
{
lean_object* v_k_u2081_26_; lean_object* v_m_u2081_27_; lean_object* v_c_u2081_28_; lean_object* v_k_u2082_29_; lean_object* v_m_u2082_30_; lean_object* v_c_u2082_31_; lean_object* v___x_32_; 
v_k_u2081_26_ = lean_ctor_get(v_t_12_, 0);
lean_inc(v_k_u2081_26_);
v_m_u2081_27_ = lean_ctor_get(v_t_12_, 1);
lean_inc(v_m_u2081_27_);
v_c_u2081_28_ = lean_ctor_get(v_t_12_, 2);
lean_inc_ref(v_c_u2081_28_);
v_k_u2082_29_ = lean_ctor_get(v_t_12_, 3);
lean_inc(v_k_u2082_29_);
v_m_u2082_30_ = lean_ctor_get(v_t_12_, 4);
lean_inc(v_m_u2082_30_);
v_c_u2082_31_ = lean_ctor_get(v_t_12_, 5);
lean_inc_ref(v_c_u2082_31_);
lean_dec_ref_known(v_t_12_, 6);
v___x_32_ = lean_apply_6(v_k_13_, v_k_u2081_26_, v_m_u2081_27_, v_c_u2081_28_, v_k_u2082_29_, v_m_u2082_30_, v_c_u2082_31_);
return v___x_32_;
}
case 3:
{
lean_object* v_k_u2081_33_; lean_object* v_c_u2081_34_; lean_object* v_k_u2082_35_; lean_object* v_m_u2082_36_; lean_object* v_c_u2082_37_; lean_object* v___x_38_; 
v_k_u2081_33_ = lean_ctor_get(v_t_12_, 0);
lean_inc(v_k_u2081_33_);
v_c_u2081_34_ = lean_ctor_get(v_t_12_, 1);
lean_inc_ref(v_c_u2081_34_);
v_k_u2082_35_ = lean_ctor_get(v_t_12_, 2);
lean_inc(v_k_u2082_35_);
v_m_u2082_36_ = lean_ctor_get(v_t_12_, 3);
lean_inc(v_m_u2082_36_);
v_c_u2082_37_ = lean_ctor_get(v_t_12_, 4);
lean_inc_ref(v_c_u2082_37_);
lean_dec_ref_known(v_t_12_, 5);
v___x_38_ = lean_apply_5(v_k_13_, v_k_u2081_33_, v_c_u2081_34_, v_k_u2082_35_, v_m_u2082_36_, v_c_u2082_37_);
return v___x_38_;
}
case 6:
{
lean_object* v_a_39_; lean_object* v_b_40_; lean_object* v_c_u2081_41_; lean_object* v_c_u2082_42_; lean_object* v___x_43_; 
v_a_39_ = lean_ctor_get(v_t_12_, 0);
lean_inc(v_a_39_);
v_b_40_ = lean_ctor_get(v_t_12_, 1);
lean_inc(v_b_40_);
v_c_u2081_41_ = lean_ctor_get(v_t_12_, 2);
lean_inc_ref(v_c_u2081_41_);
v_c_u2082_42_ = lean_ctor_get(v_t_12_, 3);
lean_inc_ref(v_c_u2082_42_);
lean_dec_ref_known(v_t_12_, 4);
v___x_43_ = lean_apply_4(v_k_13_, v_a_39_, v_b_40_, v_c_u2081_41_, v_c_u2082_42_);
return v___x_43_;
}
case 7:
{
lean_object* v_k_44_; lean_object* v_c_u2081_45_; lean_object* v_c_u2082_46_; lean_object* v___x_47_; 
v_k_44_ = lean_ctor_get(v_t_12_, 0);
lean_inc(v_k_44_);
v_c_u2081_45_ = lean_ctor_get(v_t_12_, 1);
lean_inc_ref(v_c_u2081_45_);
v_c_u2082_46_ = lean_ctor_get(v_t_12_, 2);
lean_inc_ref(v_c_u2082_46_);
lean_dec_ref_known(v_t_12_, 3);
v___x_47_ = lean_apply_3(v_k_13_, v_k_44_, v_c_u2081_45_, v_c_u2082_46_);
return v___x_47_;
}
default: 
{
lean_object* v_k_48_; lean_object* v_e_49_; lean_object* v___x_50_; 
v_k_48_ = lean_ctor_get(v_t_12_, 0);
lean_inc(v_k_48_);
v_e_49_ = lean_ctor_get(v_t_12_, 1);
lean_inc_ref(v_e_49_);
lean_dec_ref(v_t_12_);
v___x_50_ = lean_apply_2(v_k_13_, v_k_48_, v_e_49_);
return v___x_50_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim(lean_object* v_motive__2_51_, lean_object* v_ctorIdx_52_, lean_object* v_t_53_, lean_object* v_h_54_, lean_object* v_k_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_53_, v_k_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___boxed(lean_object* v_motive__2_57_, lean_object* v_ctorIdx_58_, lean_object* v_t_59_, lean_object* v_h_60_, lean_object* v_k_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim(v_motive__2_57_, v_ctorIdx_58_, v_t_59_, v_h_60_, v_k_61_);
lean_dec(v_ctorIdx_58_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_core_elim___redArg(lean_object* v_t_63_, lean_object* v_core_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_63_, v_core_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_core_elim(lean_object* v_motive__2_66_, lean_object* v_t_67_, lean_object* v_h_68_, lean_object* v_core_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_67_, v_core_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_coreS_elim___redArg(lean_object* v_t_71_, lean_object* v_coreS_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_71_, v_coreS_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_coreS_elim(lean_object* v_motive__2_74_, lean_object* v_t_75_, lean_object* v_h_76_, lean_object* v_coreS_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_75_, v_coreS_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_superpose_elim___redArg(lean_object* v_t_79_, lean_object* v_superpose_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_79_, v_superpose_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_superpose_elim(lean_object* v_motive__2_82_, lean_object* v_t_83_, lean_object* v_h_84_, lean_object* v_superpose_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_83_, v_superpose_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_simp_elim___redArg(lean_object* v_t_87_, lean_object* v_simp_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_87_, v_simp_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_simp_elim(lean_object* v_motive__2_90_, lean_object* v_t_91_, lean_object* v_h_92_, lean_object* v_simp_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_91_, v_simp_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_mul_elim___redArg(lean_object* v_t_95_, lean_object* v_mul_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_95_, v_mul_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_mul_elim(lean_object* v_motive__2_98_, lean_object* v_t_99_, lean_object* v_h_100_, lean_object* v_mul_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_99_, v_mul_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_div_elim___redArg(lean_object* v_t_103_, lean_object* v_div_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_103_, v_div_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_div_elim(lean_object* v_motive__2_106_, lean_object* v_t_107_, lean_object* v_h_108_, lean_object* v_div_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_107_, v_div_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_gcd_elim___redArg(lean_object* v_t_111_, lean_object* v_gcd_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_111_, v_gcd_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_gcd_elim(lean_object* v_motive__2_114_, lean_object* v_t_115_, lean_object* v_h_116_, lean_object* v_gcd_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_115_, v_gcd_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_numEq0_elim___redArg(lean_object* v_t_119_, lean_object* v_numEq0_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_119_, v_numEq0_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_numEq0_elim(lean_object* v_motive__2_122_, lean_object* v_t_123_, lean_object* v_h_124_, lean_object* v_numEq0_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_123_, v_numEq0_125_);
return v___x_126_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__2(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_130_ = lean_box(0);
v___x_131_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__1));
v___x_132_ = l_Lean_Expr_const___override(v___x_131_, v___x_130_);
return v___x_132_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__3(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_133_ = l_Lean_Grind_CommRing_instInhabitedExpr_default;
v___x_134_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__2);
v___x_135_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set(v___x_135_, 1, v___x_134_);
lean_ctor_set(v___x_135_, 2, v___x_133_);
lean_ctor_set(v___x_135_, 3, v___x_133_);
return v___x_135_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof(void){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__3, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__3_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__3);
return v___x_136_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstr___closed__0(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_137_ = lean_unsigned_to_nat(0u);
v___x_138_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__3, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__3_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__3);
v___x_139_ = l_Lean_Grind_CommRing_instInhabitedPoly_default;
v___x_140_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
lean_ctor_set(v___x_140_, 1, v___x_138_);
lean_ctor_set(v___x_140_, 2, v___x_137_);
lean_ctor_set(v___x_140_, 3, v___x_137_);
return v___x_140_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstr(void){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstr___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstr___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstr___closed__0);
return v___x_141_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare(lean_object* v_c_u2081_142_, lean_object* v_c_u2082_143_){
_start:
{
lean_object* v_p_144_; lean_object* v_sugar_145_; lean_object* v_id_146_; lean_object* v_p_147_; lean_object* v_sugar_148_; lean_object* v_id_149_; uint8_t v___x_150_; 
v_p_144_ = lean_ctor_get(v_c_u2081_142_, 0);
v_sugar_145_ = lean_ctor_get(v_c_u2081_142_, 2);
v_id_146_ = lean_ctor_get(v_c_u2081_142_, 3);
v_p_147_ = lean_ctor_get(v_c_u2082_143_, 0);
v_sugar_148_ = lean_ctor_get(v_c_u2082_143_, 2);
v_id_149_ = lean_ctor_get(v_c_u2082_143_, 3);
v___x_150_ = lean_nat_dec_lt(v_sugar_145_, v_sugar_148_);
if (v___x_150_ == 0)
{
uint8_t v___x_151_; 
v___x_151_ = lean_nat_dec_eq(v_sugar_145_, v_sugar_148_);
if (v___x_151_ == 0)
{
uint8_t v___x_152_; 
v___x_152_ = 2;
return v___x_152_;
}
else
{
lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_153_ = l_Lean_Grind_CommRing_Poly_degree(v_p_144_);
v___x_154_ = l_Lean_Grind_CommRing_Poly_degree(v_p_147_);
v___x_155_ = lean_nat_dec_lt(v___x_153_, v___x_154_);
if (v___x_155_ == 0)
{
uint8_t v___x_156_; 
v___x_156_ = lean_nat_dec_eq(v___x_153_, v___x_154_);
lean_dec(v___x_154_);
lean_dec(v___x_153_);
if (v___x_156_ == 0)
{
uint8_t v___x_157_; 
v___x_157_ = 2;
return v___x_157_;
}
else
{
uint8_t v___x_158_; 
v___x_158_ = lean_nat_dec_lt(v_id_146_, v_id_149_);
if (v___x_158_ == 0)
{
uint8_t v___x_159_; 
v___x_159_ = lean_nat_dec_eq(v_id_146_, v_id_149_);
if (v___x_159_ == 0)
{
uint8_t v___x_160_; 
v___x_160_ = 2;
return v___x_160_;
}
else
{
uint8_t v___x_161_; 
v___x_161_ = 1;
return v___x_161_;
}
}
else
{
uint8_t v___x_162_; 
v___x_162_ = 0;
return v___x_162_;
}
}
}
else
{
uint8_t v___x_163_; 
lean_dec(v___x_154_);
lean_dec(v___x_153_);
v___x_163_ = 0;
return v___x_163_;
}
}
}
else
{
uint8_t v___x_164_; 
v___x_164_ = 0;
return v___x_164_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare___boxed(lean_object* v_c_u2081_165_, lean_object* v_c_u2082_166_){
_start:
{
uint8_t v_res_167_; lean_object* v_r_168_; 
v_res_167_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare(v_c_u2081_165_, v_c_u2082_166_);
lean_dec_ref(v_c_u2082_166_);
lean_dec_ref(v_c_u2081_165_);
v_r_168_ = lean_box(v_res_167_);
return v_r_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorIdx(lean_object* v_x_169_){
_start:
{
switch(lean_obj_tag(v_x_169_))
{
case 0:
{
lean_object* v___x_170_; 
v___x_170_ = lean_unsigned_to_nat(0u);
return v___x_170_;
}
case 1:
{
lean_object* v___x_171_; 
v___x_171_ = lean_unsigned_to_nat(1u);
return v___x_171_;
}
default: 
{
lean_object* v___x_172_; 
v___x_172_ = lean_unsigned_to_nat(2u);
return v___x_172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorIdx___boxed(lean_object* v_x_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorIdx(v_x_173_);
lean_dec_ref(v_x_173_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim___redArg(lean_object* v_t_175_, lean_object* v_k_176_){
_start:
{
switch(lean_obj_tag(v_t_175_))
{
case 0:
{
lean_object* v_p_177_; lean_object* v___x_178_; 
v_p_177_ = lean_ctor_get(v_t_175_, 0);
lean_inc_ref(v_p_177_);
lean_dec_ref_known(v_t_175_, 1);
v___x_178_ = lean_apply_1(v_k_176_, v_p_177_);
return v___x_178_;
}
case 1:
{
lean_object* v_p_179_; lean_object* v_k_u2081_180_; lean_object* v_d_181_; lean_object* v_k_u2082_182_; lean_object* v_m_u2082_183_; lean_object* v_c_184_; lean_object* v___x_185_; 
v_p_179_ = lean_ctor_get(v_t_175_, 0);
lean_inc_ref(v_p_179_);
v_k_u2081_180_ = lean_ctor_get(v_t_175_, 1);
lean_inc(v_k_u2081_180_);
v_d_181_ = lean_ctor_get(v_t_175_, 2);
lean_inc_ref(v_d_181_);
v_k_u2082_182_ = lean_ctor_get(v_t_175_, 3);
lean_inc(v_k_u2082_182_);
v_m_u2082_183_ = lean_ctor_get(v_t_175_, 4);
lean_inc(v_m_u2082_183_);
v_c_184_ = lean_ctor_get(v_t_175_, 5);
lean_inc_ref(v_c_184_);
lean_dec_ref_known(v_t_175_, 6);
v___x_185_ = lean_apply_6(v_k_176_, v_p_179_, v_k_u2081_180_, v_d_181_, v_k_u2082_182_, v_m_u2082_183_, v_c_184_);
return v___x_185_;
}
default: 
{
lean_object* v_p_186_; lean_object* v_d_187_; lean_object* v_c_188_; lean_object* v___x_189_; 
v_p_186_ = lean_ctor_get(v_t_175_, 0);
lean_inc_ref(v_p_186_);
v_d_187_ = lean_ctor_get(v_t_175_, 1);
lean_inc_ref(v_d_187_);
v_c_188_ = lean_ctor_get(v_t_175_, 2);
lean_inc_ref(v_c_188_);
lean_dec_ref_known(v_t_175_, 3);
v___x_189_ = lean_apply_3(v_k_176_, v_p_186_, v_d_187_, v_c_188_);
return v___x_189_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim(lean_object* v_motive_190_, lean_object* v_ctorIdx_191_, lean_object* v_t_192_, lean_object* v_h_193_, lean_object* v_k_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim___redArg(v_t_192_, v_k_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim___boxed(lean_object* v_motive_196_, lean_object* v_ctorIdx_197_, lean_object* v_t_198_, lean_object* v_h_199_, lean_object* v_k_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim(v_motive_196_, v_ctorIdx_197_, v_t_198_, v_h_199_, v_k_200_);
lean_dec(v_ctorIdx_197_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_input_elim___redArg(lean_object* v_t_202_, lean_object* v_input_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim___redArg(v_t_202_, v_input_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_input_elim(lean_object* v_motive_205_, lean_object* v_t_206_, lean_object* v_h_207_, lean_object* v_input_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim___redArg(v_t_206_, v_input_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_step_elim___redArg(lean_object* v_t_210_, lean_object* v_step_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim___redArg(v_t_210_, v_step_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_step_elim(lean_object* v_motive_213_, lean_object* v_t_214_, lean_object* v_h_215_, lean_object* v_step_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim___redArg(v_t_214_, v_step_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_normEq0_elim___redArg(lean_object* v_t_218_, lean_object* v_normEq0_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim___redArg(v_t_218_, v_normEq0_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_normEq0_elim(lean_object* v_motive_221_, lean_object* v_t_222_, lean_object* v_h_223_, lean_object* v_normEq0_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim___redArg(v_t_222_, v_normEq0_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_p(lean_object* v_x_226_){
_start:
{
lean_object* v_p_227_; 
v_p_227_ = lean_ctor_get(v_x_226_, 0);
lean_inc_ref(v_p_227_);
return v_p_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_p___boxed(lean_object* v_x_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_p(v_x_228_);
lean_dec_ref(v_x_228_);
return v_res_229_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__0(void){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_230_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__1(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__0);
v___x_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
return v___x_232_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__2(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_233_ = lean_unsigned_to_nat(32u);
v___x_234_ = lean_mk_empty_array_with_capacity(v___x_233_);
v___x_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
return v___x_235_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__3(void){
_start:
{
size_t v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_236_ = ((size_t)5ULL);
v___x_237_ = lean_unsigned_to_nat(0u);
v___x_238_ = lean_unsigned_to_nat(32u);
v___x_239_ = lean_mk_empty_array_with_capacity(v___x_238_);
v___x_240_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__2);
v___x_241_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_241_, 0, v___x_240_);
lean_ctor_set(v___x_241_, 1, v___x_239_);
lean_ctor_set(v___x_241_, 2, v___x_237_);
lean_ctor_set(v___x_241_, 3, v___x_237_);
lean_ctor_set_usize(v___x_241_, 4, v___x_236_);
return v___x_241_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__4(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_242_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__3, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__3_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__3);
v___x_243_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__1);
v___x_244_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
lean_ctor_set(v___x_244_, 1, v___x_242_);
lean_ctor_set(v___x_244_, 2, v___x_243_);
return v___x_244_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default(void){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__4, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__4_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__4);
return v___x_245_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState(void){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default;
return v___x_246_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__0(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__0);
v___x_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
return v___x_248_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__1(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_249_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__0);
v___x_250_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__3, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__3_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__3);
v___x_251_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
lean_ctor_set(v___x_251_, 1, v___x_249_);
lean_ctor_set(v___x_251_, 2, v___x_249_);
return v___x_251_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default(void){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__1);
return v___x_252_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState(void){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default;
return v___x_253_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__0);
v___x_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___redArg(){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___redArg___closed__0);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___redArg___boxed(lean_object* v___dummy_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___redArg();
return v_res_259_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___redArg();
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0(lean_object* v_00_u03b2_261_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___closed__0);
return v___x_262_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__0(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_263_ = lean_unsigned_to_nat(32u);
v___x_264_ = lean_mk_empty_array_with_capacity(v___x_263_);
v___x_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
return v___x_265_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__1(void){
_start:
{
size_t v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_266_ = ((size_t)5ULL);
v___x_267_ = lean_unsigned_to_nat(0u);
v___x_268_ = lean_unsigned_to_nat(32u);
v___x_269_ = lean_mk_empty_array_with_capacity(v___x_268_);
v___x_270_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__0);
v___x_271_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_271_, 0, v___x_270_);
lean_ctor_set(v___x_271_, 1, v___x_269_);
lean_ctor_set(v___x_271_, 2, v___x_267_);
lean_ctor_set(v___x_271_, 3, v___x_267_);
lean_ctor_set_usize(v___x_271_, 4, v___x_266_);
return v___x_271_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__2(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; uint8_t v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_272_ = lean_box(0);
v___x_273_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___closed__0);
v___x_274_ = 0;
v___x_275_ = lean_box(0);
v___x_276_ = lean_box(1);
v___x_277_ = lean_unsigned_to_nat(0u);
v___x_278_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__1);
v___x_279_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default;
v___x_280_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_280_, 0, v___x_279_);
lean_ctor_set(v___x_280_, 1, v___x_278_);
lean_ctor_set(v___x_280_, 2, v___x_277_);
lean_ctor_set(v___x_280_, 3, v___x_277_);
lean_ctor_set(v___x_280_, 4, v___x_276_);
lean_ctor_set(v___x_280_, 5, v___x_275_);
lean_ctor_set(v___x_280_, 6, v___x_278_);
lean_ctor_set(v___x_280_, 7, v___x_273_);
lean_ctor_set(v___x_280_, 8, v___x_277_);
lean_ctor_set(v___x_280_, 9, v___x_272_);
lean_ctor_set_uint8(v___x_280_, sizeof(void*)*10, v___x_274_);
lean_ctor_set_uint8(v___x_280_, sizeof(void*)*10 + 1, v___x_274_);
return v___x_280_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default(void){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__2);
return v___x_281_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState(void){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default;
return v___x_282_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__1(void){
_start:
{
uint8_t v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_285_ = 0;
v___x_286_ = lean_unsigned_to_nat(0u);
v___x_287_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__0);
v___x_288_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__0));
v___x_289_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_289_, 0, v___x_288_);
lean_ctor_set(v___x_289_, 1, v___x_287_);
lean_ctor_set(v___x_289_, 2, v___x_288_);
lean_ctor_set(v___x_289_, 3, v___x_287_);
lean_ctor_set(v___x_289_, 4, v___x_288_);
lean_ctor_set(v___x_289_, 5, v___x_287_);
lean_ctor_set(v___x_289_, 6, v___x_288_);
lean_ctor_set(v___x_289_, 7, v___x_287_);
lean_ctor_set(v___x_289_, 8, v___x_286_);
lean_ctor_set_uint8(v___x_289_, sizeof(void*)*9, v___x_285_);
return v___x_289_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default(void){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__1);
return v___x_290_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState(void){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default;
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2_(lean_object* v___x_292_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_292_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2____boxed(lean_object* v___x_295_, lean_object* v___y_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2_(v___x_295_);
return v_res_297_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_298_; lean_object* v___f_299_; 
v___x_298_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__1);
v___f_299_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_299_, 0, v___x_298_);
return v___f_299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_301_; lean_object* v___x_302_; 
v___f_301_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2_);
v___x_302_ = l_Lean_Meta_Grind_registerSolverExtension___redArg(v___f_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2____boxed(lean_object* v_a_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2_();
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_309_ = l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_308_, v_a_305_, v_a_306_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg___boxed(lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_310_, v_a_311_);
lean_dec_ref(v_a_311_);
lean_dec(v_a_310_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_get_x27(lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_314_, v_a_322_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_get_x27___boxed(lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27(v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
lean_dec(v_a_329_);
lean_dec_ref(v_a_328_);
lean_dec(v_a_327_);
lean_dec(v_a_326_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_modify_x27___redArg(lean_object* v_f_338_, lean_object* v_a_339_){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_342_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_341_, v_f_338_, v_a_339_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_modify_x27___redArg___boxed(lean_object* v_f_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_Meta_Grind_Arith_CommRing_modify_x27___redArg(v_f_343_, v_a_344_);
lean_dec(v_a_344_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_modify_x27(lean_object* v_f_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_360_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_359_, v_f_347_, v_a_348_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_modify_x27___boxed(lean_object* v_f_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lean_Meta_Grind_Arith_CommRing_modify_x27(v_f_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_);
lean_dec(v_a_371_);
lean_dec_ref(v_a_370_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
lean_dec(v_a_367_);
lean_dec_ref(v_a_366_);
lean_dec(v_a_365_);
lean_dec_ref(v_a_364_);
lean_dec(v_a_363_);
lean_dec(v_a_362_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_padAndModify___redArg(lean_object* v_inst_374_, lean_object* v_a_375_, lean_object* v_i_376_, lean_object* v_f_377_){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; uint8_t v___x_382_; 
v___x_378_ = lean_unsigned_to_nat(1u);
v___x_379_ = lean_nat_add(v_i_376_, v___x_378_);
v___x_380_ = l_Array_rightpad___redArg(v___x_379_, v_inst_374_, v_a_375_);
lean_dec(v___x_379_);
v___x_381_ = lean_array_get_size(v___x_380_);
v___x_382_ = lean_nat_dec_lt(v_i_376_, v___x_381_);
if (v___x_382_ == 0)
{
lean_dec(v_f_377_);
return v___x_380_;
}
else
{
lean_object* v_v_383_; lean_object* v___x_384_; lean_object* v_xs_x27_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v_v_383_ = lean_array_fget(v___x_380_, v_i_376_);
v___x_384_ = lean_box(0);
v_xs_x27_385_ = lean_array_fset(v___x_380_, v_i_376_, v___x_384_);
v___x_386_ = lean_apply_1(v_f_377_, v_v_383_);
v___x_387_ = lean_array_fset(v_xs_x27_385_, v_i_376_, v___x_386_);
return v___x_387_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_padAndModify___redArg___boxed(lean_object* v_inst_388_, lean_object* v_a_389_, lean_object* v_i_390_, lean_object* v_f_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_padAndModify___redArg(v_inst_388_, v_a_389_, v_i_390_, v_f_391_);
lean_dec(v_i_390_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_padAndModify(lean_object* v_00_u03b1_393_, lean_object* v_inst_394_, lean_object* v_a_395_, lean_object* v_i_396_, lean_object* v_f_397_){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; uint8_t v___x_402_; 
v___x_398_ = lean_unsigned_to_nat(1u);
v___x_399_ = lean_nat_add(v_i_396_, v___x_398_);
v___x_400_ = l_Array_rightpad___redArg(v___x_399_, v_inst_394_, v_a_395_);
lean_dec(v___x_399_);
v___x_401_ = lean_array_get_size(v___x_400_);
v___x_402_ = lean_nat_dec_lt(v_i_396_, v___x_401_);
if (v___x_402_ == 0)
{
lean_dec(v_f_397_);
return v___x_400_;
}
else
{
lean_object* v_v_403_; lean_object* v___x_404_; lean_object* v_xs_x27_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v_v_403_ = lean_array_fget(v___x_400_, v_i_396_);
v___x_404_ = lean_box(0);
v_xs_x27_405_ = lean_array_fset(v___x_400_, v_i_396_, v___x_404_);
v___x_406_ = lean_apply_1(v_f_397_, v_v_403_);
v___x_407_ = lean_array_fset(v_xs_x27_405_, v_i_396_, v___x_406_);
return v___x_407_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_padAndModify___boxed(lean_object* v_00_u03b1_408_, lean_object* v_inst_409_, lean_object* v_a_410_, lean_object* v_i_411_, lean_object* v_f_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_padAndModify(v_00_u03b1_408_, v_inst_409_, v_a_410_, v_i_411_, v_f_412_);
lean_dec(v_i_411_);
return v_res_413_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_State_getRing___closed__0(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; uint8_t v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_414_ = lean_box(0);
v___x_415_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___closed__0);
v___x_416_ = 0;
v___x_417_ = lean_box(0);
v___x_418_ = lean_box(1);
v___x_419_ = lean_unsigned_to_nat(0u);
v___x_420_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__3, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__3_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__3);
v___x_421_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__1);
v___x_422_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_422_, 0, v___x_421_);
lean_ctor_set(v___x_422_, 1, v___x_420_);
lean_ctor_set(v___x_422_, 2, v___x_419_);
lean_ctor_set(v___x_422_, 3, v___x_419_);
lean_ctor_set(v___x_422_, 4, v___x_418_);
lean_ctor_set(v___x_422_, 5, v___x_417_);
lean_ctor_set(v___x_422_, 6, v___x_420_);
lean_ctor_set(v___x_422_, 7, v___x_415_);
lean_ctor_set(v___x_422_, 8, v___x_419_);
lean_ctor_set(v___x_422_, 9, v___x_414_);
lean_ctor_set_uint8(v___x_422_, sizeof(void*)*10, v___x_416_);
lean_ctor_set_uint8(v___x_422_, sizeof(void*)*10 + 1, v___x_416_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_getRing(lean_object* v_s_423_, lean_object* v_ringId_424_){
_start:
{
lean_object* v_rings_425_; lean_object* v___x_426_; lean_object* v___x_427_; uint8_t v___x_428_; 
v_rings_425_ = lean_ctor_get(v_s_423_, 0);
v___x_426_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_State_getRing___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_State_getRing___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_State_getRing___closed__0);
v___x_427_ = lean_array_get_size(v_rings_425_);
v___x_428_ = lean_nat_dec_lt(v_ringId_424_, v___x_427_);
if (v___x_428_ == 0)
{
return v___x_426_;
}
else
{
lean_object* v___x_429_; 
v___x_429_ = lean_array_fget_borrowed(v_rings_425_, v_ringId_424_);
lean_inc(v___x_429_);
return v___x_429_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_getRing___boxed(lean_object* v_s_430_, lean_object* v_ringId_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Lean_Meta_Grind_Arith_CommRing_State_getRing(v_s_430_, v_ringId_431_);
lean_dec(v_ringId_431_);
lean_dec_ref(v_s_430_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_modifyRing(lean_object* v_s_433_, lean_object* v_ringId_434_, lean_object* v_f_435_){
_start:
{
lean_object* v_rings_436_; lean_object* v_exprToRingId_437_; lean_object* v_semirings_438_; lean_object* v_exprToSemiringId_439_; lean_object* v_ncRings_440_; lean_object* v_exprToNCRingId_441_; lean_object* v_ncSemirings_442_; lean_object* v_exprToNCSemiringId_443_; lean_object* v_steps_444_; uint8_t v_reportedMaxDegreeIssue_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_466_; 
v_rings_436_ = lean_ctor_get(v_s_433_, 0);
v_exprToRingId_437_ = lean_ctor_get(v_s_433_, 1);
v_semirings_438_ = lean_ctor_get(v_s_433_, 2);
v_exprToSemiringId_439_ = lean_ctor_get(v_s_433_, 3);
v_ncRings_440_ = lean_ctor_get(v_s_433_, 4);
v_exprToNCRingId_441_ = lean_ctor_get(v_s_433_, 5);
v_ncSemirings_442_ = lean_ctor_get(v_s_433_, 6);
v_exprToNCSemiringId_443_ = lean_ctor_get(v_s_433_, 7);
v_steps_444_ = lean_ctor_get(v_s_433_, 8);
v_reportedMaxDegreeIssue_445_ = lean_ctor_get_uint8(v_s_433_, sizeof(void*)*9);
v_isSharedCheck_466_ = !lean_is_exclusive(v_s_433_);
if (v_isSharedCheck_466_ == 0)
{
v___x_447_ = v_s_433_;
v_isShared_448_ = v_isSharedCheck_466_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_steps_444_);
lean_inc(v_exprToNCSemiringId_443_);
lean_inc(v_ncSemirings_442_);
lean_inc(v_exprToNCRingId_441_);
lean_inc(v_ncRings_440_);
lean_inc(v_exprToSemiringId_439_);
lean_inc(v_semirings_438_);
lean_inc(v_exprToRingId_437_);
lean_inc(v_rings_436_);
lean_dec(v_s_433_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_466_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_449_ = lean_unsigned_to_nat(1u);
v___x_450_ = lean_nat_add(v_ringId_434_, v___x_449_);
v___x_451_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default;
v___x_452_ = l_Array_rightpad___redArg(v___x_450_, v___x_451_, v_rings_436_);
lean_dec(v___x_450_);
v___x_453_ = lean_array_get_size(v___x_452_);
v___x_454_ = lean_nat_dec_lt(v_ringId_434_, v___x_453_);
if (v___x_454_ == 0)
{
lean_object* v___x_456_; 
lean_dec_ref(v_f_435_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v___x_452_);
v___x_456_ = v___x_447_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_452_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v_exprToRingId_437_);
lean_ctor_set(v_reuseFailAlloc_457_, 2, v_semirings_438_);
lean_ctor_set(v_reuseFailAlloc_457_, 3, v_exprToSemiringId_439_);
lean_ctor_set(v_reuseFailAlloc_457_, 4, v_ncRings_440_);
lean_ctor_set(v_reuseFailAlloc_457_, 5, v_exprToNCRingId_441_);
lean_ctor_set(v_reuseFailAlloc_457_, 6, v_ncSemirings_442_);
lean_ctor_set(v_reuseFailAlloc_457_, 7, v_exprToNCSemiringId_443_);
lean_ctor_set(v_reuseFailAlloc_457_, 8, v_steps_444_);
lean_ctor_set_uint8(v_reuseFailAlloc_457_, sizeof(void*)*9, v_reportedMaxDegreeIssue_445_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
else
{
lean_object* v_v_458_; lean_object* v___x_459_; lean_object* v_xs_x27_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_464_; 
v_v_458_ = lean_array_fget(v___x_452_, v_ringId_434_);
v___x_459_ = lean_box(0);
v_xs_x27_460_ = lean_array_fset(v___x_452_, v_ringId_434_, v___x_459_);
v___x_461_ = lean_apply_1(v_f_435_, v_v_458_);
v___x_462_ = lean_array_fset(v_xs_x27_460_, v_ringId_434_, v___x_461_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v___x_462_);
v___x_464_ = v___x_447_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_462_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v_exprToRingId_437_);
lean_ctor_set(v_reuseFailAlloc_465_, 2, v_semirings_438_);
lean_ctor_set(v_reuseFailAlloc_465_, 3, v_exprToSemiringId_439_);
lean_ctor_set(v_reuseFailAlloc_465_, 4, v_ncRings_440_);
lean_ctor_set(v_reuseFailAlloc_465_, 5, v_exprToNCRingId_441_);
lean_ctor_set(v_reuseFailAlloc_465_, 6, v_ncSemirings_442_);
lean_ctor_set(v_reuseFailAlloc_465_, 7, v_exprToNCSemiringId_443_);
lean_ctor_set(v_reuseFailAlloc_465_, 8, v_steps_444_);
lean_ctor_set_uint8(v_reuseFailAlloc_465_, sizeof(void*)*9, v_reportedMaxDegreeIssue_445_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_modifyRing___boxed(lean_object* v_s_467_, lean_object* v_ringId_468_, lean_object* v_f_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Lean_Meta_Grind_Arith_CommRing_State_modifyRing(v_s_467_, v_ringId_468_, v_f_469_);
lean_dec(v_ringId_468_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_getSemiring(lean_object* v_s_471_, lean_object* v_semiringId_472_){
_start:
{
lean_object* v_semirings_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; uint8_t v___x_477_; 
v_semirings_473_ = lean_ctor_get(v_s_471_, 2);
v___x_474_ = lean_unsigned_to_nat(32u);
v___x_475_ = lean_mk_empty_array_with_capacity(v___x_474_);
lean_dec_ref(v___x_475_);
v___x_476_ = lean_array_get_size(v_semirings_473_);
v___x_477_ = lean_nat_dec_lt(v_semiringId_472_, v___x_476_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; 
v___x_478_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__4, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__4_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__4);
return v___x_478_;
}
else
{
lean_object* v___x_479_; 
v___x_479_ = lean_array_fget_borrowed(v_semirings_473_, v_semiringId_472_);
lean_inc(v___x_479_);
return v___x_479_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_getSemiring___boxed(lean_object* v_s_480_, lean_object* v_semiringId_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Lean_Meta_Grind_Arith_CommRing_State_getSemiring(v_s_480_, v_semiringId_481_);
lean_dec(v_semiringId_481_);
lean_dec_ref(v_s_480_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_modifySemiring(lean_object* v_s_483_, lean_object* v_semiringId_484_, lean_object* v_f_485_){
_start:
{
lean_object* v_rings_486_; lean_object* v_exprToRingId_487_; lean_object* v_semirings_488_; lean_object* v_exprToSemiringId_489_; lean_object* v_ncRings_490_; lean_object* v_exprToNCRingId_491_; lean_object* v_ncSemirings_492_; lean_object* v_exprToNCSemiringId_493_; lean_object* v_steps_494_; uint8_t v_reportedMaxDegreeIssue_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_516_; 
v_rings_486_ = lean_ctor_get(v_s_483_, 0);
v_exprToRingId_487_ = lean_ctor_get(v_s_483_, 1);
v_semirings_488_ = lean_ctor_get(v_s_483_, 2);
v_exprToSemiringId_489_ = lean_ctor_get(v_s_483_, 3);
v_ncRings_490_ = lean_ctor_get(v_s_483_, 4);
v_exprToNCRingId_491_ = lean_ctor_get(v_s_483_, 5);
v_ncSemirings_492_ = lean_ctor_get(v_s_483_, 6);
v_exprToNCSemiringId_493_ = lean_ctor_get(v_s_483_, 7);
v_steps_494_ = lean_ctor_get(v_s_483_, 8);
v_reportedMaxDegreeIssue_495_ = lean_ctor_get_uint8(v_s_483_, sizeof(void*)*9);
v_isSharedCheck_516_ = !lean_is_exclusive(v_s_483_);
if (v_isSharedCheck_516_ == 0)
{
v___x_497_ = v_s_483_;
v_isShared_498_ = v_isSharedCheck_516_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_steps_494_);
lean_inc(v_exprToNCSemiringId_493_);
lean_inc(v_ncSemirings_492_);
lean_inc(v_exprToNCRingId_491_);
lean_inc(v_ncRings_490_);
lean_inc(v_exprToSemiringId_489_);
lean_inc(v_semirings_488_);
lean_inc(v_exprToRingId_487_);
lean_inc(v_rings_486_);
lean_dec(v_s_483_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_516_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_499_ = lean_unsigned_to_nat(1u);
v___x_500_ = lean_nat_add(v_semiringId_484_, v___x_499_);
v___x_501_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default;
v___x_502_ = l_Array_rightpad___redArg(v___x_500_, v___x_501_, v_semirings_488_);
lean_dec(v___x_500_);
v___x_503_ = lean_array_get_size(v___x_502_);
v___x_504_ = lean_nat_dec_lt(v_semiringId_484_, v___x_503_);
if (v___x_504_ == 0)
{
lean_object* v___x_506_; 
lean_dec_ref(v_f_485_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 2, v___x_502_);
v___x_506_ = v___x_497_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_rings_486_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v_exprToRingId_487_);
lean_ctor_set(v_reuseFailAlloc_507_, 2, v___x_502_);
lean_ctor_set(v_reuseFailAlloc_507_, 3, v_exprToSemiringId_489_);
lean_ctor_set(v_reuseFailAlloc_507_, 4, v_ncRings_490_);
lean_ctor_set(v_reuseFailAlloc_507_, 5, v_exprToNCRingId_491_);
lean_ctor_set(v_reuseFailAlloc_507_, 6, v_ncSemirings_492_);
lean_ctor_set(v_reuseFailAlloc_507_, 7, v_exprToNCSemiringId_493_);
lean_ctor_set(v_reuseFailAlloc_507_, 8, v_steps_494_);
lean_ctor_set_uint8(v_reuseFailAlloc_507_, sizeof(void*)*9, v_reportedMaxDegreeIssue_495_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
else
{
lean_object* v_v_508_; lean_object* v___x_509_; lean_object* v_xs_x27_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_514_; 
v_v_508_ = lean_array_fget(v___x_502_, v_semiringId_484_);
v___x_509_ = lean_box(0);
v_xs_x27_510_ = lean_array_fset(v___x_502_, v_semiringId_484_, v___x_509_);
v___x_511_ = lean_apply_1(v_f_485_, v_v_508_);
v___x_512_ = lean_array_fset(v_xs_x27_510_, v_semiringId_484_, v___x_511_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 2, v___x_512_);
v___x_514_ = v___x_497_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_rings_486_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_exprToRingId_487_);
lean_ctor_set(v_reuseFailAlloc_515_, 2, v___x_512_);
lean_ctor_set(v_reuseFailAlloc_515_, 3, v_exprToSemiringId_489_);
lean_ctor_set(v_reuseFailAlloc_515_, 4, v_ncRings_490_);
lean_ctor_set(v_reuseFailAlloc_515_, 5, v_exprToNCRingId_491_);
lean_ctor_set(v_reuseFailAlloc_515_, 6, v_ncSemirings_492_);
lean_ctor_set(v_reuseFailAlloc_515_, 7, v_exprToNCSemiringId_493_);
lean_ctor_set(v_reuseFailAlloc_515_, 8, v_steps_494_);
lean_ctor_set_uint8(v_reuseFailAlloc_515_, sizeof(void*)*9, v_reportedMaxDegreeIssue_495_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_modifySemiring___boxed(lean_object* v_s_517_, lean_object* v_semiringId_518_, lean_object* v_f_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Lean_Meta_Grind_Arith_CommRing_State_modifySemiring(v_s_517_, v_semiringId_518_, v_f_519_);
lean_dec(v_semiringId_518_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_getNCRing(lean_object* v_s_521_, lean_object* v_ringId_522_){
_start:
{
lean_object* v_ncRings_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; uint8_t v___x_527_; 
v_ncRings_523_ = lean_ctor_get(v_s_521_, 4);
v___x_524_ = lean_unsigned_to_nat(32u);
v___x_525_ = lean_mk_empty_array_with_capacity(v___x_524_);
lean_dec_ref(v___x_525_);
v___x_526_ = lean_array_get_size(v_ncRings_523_);
v___x_527_ = lean_nat_dec_lt(v_ringId_522_, v___x_526_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; 
v___x_528_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__1);
return v___x_528_;
}
else
{
lean_object* v___x_529_; 
v___x_529_ = lean_array_fget_borrowed(v_ncRings_523_, v_ringId_522_);
lean_inc(v___x_529_);
return v___x_529_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_getNCRing___boxed(lean_object* v_s_530_, lean_object* v_ringId_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_Meta_Grind_Arith_CommRing_State_getNCRing(v_s_530_, v_ringId_531_);
lean_dec(v_ringId_531_);
lean_dec_ref(v_s_530_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_modifyNCRing(lean_object* v_s_533_, lean_object* v_ringId_534_, lean_object* v_f_535_){
_start:
{
lean_object* v_rings_536_; lean_object* v_exprToRingId_537_; lean_object* v_semirings_538_; lean_object* v_exprToSemiringId_539_; lean_object* v_ncRings_540_; lean_object* v_exprToNCRingId_541_; lean_object* v_ncSemirings_542_; lean_object* v_exprToNCSemiringId_543_; lean_object* v_steps_544_; uint8_t v_reportedMaxDegreeIssue_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_566_; 
v_rings_536_ = lean_ctor_get(v_s_533_, 0);
v_exprToRingId_537_ = lean_ctor_get(v_s_533_, 1);
v_semirings_538_ = lean_ctor_get(v_s_533_, 2);
v_exprToSemiringId_539_ = lean_ctor_get(v_s_533_, 3);
v_ncRings_540_ = lean_ctor_get(v_s_533_, 4);
v_exprToNCRingId_541_ = lean_ctor_get(v_s_533_, 5);
v_ncSemirings_542_ = lean_ctor_get(v_s_533_, 6);
v_exprToNCSemiringId_543_ = lean_ctor_get(v_s_533_, 7);
v_steps_544_ = lean_ctor_get(v_s_533_, 8);
v_reportedMaxDegreeIssue_545_ = lean_ctor_get_uint8(v_s_533_, sizeof(void*)*9);
v_isSharedCheck_566_ = !lean_is_exclusive(v_s_533_);
if (v_isSharedCheck_566_ == 0)
{
v___x_547_ = v_s_533_;
v_isShared_548_ = v_isSharedCheck_566_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_steps_544_);
lean_inc(v_exprToNCSemiringId_543_);
lean_inc(v_ncSemirings_542_);
lean_inc(v_exprToNCRingId_541_);
lean_inc(v_ncRings_540_);
lean_inc(v_exprToSemiringId_539_);
lean_inc(v_semirings_538_);
lean_inc(v_exprToRingId_537_);
lean_inc(v_rings_536_);
lean_dec(v_s_533_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_566_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v___x_549_ = lean_unsigned_to_nat(1u);
v___x_550_ = lean_nat_add(v_ringId_534_, v___x_549_);
v___x_551_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default;
v___x_552_ = l_Array_rightpad___redArg(v___x_550_, v___x_551_, v_ncRings_540_);
lean_dec(v___x_550_);
v___x_553_ = lean_array_get_size(v___x_552_);
v___x_554_ = lean_nat_dec_lt(v_ringId_534_, v___x_553_);
if (v___x_554_ == 0)
{
lean_object* v___x_556_; 
lean_dec_ref(v_f_535_);
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 4, v___x_552_);
v___x_556_ = v___x_547_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_rings_536_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v_exprToRingId_537_);
lean_ctor_set(v_reuseFailAlloc_557_, 2, v_semirings_538_);
lean_ctor_set(v_reuseFailAlloc_557_, 3, v_exprToSemiringId_539_);
lean_ctor_set(v_reuseFailAlloc_557_, 4, v___x_552_);
lean_ctor_set(v_reuseFailAlloc_557_, 5, v_exprToNCRingId_541_);
lean_ctor_set(v_reuseFailAlloc_557_, 6, v_ncSemirings_542_);
lean_ctor_set(v_reuseFailAlloc_557_, 7, v_exprToNCSemiringId_543_);
lean_ctor_set(v_reuseFailAlloc_557_, 8, v_steps_544_);
lean_ctor_set_uint8(v_reuseFailAlloc_557_, sizeof(void*)*9, v_reportedMaxDegreeIssue_545_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
else
{
lean_object* v_v_558_; lean_object* v___x_559_; lean_object* v_xs_x27_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_564_; 
v_v_558_ = lean_array_fget(v___x_552_, v_ringId_534_);
v___x_559_ = lean_box(0);
v_xs_x27_560_ = lean_array_fset(v___x_552_, v_ringId_534_, v___x_559_);
v___x_561_ = lean_apply_1(v_f_535_, v_v_558_);
v___x_562_ = lean_array_fset(v_xs_x27_560_, v_ringId_534_, v___x_561_);
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 4, v___x_562_);
v___x_564_ = v___x_547_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_rings_536_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v_exprToRingId_537_);
lean_ctor_set(v_reuseFailAlloc_565_, 2, v_semirings_538_);
lean_ctor_set(v_reuseFailAlloc_565_, 3, v_exprToSemiringId_539_);
lean_ctor_set(v_reuseFailAlloc_565_, 4, v___x_562_);
lean_ctor_set(v_reuseFailAlloc_565_, 5, v_exprToNCRingId_541_);
lean_ctor_set(v_reuseFailAlloc_565_, 6, v_ncSemirings_542_);
lean_ctor_set(v_reuseFailAlloc_565_, 7, v_exprToNCSemiringId_543_);
lean_ctor_set(v_reuseFailAlloc_565_, 8, v_steps_544_);
lean_ctor_set_uint8(v_reuseFailAlloc_565_, sizeof(void*)*9, v_reportedMaxDegreeIssue_545_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_modifyNCRing___boxed(lean_object* v_s_567_, lean_object* v_ringId_568_, lean_object* v_f_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_Meta_Grind_Arith_CommRing_State_modifyNCRing(v_s_567_, v_ringId_568_, v_f_569_);
lean_dec(v_ringId_568_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_getNCSemiring(lean_object* v_s_571_, lean_object* v_semiringId_572_){
_start:
{
lean_object* v_ncSemirings_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; uint8_t v___x_577_; 
v_ncSemirings_573_ = lean_ctor_get(v_s_571_, 6);
v___x_574_ = lean_unsigned_to_nat(32u);
v___x_575_ = lean_mk_empty_array_with_capacity(v___x_574_);
lean_dec_ref(v___x_575_);
v___x_576_ = lean_array_get_size(v_ncSemirings_573_);
v___x_577_ = lean_nat_dec_lt(v_semiringId_572_, v___x_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; 
v___x_578_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__4, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__4_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__4);
return v___x_578_;
}
else
{
lean_object* v___x_579_; 
v___x_579_ = lean_array_fget_borrowed(v_ncSemirings_573_, v_semiringId_572_);
lean_inc(v___x_579_);
return v___x_579_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_getNCSemiring___boxed(lean_object* v_s_580_, lean_object* v_semiringId_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Lean_Meta_Grind_Arith_CommRing_State_getNCSemiring(v_s_580_, v_semiringId_581_);
lean_dec(v_semiringId_581_);
lean_dec_ref(v_s_580_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_modifyNCSemiring(lean_object* v_s_583_, lean_object* v_semiringId_584_, lean_object* v_f_585_){
_start:
{
lean_object* v_rings_586_; lean_object* v_exprToRingId_587_; lean_object* v_semirings_588_; lean_object* v_exprToSemiringId_589_; lean_object* v_ncRings_590_; lean_object* v_exprToNCRingId_591_; lean_object* v_ncSemirings_592_; lean_object* v_exprToNCSemiringId_593_; lean_object* v_steps_594_; uint8_t v_reportedMaxDegreeIssue_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_616_; 
v_rings_586_ = lean_ctor_get(v_s_583_, 0);
v_exprToRingId_587_ = lean_ctor_get(v_s_583_, 1);
v_semirings_588_ = lean_ctor_get(v_s_583_, 2);
v_exprToSemiringId_589_ = lean_ctor_get(v_s_583_, 3);
v_ncRings_590_ = lean_ctor_get(v_s_583_, 4);
v_exprToNCRingId_591_ = lean_ctor_get(v_s_583_, 5);
v_ncSemirings_592_ = lean_ctor_get(v_s_583_, 6);
v_exprToNCSemiringId_593_ = lean_ctor_get(v_s_583_, 7);
v_steps_594_ = lean_ctor_get(v_s_583_, 8);
v_reportedMaxDegreeIssue_595_ = lean_ctor_get_uint8(v_s_583_, sizeof(void*)*9);
v_isSharedCheck_616_ = !lean_is_exclusive(v_s_583_);
if (v_isSharedCheck_616_ == 0)
{
v___x_597_ = v_s_583_;
v_isShared_598_ = v_isSharedCheck_616_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_steps_594_);
lean_inc(v_exprToNCSemiringId_593_);
lean_inc(v_ncSemirings_592_);
lean_inc(v_exprToNCRingId_591_);
lean_inc(v_ncRings_590_);
lean_inc(v_exprToSemiringId_589_);
lean_inc(v_semirings_588_);
lean_inc(v_exprToRingId_587_);
lean_inc(v_rings_586_);
lean_dec(v_s_583_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_616_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_599_ = lean_unsigned_to_nat(1u);
v___x_600_ = lean_nat_add(v_semiringId_584_, v___x_599_);
v___x_601_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default;
v___x_602_ = l_Array_rightpad___redArg(v___x_600_, v___x_601_, v_ncSemirings_592_);
lean_dec(v___x_600_);
v___x_603_ = lean_array_get_size(v___x_602_);
v___x_604_ = lean_nat_dec_lt(v_semiringId_584_, v___x_603_);
if (v___x_604_ == 0)
{
lean_object* v___x_606_; 
lean_dec_ref(v_f_585_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 6, v___x_602_);
v___x_606_ = v___x_597_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_rings_586_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v_exprToRingId_587_);
lean_ctor_set(v_reuseFailAlloc_607_, 2, v_semirings_588_);
lean_ctor_set(v_reuseFailAlloc_607_, 3, v_exprToSemiringId_589_);
lean_ctor_set(v_reuseFailAlloc_607_, 4, v_ncRings_590_);
lean_ctor_set(v_reuseFailAlloc_607_, 5, v_exprToNCRingId_591_);
lean_ctor_set(v_reuseFailAlloc_607_, 6, v___x_602_);
lean_ctor_set(v_reuseFailAlloc_607_, 7, v_exprToNCSemiringId_593_);
lean_ctor_set(v_reuseFailAlloc_607_, 8, v_steps_594_);
lean_ctor_set_uint8(v_reuseFailAlloc_607_, sizeof(void*)*9, v_reportedMaxDegreeIssue_595_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
else
{
lean_object* v_v_608_; lean_object* v___x_609_; lean_object* v_xs_x27_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_614_; 
v_v_608_ = lean_array_fget(v___x_602_, v_semiringId_584_);
v___x_609_ = lean_box(0);
v_xs_x27_610_ = lean_array_fset(v___x_602_, v_semiringId_584_, v___x_609_);
v___x_611_ = lean_apply_1(v_f_585_, v_v_608_);
v___x_612_ = lean_array_fset(v_xs_x27_610_, v_semiringId_584_, v___x_611_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 6, v___x_612_);
v___x_614_ = v___x_597_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_rings_586_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v_exprToRingId_587_);
lean_ctor_set(v_reuseFailAlloc_615_, 2, v_semirings_588_);
lean_ctor_set(v_reuseFailAlloc_615_, 3, v_exprToSemiringId_589_);
lean_ctor_set(v_reuseFailAlloc_615_, 4, v_ncRings_590_);
lean_ctor_set(v_reuseFailAlloc_615_, 5, v_exprToNCRingId_591_);
lean_ctor_set(v_reuseFailAlloc_615_, 6, v___x_612_);
lean_ctor_set(v_reuseFailAlloc_615_, 7, v_exprToNCSemiringId_593_);
lean_ctor_set(v_reuseFailAlloc_615_, 8, v_steps_594_);
lean_ctor_set_uint8(v_reuseFailAlloc_615_, sizeof(void*)*9, v_reportedMaxDegreeIssue_595_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_modifyNCSemiring___boxed(lean_object* v_s_617_, lean_object* v_semiringId_618_, lean_object* v_f_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_Meta_Grind_Arith_CommRing_State_modifyNCSemiring(v_s_617_, v_semiringId_618_, v_f_619_);
lean_dec(v_semiringId_618_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadLift___redArg___lam__0(lean_object* v_modifyRingState_621_, lean_object* v_inst_622_, lean_object* v_f_623_){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = lean_apply_1(v_modifyRingState_621_, v_f_623_);
v___x_625_ = lean_apply_2(v_inst_622_, lean_box(0), v___x_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadLift___redArg(lean_object* v_inst_626_, lean_object* v_inst_627_){
_start:
{
lean_object* v_getRingState_628_; lean_object* v_modifyRingState_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_638_; 
v_getRingState_628_ = lean_ctor_get(v_inst_627_, 0);
v_modifyRingState_629_ = lean_ctor_get(v_inst_627_, 1);
v_isSharedCheck_638_ = !lean_is_exclusive(v_inst_627_);
if (v_isSharedCheck_638_ == 0)
{
v___x_631_ = v_inst_627_;
v_isShared_632_ = v_isSharedCheck_638_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_modifyRingState_629_);
lean_inc(v_getRingState_628_);
lean_dec(v_inst_627_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_638_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___f_633_; lean_object* v___x_634_; lean_object* v___x_636_; 
lean_inc(v_inst_626_);
v___f_633_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_633_, 0, v_modifyRingState_629_);
lean_closure_set(v___f_633_, 1, v_inst_626_);
v___x_634_ = lean_apply_2(v_inst_626_, lean_box(0), v_getRingState_628_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 1, v___f_633_);
lean_ctor_set(v___x_631_, 0, v___x_634_);
v___x_636_ = v___x_631_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v___f_633_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadLift(lean_object* v_m_639_, lean_object* v_n_640_, lean_object* v_inst_641_, lean_object* v_inst_642_){
_start:
{
lean_object* v_getRingState_643_; lean_object* v_modifyRingState_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_653_; 
v_getRingState_643_ = lean_ctor_get(v_inst_642_, 0);
v_modifyRingState_644_ = lean_ctor_get(v_inst_642_, 1);
v_isSharedCheck_653_ = !lean_is_exclusive(v_inst_642_);
if (v_isSharedCheck_653_ == 0)
{
v___x_646_ = v_inst_642_;
v_isShared_647_ = v_isSharedCheck_653_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_modifyRingState_644_);
lean_inc(v_getRingState_643_);
lean_dec(v_inst_642_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_653_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___f_648_; lean_object* v___x_649_; lean_object* v___x_651_; 
lean_inc(v_inst_641_);
v___f_648_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_648_, 0, v_modifyRingState_644_);
lean_closure_set(v___f_648_, 1, v_inst_641_);
v___x_649_ = lean_apply_2(v_inst_641_, lean_box(0), v_getRingState_643_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 1, v___f_648_);
lean_ctor_set(v___x_646_, 0, v___x_649_);
v___x_651_ = v___x_646_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_649_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v___f_648_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateOfMonadLift___redArg___lam__0(lean_object* v_modifyCommRingState_654_, lean_object* v_inst_655_, lean_object* v_f_656_){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = lean_apply_1(v_modifyCommRingState_654_, v_f_656_);
v___x_658_ = lean_apply_2(v_inst_655_, lean_box(0), v___x_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateOfMonadLift___redArg(lean_object* v_inst_659_, lean_object* v_inst_660_){
_start:
{
lean_object* v_getCommRingState_661_; lean_object* v_modifyCommRingState_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_671_; 
v_getCommRingState_661_ = lean_ctor_get(v_inst_660_, 0);
v_modifyCommRingState_662_ = lean_ctor_get(v_inst_660_, 1);
v_isSharedCheck_671_ = !lean_is_exclusive(v_inst_660_);
if (v_isSharedCheck_671_ == 0)
{
v___x_664_ = v_inst_660_;
v_isShared_665_ = v_isSharedCheck_671_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_modifyCommRingState_662_);
lean_inc(v_getCommRingState_661_);
lean_dec(v_inst_660_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_671_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___f_666_; lean_object* v___x_667_; lean_object* v___x_669_; 
lean_inc(v_inst_659_);
v___f_666_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_666_, 0, v_modifyCommRingState_662_);
lean_closure_set(v___f_666_, 1, v_inst_659_);
v___x_667_ = lean_apply_2(v_inst_659_, lean_box(0), v_getCommRingState_661_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 1, v___f_666_);
lean_ctor_set(v___x_664_, 0, v___x_667_);
v___x_669_ = v___x_664_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_667_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v___f_666_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateOfMonadLift(lean_object* v_m_672_, lean_object* v_n_673_, lean_object* v_inst_674_, lean_object* v_inst_675_){
_start:
{
lean_object* v_getCommRingState_676_; lean_object* v_modifyCommRingState_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_686_; 
v_getCommRingState_676_ = lean_ctor_get(v_inst_675_, 0);
v_modifyCommRingState_677_ = lean_ctor_get(v_inst_675_, 1);
v_isSharedCheck_686_ = !lean_is_exclusive(v_inst_675_);
if (v_isSharedCheck_686_ == 0)
{
v___x_679_ = v_inst_675_;
v_isShared_680_ = v_isSharedCheck_686_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_modifyCommRingState_677_);
lean_inc(v_getCommRingState_676_);
lean_dec(v_inst_675_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_686_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___f_681_; lean_object* v___x_682_; lean_object* v___x_684_; 
lean_inc(v_inst_674_);
v___f_681_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_681_, 0, v_modifyCommRingState_677_);
lean_closure_set(v___f_681_, 1, v_inst_674_);
v___x_682_ = lean_apply_2(v_inst_674_, lean_box(0), v_getCommRingState_676_);
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 1, v___f_681_);
lean_ctor_set(v___x_679_, 0, v___x_682_);
v___x_684_ = v___x_679_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_682_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v___f_681_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__0(lean_object* v_f_687_, lean_object* v_s_688_){
_start:
{
lean_object* v_toRingState_689_; lean_object* v_denoteEntries_690_; lean_object* v_nextId_691_; lean_object* v_steps_692_; lean_object* v_queue_693_; lean_object* v_basis_694_; lean_object* v_diseqs_695_; uint8_t v_recheck_696_; lean_object* v_invSet_697_; lean_object* v_powIdentityVarCount_698_; lean_object* v_numEq0_x3f_699_; uint8_t v_numEq0Updated_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_708_; 
v_toRingState_689_ = lean_ctor_get(v_s_688_, 0);
v_denoteEntries_690_ = lean_ctor_get(v_s_688_, 1);
v_nextId_691_ = lean_ctor_get(v_s_688_, 2);
v_steps_692_ = lean_ctor_get(v_s_688_, 3);
v_queue_693_ = lean_ctor_get(v_s_688_, 4);
v_basis_694_ = lean_ctor_get(v_s_688_, 5);
v_diseqs_695_ = lean_ctor_get(v_s_688_, 6);
v_recheck_696_ = lean_ctor_get_uint8(v_s_688_, sizeof(void*)*10);
v_invSet_697_ = lean_ctor_get(v_s_688_, 7);
v_powIdentityVarCount_698_ = lean_ctor_get(v_s_688_, 8);
v_numEq0_x3f_699_ = lean_ctor_get(v_s_688_, 9);
v_numEq0Updated_700_ = lean_ctor_get_uint8(v_s_688_, sizeof(void*)*10 + 1);
v_isSharedCheck_708_ = !lean_is_exclusive(v_s_688_);
if (v_isSharedCheck_708_ == 0)
{
v___x_702_ = v_s_688_;
v_isShared_703_ = v_isSharedCheck_708_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_numEq0_x3f_699_);
lean_inc(v_powIdentityVarCount_698_);
lean_inc(v_invSet_697_);
lean_inc(v_diseqs_695_);
lean_inc(v_basis_694_);
lean_inc(v_queue_693_);
lean_inc(v_steps_692_);
lean_inc(v_nextId_691_);
lean_inc(v_denoteEntries_690_);
lean_inc(v_toRingState_689_);
lean_dec(v_s_688_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_708_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_704_; lean_object* v___x_706_; 
v___x_704_ = lean_apply_1(v_f_687_, v_toRingState_689_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 0, v___x_704_);
v___x_706_ = v___x_702_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_704_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v_denoteEntries_690_);
lean_ctor_set(v_reuseFailAlloc_707_, 2, v_nextId_691_);
lean_ctor_set(v_reuseFailAlloc_707_, 3, v_steps_692_);
lean_ctor_set(v_reuseFailAlloc_707_, 4, v_queue_693_);
lean_ctor_set(v_reuseFailAlloc_707_, 5, v_basis_694_);
lean_ctor_set(v_reuseFailAlloc_707_, 6, v_diseqs_695_);
lean_ctor_set(v_reuseFailAlloc_707_, 7, v_invSet_697_);
lean_ctor_set(v_reuseFailAlloc_707_, 8, v_powIdentityVarCount_698_);
lean_ctor_set(v_reuseFailAlloc_707_, 9, v_numEq0_x3f_699_);
lean_ctor_set_uint8(v_reuseFailAlloc_707_, sizeof(void*)*10, v_recheck_696_);
lean_ctor_set_uint8(v_reuseFailAlloc_707_, sizeof(void*)*10 + 1, v_numEq0Updated_700_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__1(lean_object* v_modifyCommRingState_709_, lean_object* v_f_710_){
_start:
{
lean_object* v___f_711_; lean_object* v___x_712_; 
v___f_711_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__0), 2, 1);
lean_closure_set(v___f_711_, 0, v_f_710_);
v___x_712_ = lean_apply_1(v_modifyCommRingState_709_, v___f_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__2(lean_object* v_toPure_713_, lean_object* v_____do__lift_714_){
_start:
{
lean_object* v_toRingState_715_; lean_object* v___x_716_; 
v_toRingState_715_ = lean_ctor_get(v_____do__lift_714_, 0);
lean_inc_ref(v_toRingState_715_);
lean_dec_ref(v_____do__lift_714_);
v___x_716_ = lean_apply_2(v_toPure_713_, lean_box(0), v_toRingState_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg(lean_object* v_inst_717_, lean_object* v_inst_718_){
_start:
{
lean_object* v_toApplicative_719_; lean_object* v_toBind_720_; lean_object* v_getCommRingState_721_; lean_object* v_modifyCommRingState_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_733_; 
v_toApplicative_719_ = lean_ctor_get(v_inst_717_, 0);
lean_inc_ref(v_toApplicative_719_);
v_toBind_720_ = lean_ctor_get(v_inst_717_, 1);
lean_inc(v_toBind_720_);
lean_dec_ref(v_inst_717_);
v_getCommRingState_721_ = lean_ctor_get(v_inst_718_, 0);
v_modifyCommRingState_722_ = lean_ctor_get(v_inst_718_, 1);
v_isSharedCheck_733_ = !lean_is_exclusive(v_inst_718_);
if (v_isSharedCheck_733_ == 0)
{
v___x_724_ = v_inst_718_;
v_isShared_725_ = v_isSharedCheck_733_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_modifyCommRingState_722_);
lean_inc(v_getCommRingState_721_);
lean_dec(v_inst_718_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_733_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v_toPure_726_; lean_object* v___f_727_; lean_object* v___f_728_; lean_object* v___x_729_; lean_object* v___x_731_; 
v_toPure_726_ = lean_ctor_get(v_toApplicative_719_, 1);
lean_inc(v_toPure_726_);
lean_dec_ref(v_toApplicative_719_);
v___f_727_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__1), 2, 1);
lean_closure_set(v___f_727_, 0, v_modifyCommRingState_722_);
v___f_728_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__2), 2, 1);
lean_closure_set(v___f_728_, 0, v_toPure_726_);
v___x_729_ = lean_apply_4(v_toBind_720_, lean_box(0), lean_box(0), v_getCommRingState_721_, v___f_728_);
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 1, v___f_727_);
lean_ctor_set(v___x_724_, 0, v___x_729_);
v___x_731_ = v___x_724_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_729_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v___f_727_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState(lean_object* v_m_734_, lean_object* v_inst_735_, lean_object* v_inst_736_){
_start:
{
lean_object* v_toApplicative_737_; lean_object* v_toBind_738_; lean_object* v_getCommRingState_739_; lean_object* v_modifyCommRingState_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_751_; 
v_toApplicative_737_ = lean_ctor_get(v_inst_735_, 0);
lean_inc_ref(v_toApplicative_737_);
v_toBind_738_ = lean_ctor_get(v_inst_735_, 1);
lean_inc(v_toBind_738_);
lean_dec_ref(v_inst_735_);
v_getCommRingState_739_ = lean_ctor_get(v_inst_736_, 0);
v_modifyCommRingState_740_ = lean_ctor_get(v_inst_736_, 1);
v_isSharedCheck_751_ = !lean_is_exclusive(v_inst_736_);
if (v_isSharedCheck_751_ == 0)
{
v___x_742_ = v_inst_736_;
v_isShared_743_ = v_isSharedCheck_751_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_modifyCommRingState_740_);
lean_inc(v_getCommRingState_739_);
lean_dec(v_inst_736_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_751_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v_toPure_744_; lean_object* v___f_745_; lean_object* v___f_746_; lean_object* v___x_747_; lean_object* v___x_749_; 
v_toPure_744_ = lean_ctor_get(v_toApplicative_737_, 1);
lean_inc(v_toPure_744_);
lean_dec_ref(v_toApplicative_737_);
v___f_745_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__1), 2, 1);
lean_closure_set(v___f_745_, 0, v_modifyCommRingState_740_);
v___f_746_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__2), 2, 1);
lean_closure_set(v___f_746_, 0, v_toPure_744_);
v___x_747_ = lean_apply_4(v_toBind_738_, lean_box(0), lean_box(0), v_getCommRingState_739_, v___f_746_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 1, v___f_745_);
lean_ctor_set(v___x_742_, 0, v___x_747_);
v___x_749_ = v___x_742_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v___f_745_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateOfMonadLift___redArg___lam__0(lean_object* v_modifySemiringState_752_, lean_object* v_inst_753_, lean_object* v_f_754_){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = lean_apply_1(v_modifySemiringState_752_, v_f_754_);
v___x_756_ = lean_apply_2(v_inst_753_, lean_box(0), v___x_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateOfMonadLift___redArg(lean_object* v_inst_757_, lean_object* v_inst_758_){
_start:
{
lean_object* v_getSemiringState_759_; lean_object* v_modifySemiringState_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_769_; 
v_getSemiringState_759_ = lean_ctor_get(v_inst_758_, 0);
v_modifySemiringState_760_ = lean_ctor_get(v_inst_758_, 1);
v_isSharedCheck_769_ = !lean_is_exclusive(v_inst_758_);
if (v_isSharedCheck_769_ == 0)
{
v___x_762_ = v_inst_758_;
v_isShared_763_ = v_isSharedCheck_769_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_modifySemiringState_760_);
lean_inc(v_getSemiringState_759_);
lean_dec(v_inst_758_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_769_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___f_764_; lean_object* v___x_765_; lean_object* v___x_767_; 
lean_inc(v_inst_757_);
v___f_764_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_764_, 0, v_modifySemiringState_760_);
lean_closure_set(v___f_764_, 1, v_inst_757_);
v___x_765_ = lean_apply_2(v_inst_757_, lean_box(0), v_getSemiringState_759_);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 1, v___f_764_);
lean_ctor_set(v___x_762_, 0, v___x_765_);
v___x_767_ = v___x_762_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v___x_765_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v___f_764_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateOfMonadLift(lean_object* v_m_770_, lean_object* v_n_771_, lean_object* v_inst_772_, lean_object* v_inst_773_){
_start:
{
lean_object* v_getSemiringState_774_; lean_object* v_modifySemiringState_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_784_; 
v_getSemiringState_774_ = lean_ctor_get(v_inst_773_, 0);
v_modifySemiringState_775_ = lean_ctor_get(v_inst_773_, 1);
v_isSharedCheck_784_ = !lean_is_exclusive(v_inst_773_);
if (v_isSharedCheck_784_ == 0)
{
v___x_777_ = v_inst_773_;
v_isShared_778_ = v_isSharedCheck_784_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_modifySemiringState_775_);
lean_inc(v_getSemiringState_774_);
lean_dec(v_inst_773_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_784_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___f_779_; lean_object* v___x_780_; lean_object* v___x_782_; 
lean_inc(v_inst_772_);
v___f_779_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_779_, 0, v_modifySemiringState_775_);
lean_closure_set(v___f_779_, 1, v_inst_772_);
v___x_780_ = lean_apply_2(v_inst_772_, lean_box(0), v_getSemiringState_774_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 1, v___f_779_);
lean_ctor_set(v___x_777_, 0, v___x_780_);
v___x_782_ = v___x_777_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v___f_779_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
lean_object* runtime_initialize_Init_Grind_Ring_CommSemiringAdapter(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Poly(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Grind_Ring_CommSemiringAdapter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_Poly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof = _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof);
l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstr = _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstr();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstr);
l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default = _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default);
l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState = _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState);
l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default = _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default);
l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState = _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState);
l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default = _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default);
l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState = _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState);
l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default = _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default);
l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState = _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState);
res = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_Arith_CommRing_ringExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_ringExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Ring_CommSemiringAdapter(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Arith_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Arith_Poly(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Ring_CommSemiringAdapter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Arith_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Arith_Poly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(builtin);
}
#ifdef __cplusplus
}
#endif
