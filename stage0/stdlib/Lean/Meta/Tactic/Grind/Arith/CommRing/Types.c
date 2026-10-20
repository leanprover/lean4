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
lean_object* lean_obj_tag_nat(lean_object*);
extern lean_object* l_Lean_Grind_CommRing_instInhabitedExpr_default;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Grind_CommRing_instInhabitedPoly_default;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_degree(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
switch(lean_obj_tag(v_t_5_))
{
case 0:
{
lean_object* v_a_7_; lean_object* v_b_8_; lean_object* v_ra_9_; lean_object* v_rb_10_; lean_object* v___x_11_; 
v_a_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_a_7_);
v_b_8_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_b_8_);
v_ra_9_ = lean_ctor_get(v_t_5_, 2);
lean_inc_ref(v_ra_9_);
v_rb_10_ = lean_ctor_get(v_t_5_, 3);
lean_inc_ref(v_rb_10_);
lean_dec_ref_known(v_t_5_, 4);
v___x_11_ = lean_apply_4(v_k_6_, v_a_7_, v_b_8_, v_ra_9_, v_rb_10_);
return v___x_11_;
}
case 1:
{
lean_object* v_a_12_; lean_object* v_b_13_; lean_object* v_sa_14_; lean_object* v_sb_15_; lean_object* v_ra_16_; lean_object* v_rb_17_; lean_object* v___x_18_; 
v_a_12_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_a_12_);
v_b_13_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_b_13_);
v_sa_14_ = lean_ctor_get(v_t_5_, 2);
lean_inc_ref(v_sa_14_);
v_sb_15_ = lean_ctor_get(v_t_5_, 3);
lean_inc_ref(v_sb_15_);
v_ra_16_ = lean_ctor_get(v_t_5_, 4);
lean_inc_ref(v_ra_16_);
v_rb_17_ = lean_ctor_get(v_t_5_, 5);
lean_inc_ref(v_rb_17_);
lean_dec_ref_known(v_t_5_, 6);
v___x_18_ = lean_apply_6(v_k_6_, v_a_12_, v_b_13_, v_sa_14_, v_sb_15_, v_ra_16_, v_rb_17_);
return v___x_18_;
}
case 2:
{
lean_object* v_k_u2081_19_; lean_object* v_m_u2081_20_; lean_object* v_c_u2081_21_; lean_object* v_k_u2082_22_; lean_object* v_m_u2082_23_; lean_object* v_c_u2082_24_; lean_object* v___x_25_; 
v_k_u2081_19_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_k_u2081_19_);
v_m_u2081_20_ = lean_ctor_get(v_t_5_, 1);
lean_inc(v_m_u2081_20_);
v_c_u2081_21_ = lean_ctor_get(v_t_5_, 2);
lean_inc_ref(v_c_u2081_21_);
v_k_u2082_22_ = lean_ctor_get(v_t_5_, 3);
lean_inc(v_k_u2082_22_);
v_m_u2082_23_ = lean_ctor_get(v_t_5_, 4);
lean_inc(v_m_u2082_23_);
v_c_u2082_24_ = lean_ctor_get(v_t_5_, 5);
lean_inc_ref(v_c_u2082_24_);
lean_dec_ref_known(v_t_5_, 6);
v___x_25_ = lean_apply_6(v_k_6_, v_k_u2081_19_, v_m_u2081_20_, v_c_u2081_21_, v_k_u2082_22_, v_m_u2082_23_, v_c_u2082_24_);
return v___x_25_;
}
case 3:
{
lean_object* v_k_u2081_26_; lean_object* v_c_u2081_27_; lean_object* v_k_u2082_28_; lean_object* v_m_u2082_29_; lean_object* v_c_u2082_30_; lean_object* v___x_31_; 
v_k_u2081_26_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_k_u2081_26_);
v_c_u2081_27_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_c_u2081_27_);
v_k_u2082_28_ = lean_ctor_get(v_t_5_, 2);
lean_inc(v_k_u2082_28_);
v_m_u2082_29_ = lean_ctor_get(v_t_5_, 3);
lean_inc(v_m_u2082_29_);
v_c_u2082_30_ = lean_ctor_get(v_t_5_, 4);
lean_inc_ref(v_c_u2082_30_);
lean_dec_ref_known(v_t_5_, 5);
v___x_31_ = lean_apply_5(v_k_6_, v_k_u2081_26_, v_c_u2081_27_, v_k_u2082_28_, v_m_u2082_29_, v_c_u2082_30_);
return v___x_31_;
}
case 6:
{
lean_object* v_a_32_; lean_object* v_b_33_; lean_object* v_c_u2081_34_; lean_object* v_c_u2082_35_; lean_object* v___x_36_; 
v_a_32_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_a_32_);
v_b_33_ = lean_ctor_get(v_t_5_, 1);
lean_inc(v_b_33_);
v_c_u2081_34_ = lean_ctor_get(v_t_5_, 2);
lean_inc_ref(v_c_u2081_34_);
v_c_u2082_35_ = lean_ctor_get(v_t_5_, 3);
lean_inc_ref(v_c_u2082_35_);
lean_dec_ref_known(v_t_5_, 4);
v___x_36_ = lean_apply_4(v_k_6_, v_a_32_, v_b_33_, v_c_u2081_34_, v_c_u2082_35_);
return v___x_36_;
}
case 7:
{
lean_object* v_k_37_; lean_object* v_c_u2081_38_; lean_object* v_c_u2082_39_; lean_object* v___x_40_; 
v_k_37_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_k_37_);
v_c_u2081_38_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_c_u2081_38_);
v_c_u2082_39_ = lean_ctor_get(v_t_5_, 2);
lean_inc_ref(v_c_u2082_39_);
lean_dec_ref_known(v_t_5_, 3);
v___x_40_ = lean_apply_3(v_k_6_, v_k_37_, v_c_u2081_38_, v_c_u2082_39_);
return v___x_40_;
}
default: 
{
lean_object* v_k_41_; lean_object* v_e_42_; lean_object* v___x_43_; 
v_k_41_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_k_41_);
v_e_42_ = lean_ctor_get(v_t_5_, 1);
lean_inc_ref(v_e_42_);
lean_dec_ref(v_t_5_);
v___x_43_ = lean_apply_2(v_k_6_, v_k_41_, v_e_42_);
return v___x_43_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim(lean_object* v_motive__2_44_, lean_object* v_ctorIdx_45_, lean_object* v_t_46_, lean_object* v_h_47_, lean_object* v_k_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_46_, v_k_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___boxed(lean_object* v_motive__2_50_, lean_object* v_ctorIdx_51_, lean_object* v_t_52_, lean_object* v_h_53_, lean_object* v_k_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim(v_motive__2_50_, v_ctorIdx_51_, v_t_52_, v_h_53_, v_k_54_);
lean_dec(v_ctorIdx_51_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_core_elim___redArg(lean_object* v_t_56_, lean_object* v_core_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_56_, v_core_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_core_elim(lean_object* v_motive__2_59_, lean_object* v_t_60_, lean_object* v_h_61_, lean_object* v_core_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_60_, v_core_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_coreS_elim___redArg(lean_object* v_t_64_, lean_object* v_coreS_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_64_, v_coreS_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_coreS_elim(lean_object* v_motive__2_67_, lean_object* v_t_68_, lean_object* v_h_69_, lean_object* v_coreS_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_68_, v_coreS_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_superpose_elim___redArg(lean_object* v_t_72_, lean_object* v_superpose_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_72_, v_superpose_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_superpose_elim(lean_object* v_motive__2_75_, lean_object* v_t_76_, lean_object* v_h_77_, lean_object* v_superpose_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_76_, v_superpose_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_simp_elim___redArg(lean_object* v_t_80_, lean_object* v_simp_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_80_, v_simp_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_simp_elim(lean_object* v_motive__2_83_, lean_object* v_t_84_, lean_object* v_h_85_, lean_object* v_simp_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_84_, v_simp_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_mul_elim___redArg(lean_object* v_t_88_, lean_object* v_mul_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_88_, v_mul_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_mul_elim(lean_object* v_motive__2_91_, lean_object* v_t_92_, lean_object* v_h_93_, lean_object* v_mul_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_92_, v_mul_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_div_elim___redArg(lean_object* v_t_96_, lean_object* v_div_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_96_, v_div_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_div_elim(lean_object* v_motive__2_99_, lean_object* v_t_100_, lean_object* v_h_101_, lean_object* v_div_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_100_, v_div_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_gcd_elim___redArg(lean_object* v_t_104_, lean_object* v_gcd_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_104_, v_gcd_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_gcd_elim(lean_object* v_motive__2_107_, lean_object* v_t_108_, lean_object* v_h_109_, lean_object* v_gcd_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_108_, v_gcd_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_numEq0_elim___redArg(lean_object* v_t_112_, lean_object* v_numEq0_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_112_, v_numEq0_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_numEq0_elim(lean_object* v_motive__2_115_, lean_object* v_t_116_, lean_object* v_h_117_, lean_object* v_numEq0_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstrProof_ctorElim___redArg(v_t_116_, v_numEq0_118_);
return v___x_119_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__2(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_123_ = lean_box(0);
v___x_124_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__1));
v___x_125_ = l_Lean_Expr_const___override(v___x_124_, v___x_123_);
return v___x_125_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__3(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_126_ = l_Lean_Grind_CommRing_instInhabitedExpr_default;
v___x_127_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__2);
v___x_128_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v___x_127_);
lean_ctor_set(v___x_128_, 2, v___x_126_);
lean_ctor_set(v___x_128_, 3, v___x_126_);
return v___x_128_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof(void){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__3, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__3_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__3);
return v___x_129_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstr___closed__0(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_130_ = lean_unsigned_to_nat(0u);
v___x_131_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__3, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__3_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstrProof___closed__3);
v___x_132_ = l_Lean_Grind_CommRing_instInhabitedPoly_default;
v___x_133_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
lean_ctor_set(v___x_133_, 1, v___x_131_);
lean_ctor_set(v___x_133_, 2, v___x_130_);
lean_ctor_set(v___x_133_, 3, v___x_130_);
return v___x_133_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstr(void){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstr___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstr___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedEqCnstr___closed__0);
return v___x_134_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare(lean_object* v_c_u2081_135_, lean_object* v_c_u2082_136_){
_start:
{
lean_object* v_p_137_; lean_object* v_sugar_138_; lean_object* v_id_139_; lean_object* v_p_140_; lean_object* v_sugar_141_; lean_object* v_id_142_; uint8_t v___x_143_; 
v_p_137_ = lean_ctor_get(v_c_u2081_135_, 0);
v_sugar_138_ = lean_ctor_get(v_c_u2081_135_, 2);
v_id_139_ = lean_ctor_get(v_c_u2081_135_, 3);
v_p_140_ = lean_ctor_get(v_c_u2082_136_, 0);
v_sugar_141_ = lean_ctor_get(v_c_u2082_136_, 2);
v_id_142_ = lean_ctor_get(v_c_u2082_136_, 3);
v___x_143_ = lean_nat_dec_lt(v_sugar_138_, v_sugar_141_);
if (v___x_143_ == 0)
{
uint8_t v___x_144_; 
v___x_144_ = lean_nat_dec_eq(v_sugar_138_, v_sugar_141_);
if (v___x_144_ == 0)
{
uint8_t v___x_145_; 
v___x_145_ = 2;
return v___x_145_;
}
else
{
lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_146_ = l_Lean_Grind_CommRing_Poly_degree(v_p_137_);
v___x_147_ = l_Lean_Grind_CommRing_Poly_degree(v_p_140_);
v___x_148_ = lean_nat_dec_lt(v___x_146_, v___x_147_);
if (v___x_148_ == 0)
{
uint8_t v___x_149_; 
v___x_149_ = lean_nat_dec_eq(v___x_146_, v___x_147_);
lean_dec(v___x_147_);
lean_dec(v___x_146_);
if (v___x_149_ == 0)
{
uint8_t v___x_150_; 
v___x_150_ = 2;
return v___x_150_;
}
else
{
uint8_t v___x_151_; 
v___x_151_ = lean_nat_dec_lt(v_id_139_, v_id_142_);
if (v___x_151_ == 0)
{
uint8_t v___x_152_; 
v___x_152_ = lean_nat_dec_eq(v_id_139_, v_id_142_);
if (v___x_152_ == 0)
{
uint8_t v___x_153_; 
v___x_153_ = 2;
return v___x_153_;
}
else
{
uint8_t v___x_154_; 
v___x_154_ = 1;
return v___x_154_;
}
}
else
{
uint8_t v___x_155_; 
v___x_155_ = 0;
return v___x_155_;
}
}
}
else
{
uint8_t v___x_156_; 
lean_dec(v___x_147_);
lean_dec(v___x_146_);
v___x_156_ = 0;
return v___x_156_;
}
}
}
else
{
uint8_t v___x_157_; 
v___x_157_ = 0;
return v___x_157_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare___boxed(lean_object* v_c_u2081_158_, lean_object* v_c_u2082_159_){
_start:
{
uint8_t v_res_160_; lean_object* v_r_161_; 
v_res_160_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare(v_c_u2081_158_, v_c_u2082_159_);
lean_dec_ref(v_c_u2082_159_);
lean_dec_ref(v_c_u2081_158_);
v_r_161_ = lean_box(v_res_160_);
return v_r_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorIdx___impl(lean_object* v_x_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = lean_obj_tag_nat(v_x_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorIdx___impl___boxed(lean_object* v_x_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorIdx___impl(v_x_164_);
lean_dec_ref(v_x_164_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim___redArg(lean_object* v_t_166_, lean_object* v_k_167_){
_start:
{
switch(lean_obj_tag(v_t_166_))
{
case 0:
{
lean_object* v_p_168_; lean_object* v___x_169_; 
v_p_168_ = lean_ctor_get(v_t_166_, 0);
lean_inc_ref(v_p_168_);
lean_dec_ref_known(v_t_166_, 1);
v___x_169_ = lean_apply_1(v_k_167_, v_p_168_);
return v___x_169_;
}
case 1:
{
lean_object* v_p_170_; lean_object* v_k_u2081_171_; lean_object* v_d_172_; lean_object* v_k_u2082_173_; lean_object* v_m_u2082_174_; lean_object* v_c_175_; lean_object* v___x_176_; 
v_p_170_ = lean_ctor_get(v_t_166_, 0);
lean_inc_ref(v_p_170_);
v_k_u2081_171_ = lean_ctor_get(v_t_166_, 1);
lean_inc(v_k_u2081_171_);
v_d_172_ = lean_ctor_get(v_t_166_, 2);
lean_inc_ref(v_d_172_);
v_k_u2082_173_ = lean_ctor_get(v_t_166_, 3);
lean_inc(v_k_u2082_173_);
v_m_u2082_174_ = lean_ctor_get(v_t_166_, 4);
lean_inc(v_m_u2082_174_);
v_c_175_ = lean_ctor_get(v_t_166_, 5);
lean_inc_ref(v_c_175_);
lean_dec_ref_known(v_t_166_, 6);
v___x_176_ = lean_apply_6(v_k_167_, v_p_170_, v_k_u2081_171_, v_d_172_, v_k_u2082_173_, v_m_u2082_174_, v_c_175_);
return v___x_176_;
}
default: 
{
lean_object* v_p_177_; lean_object* v_d_178_; lean_object* v_c_179_; lean_object* v___x_180_; 
v_p_177_ = lean_ctor_get(v_t_166_, 0);
lean_inc_ref(v_p_177_);
v_d_178_ = lean_ctor_get(v_t_166_, 1);
lean_inc_ref(v_d_178_);
v_c_179_ = lean_ctor_get(v_t_166_, 2);
lean_inc_ref(v_c_179_);
lean_dec_ref_known(v_t_166_, 3);
v___x_180_ = lean_apply_3(v_k_167_, v_p_177_, v_d_178_, v_c_179_);
return v___x_180_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim(lean_object* v_motive_181_, lean_object* v_ctorIdx_182_, lean_object* v_t_183_, lean_object* v_h_184_, lean_object* v_k_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim___redArg(v_t_183_, v_k_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim___boxed(lean_object* v_motive_187_, lean_object* v_ctorIdx_188_, lean_object* v_t_189_, lean_object* v_h_190_, lean_object* v_k_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim(v_motive_187_, v_ctorIdx_188_, v_t_189_, v_h_190_, v_k_191_);
lean_dec(v_ctorIdx_188_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_input_elim___redArg(lean_object* v_t_193_, lean_object* v_input_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim___redArg(v_t_193_, v_input_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_input_elim(lean_object* v_motive_196_, lean_object* v_t_197_, lean_object* v_h_198_, lean_object* v_input_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim___redArg(v_t_197_, v_input_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_step_elim___redArg(lean_object* v_t_201_, lean_object* v_step_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim___redArg(v_t_201_, v_step_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_step_elim(lean_object* v_motive_204_, lean_object* v_t_205_, lean_object* v_h_206_, lean_object* v_step_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim___redArg(v_t_205_, v_step_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_normEq0_elim___redArg(lean_object* v_t_209_, lean_object* v_normEq0_210_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim___redArg(v_t_209_, v_normEq0_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_normEq0_elim(lean_object* v_motive_212_, lean_object* v_t_213_, lean_object* v_h_214_, lean_object* v_normEq0_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim___redArg(v_t_213_, v_normEq0_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_p(lean_object* v_x_217_){
_start:
{
lean_object* v_p_218_; 
v_p_218_ = lean_ctor_get(v_x_217_, 0);
lean_inc_ref(v_p_218_);
return v_p_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_p___boxed(lean_object* v_x_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_p(v_x_219_);
lean_dec_ref(v_x_219_);
return v_res_220_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__0(void){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_221_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__1(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__0);
v___x_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
return v___x_223_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__2(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_224_ = lean_unsigned_to_nat(32u);
v___x_225_ = lean_mk_empty_array_with_capacity(v___x_224_);
v___x_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
return v___x_226_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__3(void){
_start:
{
size_t v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_227_ = ((size_t)5ULL);
v___x_228_ = lean_unsigned_to_nat(0u);
v___x_229_ = lean_unsigned_to_nat(32u);
v___x_230_ = lean_mk_empty_array_with_capacity(v___x_229_);
v___x_231_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__2);
v___x_232_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_232_, 0, v___x_231_);
lean_ctor_set(v___x_232_, 1, v___x_230_);
lean_ctor_set(v___x_232_, 2, v___x_228_);
lean_ctor_set(v___x_232_, 3, v___x_228_);
lean_ctor_set_usize(v___x_232_, 4, v___x_227_);
return v___x_232_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__4(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_233_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__3, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__3_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__3);
v___x_234_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__1);
v___x_235_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
lean_ctor_set(v___x_235_, 1, v___x_233_);
lean_ctor_set(v___x_235_, 2, v___x_234_);
return v___x_235_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default(void){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__4, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__4_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__4);
return v___x_236_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState(void){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default;
return v___x_237_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__0(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__0);
v___x_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
return v___x_239_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__1(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_240_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__0);
v___x_241_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__3, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__3_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__3);
v___x_242_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
lean_ctor_set(v___x_242_, 1, v___x_240_);
lean_ctor_set(v___x_242_, 2, v___x_240_);
return v___x_242_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default(void){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__1);
return v___x_243_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState(void){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default;
return v___x_244_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__0);
v___x_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___redArg(){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___redArg___closed__0);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___redArg___boxed(lean_object* v___dummy_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___redArg();
return v_res_250_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___redArg();
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0(lean_object* v_00_u03b2_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___closed__0);
return v___x_253_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__0(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_254_ = lean_unsigned_to_nat(32u);
v___x_255_ = lean_mk_empty_array_with_capacity(v___x_254_);
v___x_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
return v___x_256_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__1(void){
_start:
{
size_t v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_257_ = ((size_t)5ULL);
v___x_258_ = lean_unsigned_to_nat(0u);
v___x_259_ = lean_unsigned_to_nat(32u);
v___x_260_ = lean_mk_empty_array_with_capacity(v___x_259_);
v___x_261_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__0);
v___x_262_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_262_, 0, v___x_261_);
lean_ctor_set(v___x_262_, 1, v___x_260_);
lean_ctor_set(v___x_262_, 2, v___x_258_);
lean_ctor_set(v___x_262_, 3, v___x_258_);
lean_ctor_set_usize(v___x_262_, 4, v___x_257_);
return v___x_262_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__2(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_263_ = lean_box(0);
v___x_264_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___closed__0);
v___x_265_ = 0;
v___x_266_ = lean_box(0);
v___x_267_ = lean_box(1);
v___x_268_ = lean_unsigned_to_nat(0u);
v___x_269_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__1);
v___x_270_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default;
v___x_271_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_271_, 0, v___x_270_);
lean_ctor_set(v___x_271_, 1, v___x_269_);
lean_ctor_set(v___x_271_, 2, v___x_268_);
lean_ctor_set(v___x_271_, 3, v___x_268_);
lean_ctor_set(v___x_271_, 4, v___x_267_);
lean_ctor_set(v___x_271_, 5, v___x_266_);
lean_ctor_set(v___x_271_, 6, v___x_269_);
lean_ctor_set(v___x_271_, 7, v___x_264_);
lean_ctor_set(v___x_271_, 8, v___x_268_);
lean_ctor_set(v___x_271_, 9, v___x_263_);
lean_ctor_set_uint8(v___x_271_, sizeof(void*)*10, v___x_265_);
lean_ctor_set_uint8(v___x_271_, sizeof(void*)*10 + 1, v___x_265_);
return v___x_271_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default(void){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__2);
return v___x_272_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState(void){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default;
return v___x_273_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__1(void){
_start:
{
uint8_t v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_276_ = 0;
v___x_277_ = lean_unsigned_to_nat(0u);
v___x_278_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__0);
v___x_279_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__0));
v___x_280_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_280_, 0, v___x_279_);
lean_ctor_set(v___x_280_, 1, v___x_278_);
lean_ctor_set(v___x_280_, 2, v___x_279_);
lean_ctor_set(v___x_280_, 3, v___x_278_);
lean_ctor_set(v___x_280_, 4, v___x_279_);
lean_ctor_set(v___x_280_, 5, v___x_278_);
lean_ctor_set(v___x_280_, 6, v___x_279_);
lean_ctor_set(v___x_280_, 7, v___x_278_);
lean_ctor_set(v___x_280_, 8, v___x_277_);
lean_ctor_set_uint8(v___x_280_, sizeof(void*)*9, v___x_276_);
return v___x_280_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default(void){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__1);
return v___x_281_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState(void){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default;
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2_(lean_object* v___x_283_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_283_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2____boxed(lean_object* v___x_286_, lean_object* v___y_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2_(v___x_286_);
return v_res_288_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_289_; lean_object* v___f_290_; 
v___x_289_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__1);
v___f_290_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_290_, 0, v___x_289_);
return v___f_290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_292_; lean_object* v___x_293_; 
v___f_292_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2_);
v___x_293_ = l_Lean_Meta_Grind_registerSolverExtension___redArg(v___f_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2____boxed(lean_object* v_a_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2_();
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(lean_object* v_a_296_, lean_object* v_a_297_){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_300_ = l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_299_, v_a_296_, v_a_297_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg___boxed(lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_301_, v_a_302_);
lean_dec_ref(v_a_302_);
lean_dec(v_a_301_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_get_x27(lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_305_, v_a_313_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_get_x27___boxed(lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27(v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
lean_dec(v_a_326_);
lean_dec_ref(v_a_325_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
lean_dec(v_a_322_);
lean_dec_ref(v_a_321_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec(v_a_317_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_modify_x27___redArg(lean_object* v_f_329_, lean_object* v_a_330_){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_333_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_332_, v_f_329_, v_a_330_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_modify_x27___redArg___boxed(lean_object* v_f_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_Meta_Grind_Arith_CommRing_modify_x27___redArg(v_f_334_, v_a_335_);
lean_dec(v_a_335_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_modify_x27(lean_object* v_f_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_351_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_350_, v_f_338_, v_a_339_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_modify_x27___boxed(lean_object* v_f_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_Meta_Grind_Arith_CommRing_modify_x27(v_f_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_);
lean_dec(v_a_362_);
lean_dec_ref(v_a_361_);
lean_dec(v_a_360_);
lean_dec_ref(v_a_359_);
lean_dec(v_a_358_);
lean_dec_ref(v_a_357_);
lean_dec(v_a_356_);
lean_dec_ref(v_a_355_);
lean_dec(v_a_354_);
lean_dec(v_a_353_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_padAndModify___redArg(lean_object* v_inst_365_, lean_object* v_a_366_, lean_object* v_i_367_, lean_object* v_f_368_){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_369_ = lean_unsigned_to_nat(1u);
v___x_370_ = lean_nat_add(v_i_367_, v___x_369_);
v___x_371_ = l_Array_rightpad___redArg(v___x_370_, v_inst_365_, v_a_366_);
lean_dec(v___x_370_);
v___x_372_ = lean_array_get_size(v___x_371_);
v___x_373_ = lean_nat_dec_lt(v_i_367_, v___x_372_);
if (v___x_373_ == 0)
{
lean_dec(v_f_368_);
return v___x_371_;
}
else
{
lean_object* v_v_374_; lean_object* v___x_375_; lean_object* v_xs_x27_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v_v_374_ = lean_array_fget(v___x_371_, v_i_367_);
v___x_375_ = lean_box(0);
v_xs_x27_376_ = lean_array_fset(v___x_371_, v_i_367_, v___x_375_);
v___x_377_ = lean_apply_1(v_f_368_, v_v_374_);
v___x_378_ = lean_array_fset(v_xs_x27_376_, v_i_367_, v___x_377_);
return v___x_378_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_padAndModify___redArg___boxed(lean_object* v_inst_379_, lean_object* v_a_380_, lean_object* v_i_381_, lean_object* v_f_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_padAndModify___redArg(v_inst_379_, v_a_380_, v_i_381_, v_f_382_);
lean_dec(v_i_381_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_padAndModify(lean_object* v_00_u03b1_384_, lean_object* v_inst_385_, lean_object* v_a_386_, lean_object* v_i_387_, lean_object* v_f_388_){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_389_ = lean_unsigned_to_nat(1u);
v___x_390_ = lean_nat_add(v_i_387_, v___x_389_);
v___x_391_ = l_Array_rightpad___redArg(v___x_390_, v_inst_385_, v_a_386_);
lean_dec(v___x_390_);
v___x_392_ = lean_array_get_size(v___x_391_);
v___x_393_ = lean_nat_dec_lt(v_i_387_, v___x_392_);
if (v___x_393_ == 0)
{
lean_dec(v_f_388_);
return v___x_391_;
}
else
{
lean_object* v_v_394_; lean_object* v___x_395_; lean_object* v_xs_x27_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v_v_394_ = lean_array_fget(v___x_391_, v_i_387_);
v___x_395_ = lean_box(0);
v_xs_x27_396_ = lean_array_fset(v___x_391_, v_i_387_, v___x_395_);
v___x_397_ = lean_apply_1(v_f_388_, v_v_394_);
v___x_398_ = lean_array_fset(v_xs_x27_396_, v_i_387_, v___x_397_);
return v___x_398_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_padAndModify___boxed(lean_object* v_00_u03b1_399_, lean_object* v_inst_400_, lean_object* v_a_401_, lean_object* v_i_402_, lean_object* v_f_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_padAndModify(v_00_u03b1_399_, v_inst_400_, v_a_401_, v_i_402_, v_f_403_);
lean_dec(v_i_402_);
return v_res_404_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_State_getRing___closed__0(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; uint8_t v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_405_ = lean_box(0);
v___x_406_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___closed__0);
v___x_407_ = 0;
v___x_408_ = lean_box(0);
v___x_409_ = lean_box(1);
v___x_410_ = lean_unsigned_to_nat(0u);
v___x_411_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__3, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__3_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__3);
v___x_412_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__1);
v___x_413_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_413_, 0, v___x_412_);
lean_ctor_set(v___x_413_, 1, v___x_411_);
lean_ctor_set(v___x_413_, 2, v___x_410_);
lean_ctor_set(v___x_413_, 3, v___x_410_);
lean_ctor_set(v___x_413_, 4, v___x_409_);
lean_ctor_set(v___x_413_, 5, v___x_408_);
lean_ctor_set(v___x_413_, 6, v___x_411_);
lean_ctor_set(v___x_413_, 7, v___x_406_);
lean_ctor_set(v___x_413_, 8, v___x_410_);
lean_ctor_set(v___x_413_, 9, v___x_405_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*10, v___x_407_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*10 + 1, v___x_407_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_getRing(lean_object* v_s_414_, lean_object* v_ringId_415_){
_start:
{
lean_object* v_rings_416_; lean_object* v___x_417_; lean_object* v___x_418_; uint8_t v___x_419_; 
v_rings_416_ = lean_ctor_get(v_s_414_, 0);
v___x_417_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_State_getRing___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_State_getRing___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_State_getRing___closed__0);
v___x_418_ = lean_array_get_size(v_rings_416_);
v___x_419_ = lean_nat_dec_lt(v_ringId_415_, v___x_418_);
if (v___x_419_ == 0)
{
return v___x_417_;
}
else
{
lean_object* v___x_420_; 
v___x_420_ = lean_array_fget_borrowed(v_rings_416_, v_ringId_415_);
lean_inc(v___x_420_);
return v___x_420_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_getRing___boxed(lean_object* v_s_421_, lean_object* v_ringId_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lean_Meta_Grind_Arith_CommRing_State_getRing(v_s_421_, v_ringId_422_);
lean_dec(v_ringId_422_);
lean_dec_ref(v_s_421_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_modifyRing(lean_object* v_s_424_, lean_object* v_ringId_425_, lean_object* v_f_426_){
_start:
{
lean_object* v_rings_427_; lean_object* v_exprToRingId_428_; lean_object* v_semirings_429_; lean_object* v_exprToSemiringId_430_; lean_object* v_ncRings_431_; lean_object* v_exprToNCRingId_432_; lean_object* v_ncSemirings_433_; lean_object* v_exprToNCSemiringId_434_; lean_object* v_steps_435_; uint8_t v_reportedMaxDegreeIssue_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_457_; 
v_rings_427_ = lean_ctor_get(v_s_424_, 0);
v_exprToRingId_428_ = lean_ctor_get(v_s_424_, 1);
v_semirings_429_ = lean_ctor_get(v_s_424_, 2);
v_exprToSemiringId_430_ = lean_ctor_get(v_s_424_, 3);
v_ncRings_431_ = lean_ctor_get(v_s_424_, 4);
v_exprToNCRingId_432_ = lean_ctor_get(v_s_424_, 5);
v_ncSemirings_433_ = lean_ctor_get(v_s_424_, 6);
v_exprToNCSemiringId_434_ = lean_ctor_get(v_s_424_, 7);
v_steps_435_ = lean_ctor_get(v_s_424_, 8);
v_reportedMaxDegreeIssue_436_ = lean_ctor_get_uint8(v_s_424_, sizeof(void*)*9);
v_isSharedCheck_457_ = !lean_is_exclusive(v_s_424_);
if (v_isSharedCheck_457_ == 0)
{
v___x_438_ = v_s_424_;
v_isShared_439_ = v_isSharedCheck_457_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_steps_435_);
lean_inc(v_exprToNCSemiringId_434_);
lean_inc(v_ncSemirings_433_);
lean_inc(v_exprToNCRingId_432_);
lean_inc(v_ncRings_431_);
lean_inc(v_exprToSemiringId_430_);
lean_inc(v_semirings_429_);
lean_inc(v_exprToRingId_428_);
lean_inc(v_rings_427_);
lean_dec(v_s_424_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_457_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_440_ = lean_unsigned_to_nat(1u);
v___x_441_ = lean_nat_add(v_ringId_425_, v___x_440_);
v___x_442_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default;
v___x_443_ = l_Array_rightpad___redArg(v___x_441_, v___x_442_, v_rings_427_);
lean_dec(v___x_441_);
v___x_444_ = lean_array_get_size(v___x_443_);
v___x_445_ = lean_nat_dec_lt(v_ringId_425_, v___x_444_);
if (v___x_445_ == 0)
{
lean_object* v___x_447_; 
lean_dec_ref(v_f_426_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 0, v___x_443_);
v___x_447_ = v___x_438_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_443_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v_exprToRingId_428_);
lean_ctor_set(v_reuseFailAlloc_448_, 2, v_semirings_429_);
lean_ctor_set(v_reuseFailAlloc_448_, 3, v_exprToSemiringId_430_);
lean_ctor_set(v_reuseFailAlloc_448_, 4, v_ncRings_431_);
lean_ctor_set(v_reuseFailAlloc_448_, 5, v_exprToNCRingId_432_);
lean_ctor_set(v_reuseFailAlloc_448_, 6, v_ncSemirings_433_);
lean_ctor_set(v_reuseFailAlloc_448_, 7, v_exprToNCSemiringId_434_);
lean_ctor_set(v_reuseFailAlloc_448_, 8, v_steps_435_);
lean_ctor_set_uint8(v_reuseFailAlloc_448_, sizeof(void*)*9, v_reportedMaxDegreeIssue_436_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
else
{
lean_object* v_v_449_; lean_object* v___x_450_; lean_object* v_xs_x27_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_455_; 
v_v_449_ = lean_array_fget(v___x_443_, v_ringId_425_);
v___x_450_ = lean_box(0);
v_xs_x27_451_ = lean_array_fset(v___x_443_, v_ringId_425_, v___x_450_);
v___x_452_ = lean_apply_1(v_f_426_, v_v_449_);
v___x_453_ = lean_array_fset(v_xs_x27_451_, v_ringId_425_, v___x_452_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 0, v___x_453_);
v___x_455_ = v___x_438_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_453_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v_exprToRingId_428_);
lean_ctor_set(v_reuseFailAlloc_456_, 2, v_semirings_429_);
lean_ctor_set(v_reuseFailAlloc_456_, 3, v_exprToSemiringId_430_);
lean_ctor_set(v_reuseFailAlloc_456_, 4, v_ncRings_431_);
lean_ctor_set(v_reuseFailAlloc_456_, 5, v_exprToNCRingId_432_);
lean_ctor_set(v_reuseFailAlloc_456_, 6, v_ncSemirings_433_);
lean_ctor_set(v_reuseFailAlloc_456_, 7, v_exprToNCSemiringId_434_);
lean_ctor_set(v_reuseFailAlloc_456_, 8, v_steps_435_);
lean_ctor_set_uint8(v_reuseFailAlloc_456_, sizeof(void*)*9, v_reportedMaxDegreeIssue_436_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_modifyRing___boxed(lean_object* v_s_458_, lean_object* v_ringId_459_, lean_object* v_f_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lean_Meta_Grind_Arith_CommRing_State_modifyRing(v_s_458_, v_ringId_459_, v_f_460_);
lean_dec(v_ringId_459_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_getSemiring(lean_object* v_s_462_, lean_object* v_semiringId_463_){
_start:
{
lean_object* v_semirings_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; uint8_t v___x_468_; 
v_semirings_464_ = lean_ctor_get(v_s_462_, 2);
v___x_465_ = lean_unsigned_to_nat(32u);
v___x_466_ = lean_mk_empty_array_with_capacity(v___x_465_);
lean_dec_ref(v___x_466_);
v___x_467_ = lean_array_get_size(v_semirings_464_);
v___x_468_ = lean_nat_dec_lt(v_semiringId_463_, v___x_467_);
if (v___x_468_ == 0)
{
lean_object* v___x_469_; 
v___x_469_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__4, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__4_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__4);
return v___x_469_;
}
else
{
lean_object* v___x_470_; 
v___x_470_ = lean_array_fget_borrowed(v_semirings_464_, v_semiringId_463_);
lean_inc(v___x_470_);
return v___x_470_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_getSemiring___boxed(lean_object* v_s_471_, lean_object* v_semiringId_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lean_Meta_Grind_Arith_CommRing_State_getSemiring(v_s_471_, v_semiringId_472_);
lean_dec(v_semiringId_472_);
lean_dec_ref(v_s_471_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_modifySemiring(lean_object* v_s_474_, lean_object* v_semiringId_475_, lean_object* v_f_476_){
_start:
{
lean_object* v_rings_477_; lean_object* v_exprToRingId_478_; lean_object* v_semirings_479_; lean_object* v_exprToSemiringId_480_; lean_object* v_ncRings_481_; lean_object* v_exprToNCRingId_482_; lean_object* v_ncSemirings_483_; lean_object* v_exprToNCSemiringId_484_; lean_object* v_steps_485_; uint8_t v_reportedMaxDegreeIssue_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_507_; 
v_rings_477_ = lean_ctor_get(v_s_474_, 0);
v_exprToRingId_478_ = lean_ctor_get(v_s_474_, 1);
v_semirings_479_ = lean_ctor_get(v_s_474_, 2);
v_exprToSemiringId_480_ = lean_ctor_get(v_s_474_, 3);
v_ncRings_481_ = lean_ctor_get(v_s_474_, 4);
v_exprToNCRingId_482_ = lean_ctor_get(v_s_474_, 5);
v_ncSemirings_483_ = lean_ctor_get(v_s_474_, 6);
v_exprToNCSemiringId_484_ = lean_ctor_get(v_s_474_, 7);
v_steps_485_ = lean_ctor_get(v_s_474_, 8);
v_reportedMaxDegreeIssue_486_ = lean_ctor_get_uint8(v_s_474_, sizeof(void*)*9);
v_isSharedCheck_507_ = !lean_is_exclusive(v_s_474_);
if (v_isSharedCheck_507_ == 0)
{
v___x_488_ = v_s_474_;
v_isShared_489_ = v_isSharedCheck_507_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_steps_485_);
lean_inc(v_exprToNCSemiringId_484_);
lean_inc(v_ncSemirings_483_);
lean_inc(v_exprToNCRingId_482_);
lean_inc(v_ncRings_481_);
lean_inc(v_exprToSemiringId_480_);
lean_inc(v_semirings_479_);
lean_inc(v_exprToRingId_478_);
lean_inc(v_rings_477_);
lean_dec(v_s_474_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_507_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; uint8_t v___x_495_; 
v___x_490_ = lean_unsigned_to_nat(1u);
v___x_491_ = lean_nat_add(v_semiringId_475_, v___x_490_);
v___x_492_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default;
v___x_493_ = l_Array_rightpad___redArg(v___x_491_, v___x_492_, v_semirings_479_);
lean_dec(v___x_491_);
v___x_494_ = lean_array_get_size(v___x_493_);
v___x_495_ = lean_nat_dec_lt(v_semiringId_475_, v___x_494_);
if (v___x_495_ == 0)
{
lean_object* v___x_497_; 
lean_dec_ref(v_f_476_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 2, v___x_493_);
v___x_497_ = v___x_488_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_rings_477_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v_exprToRingId_478_);
lean_ctor_set(v_reuseFailAlloc_498_, 2, v___x_493_);
lean_ctor_set(v_reuseFailAlloc_498_, 3, v_exprToSemiringId_480_);
lean_ctor_set(v_reuseFailAlloc_498_, 4, v_ncRings_481_);
lean_ctor_set(v_reuseFailAlloc_498_, 5, v_exprToNCRingId_482_);
lean_ctor_set(v_reuseFailAlloc_498_, 6, v_ncSemirings_483_);
lean_ctor_set(v_reuseFailAlloc_498_, 7, v_exprToNCSemiringId_484_);
lean_ctor_set(v_reuseFailAlloc_498_, 8, v_steps_485_);
lean_ctor_set_uint8(v_reuseFailAlloc_498_, sizeof(void*)*9, v_reportedMaxDegreeIssue_486_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
else
{
lean_object* v_v_499_; lean_object* v___x_500_; lean_object* v_xs_x27_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_505_; 
v_v_499_ = lean_array_fget(v___x_493_, v_semiringId_475_);
v___x_500_ = lean_box(0);
v_xs_x27_501_ = lean_array_fset(v___x_493_, v_semiringId_475_, v___x_500_);
v___x_502_ = lean_apply_1(v_f_476_, v_v_499_);
v___x_503_ = lean_array_fset(v_xs_x27_501_, v_semiringId_475_, v___x_502_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 2, v___x_503_);
v___x_505_ = v___x_488_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_rings_477_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v_exprToRingId_478_);
lean_ctor_set(v_reuseFailAlloc_506_, 2, v___x_503_);
lean_ctor_set(v_reuseFailAlloc_506_, 3, v_exprToSemiringId_480_);
lean_ctor_set(v_reuseFailAlloc_506_, 4, v_ncRings_481_);
lean_ctor_set(v_reuseFailAlloc_506_, 5, v_exprToNCRingId_482_);
lean_ctor_set(v_reuseFailAlloc_506_, 6, v_ncSemirings_483_);
lean_ctor_set(v_reuseFailAlloc_506_, 7, v_exprToNCSemiringId_484_);
lean_ctor_set(v_reuseFailAlloc_506_, 8, v_steps_485_);
lean_ctor_set_uint8(v_reuseFailAlloc_506_, sizeof(void*)*9, v_reportedMaxDegreeIssue_486_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_modifySemiring___boxed(lean_object* v_s_508_, lean_object* v_semiringId_509_, lean_object* v_f_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Lean_Meta_Grind_Arith_CommRing_State_modifySemiring(v_s_508_, v_semiringId_509_, v_f_510_);
lean_dec(v_semiringId_509_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_getNCRing(lean_object* v_s_512_, lean_object* v_ringId_513_){
_start:
{
lean_object* v_ncRings_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; uint8_t v___x_518_; 
v_ncRings_514_ = lean_ctor_get(v_s_512_, 4);
v___x_515_ = lean_unsigned_to_nat(32u);
v___x_516_ = lean_mk_empty_array_with_capacity(v___x_515_);
lean_dec_ref(v___x_516_);
v___x_517_ = lean_array_get_size(v_ncRings_514_);
v___x_518_ = lean_nat_dec_lt(v_ringId_513_, v___x_517_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; 
v___x_519_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__1);
return v___x_519_;
}
else
{
lean_object* v___x_520_; 
v___x_520_ = lean_array_fget_borrowed(v_ncRings_514_, v_ringId_513_);
lean_inc(v___x_520_);
return v___x_520_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_getNCRing___boxed(lean_object* v_s_521_, lean_object* v_ringId_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Lean_Meta_Grind_Arith_CommRing_State_getNCRing(v_s_521_, v_ringId_522_);
lean_dec(v_ringId_522_);
lean_dec_ref(v_s_521_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_modifyNCRing(lean_object* v_s_524_, lean_object* v_ringId_525_, lean_object* v_f_526_){
_start:
{
lean_object* v_rings_527_; lean_object* v_exprToRingId_528_; lean_object* v_semirings_529_; lean_object* v_exprToSemiringId_530_; lean_object* v_ncRings_531_; lean_object* v_exprToNCRingId_532_; lean_object* v_ncSemirings_533_; lean_object* v_exprToNCSemiringId_534_; lean_object* v_steps_535_; uint8_t v_reportedMaxDegreeIssue_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_557_; 
v_rings_527_ = lean_ctor_get(v_s_524_, 0);
v_exprToRingId_528_ = lean_ctor_get(v_s_524_, 1);
v_semirings_529_ = lean_ctor_get(v_s_524_, 2);
v_exprToSemiringId_530_ = lean_ctor_get(v_s_524_, 3);
v_ncRings_531_ = lean_ctor_get(v_s_524_, 4);
v_exprToNCRingId_532_ = lean_ctor_get(v_s_524_, 5);
v_ncSemirings_533_ = lean_ctor_get(v_s_524_, 6);
v_exprToNCSemiringId_534_ = lean_ctor_get(v_s_524_, 7);
v_steps_535_ = lean_ctor_get(v_s_524_, 8);
v_reportedMaxDegreeIssue_536_ = lean_ctor_get_uint8(v_s_524_, sizeof(void*)*9);
v_isSharedCheck_557_ = !lean_is_exclusive(v_s_524_);
if (v_isSharedCheck_557_ == 0)
{
v___x_538_ = v_s_524_;
v_isShared_539_ = v_isSharedCheck_557_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_steps_535_);
lean_inc(v_exprToNCSemiringId_534_);
lean_inc(v_ncSemirings_533_);
lean_inc(v_exprToNCRingId_532_);
lean_inc(v_ncRings_531_);
lean_inc(v_exprToSemiringId_530_);
lean_inc(v_semirings_529_);
lean_inc(v_exprToRingId_528_);
lean_inc(v_rings_527_);
lean_dec(v_s_524_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_557_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; uint8_t v___x_545_; 
v___x_540_ = lean_unsigned_to_nat(1u);
v___x_541_ = lean_nat_add(v_ringId_525_, v___x_540_);
v___x_542_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default;
v___x_543_ = l_Array_rightpad___redArg(v___x_541_, v___x_542_, v_ncRings_531_);
lean_dec(v___x_541_);
v___x_544_ = lean_array_get_size(v___x_543_);
v___x_545_ = lean_nat_dec_lt(v_ringId_525_, v___x_544_);
if (v___x_545_ == 0)
{
lean_object* v___x_547_; 
lean_dec_ref(v_f_526_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 4, v___x_543_);
v___x_547_ = v___x_538_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_rings_527_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v_exprToRingId_528_);
lean_ctor_set(v_reuseFailAlloc_548_, 2, v_semirings_529_);
lean_ctor_set(v_reuseFailAlloc_548_, 3, v_exprToSemiringId_530_);
lean_ctor_set(v_reuseFailAlloc_548_, 4, v___x_543_);
lean_ctor_set(v_reuseFailAlloc_548_, 5, v_exprToNCRingId_532_);
lean_ctor_set(v_reuseFailAlloc_548_, 6, v_ncSemirings_533_);
lean_ctor_set(v_reuseFailAlloc_548_, 7, v_exprToNCSemiringId_534_);
lean_ctor_set(v_reuseFailAlloc_548_, 8, v_steps_535_);
lean_ctor_set_uint8(v_reuseFailAlloc_548_, sizeof(void*)*9, v_reportedMaxDegreeIssue_536_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
else
{
lean_object* v_v_549_; lean_object* v___x_550_; lean_object* v_xs_x27_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_555_; 
v_v_549_ = lean_array_fget(v___x_543_, v_ringId_525_);
v___x_550_ = lean_box(0);
v_xs_x27_551_ = lean_array_fset(v___x_543_, v_ringId_525_, v___x_550_);
v___x_552_ = lean_apply_1(v_f_526_, v_v_549_);
v___x_553_ = lean_array_fset(v_xs_x27_551_, v_ringId_525_, v___x_552_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 4, v___x_553_);
v___x_555_ = v___x_538_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_rings_527_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v_exprToRingId_528_);
lean_ctor_set(v_reuseFailAlloc_556_, 2, v_semirings_529_);
lean_ctor_set(v_reuseFailAlloc_556_, 3, v_exprToSemiringId_530_);
lean_ctor_set(v_reuseFailAlloc_556_, 4, v___x_553_);
lean_ctor_set(v_reuseFailAlloc_556_, 5, v_exprToNCRingId_532_);
lean_ctor_set(v_reuseFailAlloc_556_, 6, v_ncSemirings_533_);
lean_ctor_set(v_reuseFailAlloc_556_, 7, v_exprToNCSemiringId_534_);
lean_ctor_set(v_reuseFailAlloc_556_, 8, v_steps_535_);
lean_ctor_set_uint8(v_reuseFailAlloc_556_, sizeof(void*)*9, v_reportedMaxDegreeIssue_536_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_modifyNCRing___boxed(lean_object* v_s_558_, lean_object* v_ringId_559_, lean_object* v_f_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lean_Meta_Grind_Arith_CommRing_State_modifyNCRing(v_s_558_, v_ringId_559_, v_f_560_);
lean_dec(v_ringId_559_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_getNCSemiring(lean_object* v_s_562_, lean_object* v_semiringId_563_){
_start:
{
lean_object* v_ncSemirings_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; uint8_t v___x_568_; 
v_ncSemirings_564_ = lean_ctor_get(v_s_562_, 6);
v___x_565_ = lean_unsigned_to_nat(32u);
v___x_566_ = lean_mk_empty_array_with_capacity(v___x_565_);
lean_dec_ref(v___x_566_);
v___x_567_ = lean_array_get_size(v_ncSemirings_564_);
v___x_568_ = lean_nat_dec_lt(v_semiringId_563_, v___x_567_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; 
v___x_569_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__4, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__4_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__4);
return v___x_569_;
}
else
{
lean_object* v___x_570_; 
v___x_570_ = lean_array_fget_borrowed(v_ncSemirings_564_, v_semiringId_563_);
lean_inc(v___x_570_);
return v___x_570_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_getNCSemiring___boxed(lean_object* v_s_571_, lean_object* v_semiringId_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lean_Meta_Grind_Arith_CommRing_State_getNCSemiring(v_s_571_, v_semiringId_572_);
lean_dec(v_semiringId_572_);
lean_dec_ref(v_s_571_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_modifyNCSemiring(lean_object* v_s_574_, lean_object* v_semiringId_575_, lean_object* v_f_576_){
_start:
{
lean_object* v_rings_577_; lean_object* v_exprToRingId_578_; lean_object* v_semirings_579_; lean_object* v_exprToSemiringId_580_; lean_object* v_ncRings_581_; lean_object* v_exprToNCRingId_582_; lean_object* v_ncSemirings_583_; lean_object* v_exprToNCSemiringId_584_; lean_object* v_steps_585_; uint8_t v_reportedMaxDegreeIssue_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_607_; 
v_rings_577_ = lean_ctor_get(v_s_574_, 0);
v_exprToRingId_578_ = lean_ctor_get(v_s_574_, 1);
v_semirings_579_ = lean_ctor_get(v_s_574_, 2);
v_exprToSemiringId_580_ = lean_ctor_get(v_s_574_, 3);
v_ncRings_581_ = lean_ctor_get(v_s_574_, 4);
v_exprToNCRingId_582_ = lean_ctor_get(v_s_574_, 5);
v_ncSemirings_583_ = lean_ctor_get(v_s_574_, 6);
v_exprToNCSemiringId_584_ = lean_ctor_get(v_s_574_, 7);
v_steps_585_ = lean_ctor_get(v_s_574_, 8);
v_reportedMaxDegreeIssue_586_ = lean_ctor_get_uint8(v_s_574_, sizeof(void*)*9);
v_isSharedCheck_607_ = !lean_is_exclusive(v_s_574_);
if (v_isSharedCheck_607_ == 0)
{
v___x_588_ = v_s_574_;
v_isShared_589_ = v_isSharedCheck_607_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_steps_585_);
lean_inc(v_exprToNCSemiringId_584_);
lean_inc(v_ncSemirings_583_);
lean_inc(v_exprToNCRingId_582_);
lean_inc(v_ncRings_581_);
lean_inc(v_exprToSemiringId_580_);
lean_inc(v_semirings_579_);
lean_inc(v_exprToRingId_578_);
lean_inc(v_rings_577_);
lean_dec(v_s_574_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_607_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_590_ = lean_unsigned_to_nat(1u);
v___x_591_ = lean_nat_add(v_semiringId_575_, v___x_590_);
v___x_592_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default;
v___x_593_ = l_Array_rightpad___redArg(v___x_591_, v___x_592_, v_ncSemirings_583_);
lean_dec(v___x_591_);
v___x_594_ = lean_array_get_size(v___x_593_);
v___x_595_ = lean_nat_dec_lt(v_semiringId_575_, v___x_594_);
if (v___x_595_ == 0)
{
lean_object* v___x_597_; 
lean_dec_ref(v_f_576_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 6, v___x_593_);
v___x_597_ = v___x_588_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_rings_577_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_exprToRingId_578_);
lean_ctor_set(v_reuseFailAlloc_598_, 2, v_semirings_579_);
lean_ctor_set(v_reuseFailAlloc_598_, 3, v_exprToSemiringId_580_);
lean_ctor_set(v_reuseFailAlloc_598_, 4, v_ncRings_581_);
lean_ctor_set(v_reuseFailAlloc_598_, 5, v_exprToNCRingId_582_);
lean_ctor_set(v_reuseFailAlloc_598_, 6, v___x_593_);
lean_ctor_set(v_reuseFailAlloc_598_, 7, v_exprToNCSemiringId_584_);
lean_ctor_set(v_reuseFailAlloc_598_, 8, v_steps_585_);
lean_ctor_set_uint8(v_reuseFailAlloc_598_, sizeof(void*)*9, v_reportedMaxDegreeIssue_586_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
else
{
lean_object* v_v_599_; lean_object* v___x_600_; lean_object* v_xs_x27_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_605_; 
v_v_599_ = lean_array_fget(v___x_593_, v_semiringId_575_);
v___x_600_ = lean_box(0);
v_xs_x27_601_ = lean_array_fset(v___x_593_, v_semiringId_575_, v___x_600_);
v___x_602_ = lean_apply_1(v_f_576_, v_v_599_);
v___x_603_ = lean_array_fset(v_xs_x27_601_, v_semiringId_575_, v___x_602_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 6, v___x_603_);
v___x_605_ = v___x_588_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_rings_577_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v_exprToRingId_578_);
lean_ctor_set(v_reuseFailAlloc_606_, 2, v_semirings_579_);
lean_ctor_set(v_reuseFailAlloc_606_, 3, v_exprToSemiringId_580_);
lean_ctor_set(v_reuseFailAlloc_606_, 4, v_ncRings_581_);
lean_ctor_set(v_reuseFailAlloc_606_, 5, v_exprToNCRingId_582_);
lean_ctor_set(v_reuseFailAlloc_606_, 6, v___x_603_);
lean_ctor_set(v_reuseFailAlloc_606_, 7, v_exprToNCSemiringId_584_);
lean_ctor_set(v_reuseFailAlloc_606_, 8, v_steps_585_);
lean_ctor_set_uint8(v_reuseFailAlloc_606_, sizeof(void*)*9, v_reportedMaxDegreeIssue_586_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_modifyNCSemiring___boxed(lean_object* v_s_608_, lean_object* v_semiringId_609_, lean_object* v_f_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_Meta_Grind_Arith_CommRing_State_modifyNCSemiring(v_s_608_, v_semiringId_609_, v_f_610_);
lean_dec(v_semiringId_609_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadLift___redArg___lam__0(lean_object* v_modifyRingState_612_, lean_object* v_inst_613_, lean_object* v_f_614_){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = lean_apply_1(v_modifyRingState_612_, v_f_614_);
v___x_616_ = lean_apply_2(v_inst_613_, lean_box(0), v___x_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadLift___redArg(lean_object* v_inst_617_, lean_object* v_inst_618_){
_start:
{
lean_object* v_getRingState_619_; lean_object* v_modifyRingState_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_629_; 
v_getRingState_619_ = lean_ctor_get(v_inst_618_, 0);
v_modifyRingState_620_ = lean_ctor_get(v_inst_618_, 1);
v_isSharedCheck_629_ = !lean_is_exclusive(v_inst_618_);
if (v_isSharedCheck_629_ == 0)
{
v___x_622_ = v_inst_618_;
v_isShared_623_ = v_isSharedCheck_629_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_modifyRingState_620_);
lean_inc(v_getRingState_619_);
lean_dec(v_inst_618_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_629_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___f_624_; lean_object* v___x_625_; lean_object* v___x_627_; 
lean_inc(v_inst_617_);
v___f_624_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_624_, 0, v_modifyRingState_620_);
lean_closure_set(v___f_624_, 1, v_inst_617_);
v___x_625_ = lean_apply_2(v_inst_617_, lean_box(0), v_getRingState_619_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 1, v___f_624_);
lean_ctor_set(v___x_622_, 0, v___x_625_);
v___x_627_ = v___x_622_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_625_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v___f_624_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadLift(lean_object* v_m_630_, lean_object* v_n_631_, lean_object* v_inst_632_, lean_object* v_inst_633_){
_start:
{
lean_object* v_getRingState_634_; lean_object* v_modifyRingState_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_644_; 
v_getRingState_634_ = lean_ctor_get(v_inst_633_, 0);
v_modifyRingState_635_ = lean_ctor_get(v_inst_633_, 1);
v_isSharedCheck_644_ = !lean_is_exclusive(v_inst_633_);
if (v_isSharedCheck_644_ == 0)
{
v___x_637_ = v_inst_633_;
v_isShared_638_ = v_isSharedCheck_644_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_modifyRingState_635_);
lean_inc(v_getRingState_634_);
lean_dec(v_inst_633_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_644_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___f_639_; lean_object* v___x_640_; lean_object* v___x_642_; 
lean_inc(v_inst_632_);
v___f_639_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_639_, 0, v_modifyRingState_635_);
lean_closure_set(v___f_639_, 1, v_inst_632_);
v___x_640_ = lean_apply_2(v_inst_632_, lean_box(0), v_getRingState_634_);
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 1, v___f_639_);
lean_ctor_set(v___x_637_, 0, v___x_640_);
v___x_642_ = v___x_637_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_640_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v___f_639_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateOfMonadLift___redArg___lam__0(lean_object* v_modifyCommRingState_645_, lean_object* v_inst_646_, lean_object* v_f_647_){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = lean_apply_1(v_modifyCommRingState_645_, v_f_647_);
v___x_649_ = lean_apply_2(v_inst_646_, lean_box(0), v___x_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateOfMonadLift___redArg(lean_object* v_inst_650_, lean_object* v_inst_651_){
_start:
{
lean_object* v_getCommRingState_652_; lean_object* v_modifyCommRingState_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_662_; 
v_getCommRingState_652_ = lean_ctor_get(v_inst_651_, 0);
v_modifyCommRingState_653_ = lean_ctor_get(v_inst_651_, 1);
v_isSharedCheck_662_ = !lean_is_exclusive(v_inst_651_);
if (v_isSharedCheck_662_ == 0)
{
v___x_655_ = v_inst_651_;
v_isShared_656_ = v_isSharedCheck_662_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_modifyCommRingState_653_);
lean_inc(v_getCommRingState_652_);
lean_dec(v_inst_651_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_662_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___f_657_; lean_object* v___x_658_; lean_object* v___x_660_; 
lean_inc(v_inst_650_);
v___f_657_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_657_, 0, v_modifyCommRingState_653_);
lean_closure_set(v___f_657_, 1, v_inst_650_);
v___x_658_ = lean_apply_2(v_inst_650_, lean_box(0), v_getCommRingState_652_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 1, v___f_657_);
lean_ctor_set(v___x_655_, 0, v___x_658_);
v___x_660_ = v___x_655_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v___x_658_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v___f_657_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateOfMonadLift(lean_object* v_m_663_, lean_object* v_n_664_, lean_object* v_inst_665_, lean_object* v_inst_666_){
_start:
{
lean_object* v_getCommRingState_667_; lean_object* v_modifyCommRingState_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_677_; 
v_getCommRingState_667_ = lean_ctor_get(v_inst_666_, 0);
v_modifyCommRingState_668_ = lean_ctor_get(v_inst_666_, 1);
v_isSharedCheck_677_ = !lean_is_exclusive(v_inst_666_);
if (v_isSharedCheck_677_ == 0)
{
v___x_670_ = v_inst_666_;
v_isShared_671_ = v_isSharedCheck_677_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_modifyCommRingState_668_);
lean_inc(v_getCommRingState_667_);
lean_dec(v_inst_666_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_677_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___f_672_; lean_object* v___x_673_; lean_object* v___x_675_; 
lean_inc(v_inst_665_);
v___f_672_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_672_, 0, v_modifyCommRingState_668_);
lean_closure_set(v___f_672_, 1, v_inst_665_);
v___x_673_ = lean_apply_2(v_inst_665_, lean_box(0), v_getCommRingState_667_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 1, v___f_672_);
lean_ctor_set(v___x_670_, 0, v___x_673_);
v___x_675_ = v___x_670_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_673_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v___f_672_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__0(lean_object* v_f_678_, lean_object* v_s_679_){
_start:
{
lean_object* v_toRingState_680_; lean_object* v_denoteEntries_681_; lean_object* v_nextId_682_; lean_object* v_steps_683_; lean_object* v_queue_684_; lean_object* v_basis_685_; lean_object* v_diseqs_686_; uint8_t v_recheck_687_; lean_object* v_invSet_688_; lean_object* v_powIdentityVarCount_689_; lean_object* v_numEq0_x3f_690_; uint8_t v_numEq0Updated_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_699_; 
v_toRingState_680_ = lean_ctor_get(v_s_679_, 0);
v_denoteEntries_681_ = lean_ctor_get(v_s_679_, 1);
v_nextId_682_ = lean_ctor_get(v_s_679_, 2);
v_steps_683_ = lean_ctor_get(v_s_679_, 3);
v_queue_684_ = lean_ctor_get(v_s_679_, 4);
v_basis_685_ = lean_ctor_get(v_s_679_, 5);
v_diseqs_686_ = lean_ctor_get(v_s_679_, 6);
v_recheck_687_ = lean_ctor_get_uint8(v_s_679_, sizeof(void*)*10);
v_invSet_688_ = lean_ctor_get(v_s_679_, 7);
v_powIdentityVarCount_689_ = lean_ctor_get(v_s_679_, 8);
v_numEq0_x3f_690_ = lean_ctor_get(v_s_679_, 9);
v_numEq0Updated_691_ = lean_ctor_get_uint8(v_s_679_, sizeof(void*)*10 + 1);
v_isSharedCheck_699_ = !lean_is_exclusive(v_s_679_);
if (v_isSharedCheck_699_ == 0)
{
v___x_693_ = v_s_679_;
v_isShared_694_ = v_isSharedCheck_699_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_numEq0_x3f_690_);
lean_inc(v_powIdentityVarCount_689_);
lean_inc(v_invSet_688_);
lean_inc(v_diseqs_686_);
lean_inc(v_basis_685_);
lean_inc(v_queue_684_);
lean_inc(v_steps_683_);
lean_inc(v_nextId_682_);
lean_inc(v_denoteEntries_681_);
lean_inc(v_toRingState_680_);
lean_dec(v_s_679_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_699_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_695_; lean_object* v___x_697_; 
v___x_695_ = lean_apply_1(v_f_678_, v_toRingState_680_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v___x_695_);
v___x_697_ = v___x_693_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_695_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v_denoteEntries_681_);
lean_ctor_set(v_reuseFailAlloc_698_, 2, v_nextId_682_);
lean_ctor_set(v_reuseFailAlloc_698_, 3, v_steps_683_);
lean_ctor_set(v_reuseFailAlloc_698_, 4, v_queue_684_);
lean_ctor_set(v_reuseFailAlloc_698_, 5, v_basis_685_);
lean_ctor_set(v_reuseFailAlloc_698_, 6, v_diseqs_686_);
lean_ctor_set(v_reuseFailAlloc_698_, 7, v_invSet_688_);
lean_ctor_set(v_reuseFailAlloc_698_, 8, v_powIdentityVarCount_689_);
lean_ctor_set(v_reuseFailAlloc_698_, 9, v_numEq0_x3f_690_);
lean_ctor_set_uint8(v_reuseFailAlloc_698_, sizeof(void*)*10, v_recheck_687_);
lean_ctor_set_uint8(v_reuseFailAlloc_698_, sizeof(void*)*10 + 1, v_numEq0Updated_691_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__1(lean_object* v_modifyCommRingState_700_, lean_object* v_f_701_){
_start:
{
lean_object* v___f_702_; lean_object* v___x_703_; 
v___f_702_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__0), 2, 1);
lean_closure_set(v___f_702_, 0, v_f_701_);
v___x_703_ = lean_apply_1(v_modifyCommRingState_700_, v___f_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__2(lean_object* v_toPure_704_, lean_object* v_____do__lift_705_){
_start:
{
lean_object* v_toRingState_706_; lean_object* v___x_707_; 
v_toRingState_706_ = lean_ctor_get(v_____do__lift_705_, 0);
lean_inc_ref(v_toRingState_706_);
lean_dec_ref(v_____do__lift_705_);
v___x_707_ = lean_apply_2(v_toPure_704_, lean_box(0), v_toRingState_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg(lean_object* v_inst_708_, lean_object* v_inst_709_){
_start:
{
lean_object* v_toApplicative_710_; lean_object* v_toBind_711_; lean_object* v_getCommRingState_712_; lean_object* v_modifyCommRingState_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_724_; 
v_toApplicative_710_ = lean_ctor_get(v_inst_708_, 0);
lean_inc_ref(v_toApplicative_710_);
v_toBind_711_ = lean_ctor_get(v_inst_708_, 1);
lean_inc(v_toBind_711_);
lean_dec_ref(v_inst_708_);
v_getCommRingState_712_ = lean_ctor_get(v_inst_709_, 0);
v_modifyCommRingState_713_ = lean_ctor_get(v_inst_709_, 1);
v_isSharedCheck_724_ = !lean_is_exclusive(v_inst_709_);
if (v_isSharedCheck_724_ == 0)
{
v___x_715_ = v_inst_709_;
v_isShared_716_ = v_isSharedCheck_724_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_modifyCommRingState_713_);
lean_inc(v_getCommRingState_712_);
lean_dec(v_inst_709_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_724_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v_toPure_717_; lean_object* v___f_718_; lean_object* v___f_719_; lean_object* v___x_720_; lean_object* v___x_722_; 
v_toPure_717_ = lean_ctor_get(v_toApplicative_710_, 1);
lean_inc(v_toPure_717_);
lean_dec_ref(v_toApplicative_710_);
v___f_718_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__1), 2, 1);
lean_closure_set(v___f_718_, 0, v_modifyCommRingState_713_);
v___f_719_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__2), 2, 1);
lean_closure_set(v___f_719_, 0, v_toPure_717_);
v___x_720_ = lean_apply_4(v_toBind_711_, lean_box(0), lean_box(0), v_getCommRingState_712_, v___f_719_);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 1, v___f_718_);
lean_ctor_set(v___x_715_, 0, v___x_720_);
v___x_722_ = v___x_715_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_720_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v___f_718_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState(lean_object* v_m_725_, lean_object* v_inst_726_, lean_object* v_inst_727_){
_start:
{
lean_object* v_toApplicative_728_; lean_object* v_toBind_729_; lean_object* v_getCommRingState_730_; lean_object* v_modifyCommRingState_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_742_; 
v_toApplicative_728_ = lean_ctor_get(v_inst_726_, 0);
lean_inc_ref(v_toApplicative_728_);
v_toBind_729_ = lean_ctor_get(v_inst_726_, 1);
lean_inc(v_toBind_729_);
lean_dec_ref(v_inst_726_);
v_getCommRingState_730_ = lean_ctor_get(v_inst_727_, 0);
v_modifyCommRingState_731_ = lean_ctor_get(v_inst_727_, 1);
v_isSharedCheck_742_ = !lean_is_exclusive(v_inst_727_);
if (v_isSharedCheck_742_ == 0)
{
v___x_733_ = v_inst_727_;
v_isShared_734_ = v_isSharedCheck_742_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_modifyCommRingState_731_);
lean_inc(v_getCommRingState_730_);
lean_dec(v_inst_727_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_742_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v_toPure_735_; lean_object* v___f_736_; lean_object* v___f_737_; lean_object* v___x_738_; lean_object* v___x_740_; 
v_toPure_735_ = lean_ctor_get(v_toApplicative_728_, 1);
lean_inc(v_toPure_735_);
lean_dec_ref(v_toApplicative_728_);
v___f_736_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__1), 2, 1);
lean_closure_set(v___f_736_, 0, v_modifyCommRingState_731_);
v___f_737_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__2), 2, 1);
lean_closure_set(v___f_737_, 0, v_toPure_735_);
v___x_738_ = lean_apply_4(v_toBind_729_, lean_box(0), lean_box(0), v_getCommRingState_730_, v___f_737_);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 1, v___f_736_);
lean_ctor_set(v___x_733_, 0, v___x_738_);
v___x_740_ = v___x_733_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_738_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v___f_736_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateOfMonadLift___redArg___lam__0(lean_object* v_modifySemiringState_743_, lean_object* v_inst_744_, lean_object* v_f_745_){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_746_ = lean_apply_1(v_modifySemiringState_743_, v_f_745_);
v___x_747_ = lean_apply_2(v_inst_744_, lean_box(0), v___x_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateOfMonadLift___redArg(lean_object* v_inst_748_, lean_object* v_inst_749_){
_start:
{
lean_object* v_getSemiringState_750_; lean_object* v_modifySemiringState_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_760_; 
v_getSemiringState_750_ = lean_ctor_get(v_inst_749_, 0);
v_modifySemiringState_751_ = lean_ctor_get(v_inst_749_, 1);
v_isSharedCheck_760_ = !lean_is_exclusive(v_inst_749_);
if (v_isSharedCheck_760_ == 0)
{
v___x_753_ = v_inst_749_;
v_isShared_754_ = v_isSharedCheck_760_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_modifySemiringState_751_);
lean_inc(v_getSemiringState_750_);
lean_dec(v_inst_749_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_760_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___f_755_; lean_object* v___x_756_; lean_object* v___x_758_; 
lean_inc(v_inst_748_);
v___f_755_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_755_, 0, v_modifySemiringState_751_);
lean_closure_set(v___f_755_, 1, v_inst_748_);
v___x_756_ = lean_apply_2(v_inst_748_, lean_box(0), v_getSemiringState_750_);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 1, v___f_755_);
lean_ctor_set(v___x_753_, 0, v___x_756_);
v___x_758_ = v___x_753_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_756_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v___f_755_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateOfMonadLift(lean_object* v_m_761_, lean_object* v_n_762_, lean_object* v_inst_763_, lean_object* v_inst_764_){
_start:
{
lean_object* v_getSemiringState_765_; lean_object* v_modifySemiringState_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_775_; 
v_getSemiringState_765_ = lean_ctor_get(v_inst_764_, 0);
v_modifySemiringState_766_ = lean_ctor_get(v_inst_764_, 1);
v_isSharedCheck_775_ = !lean_is_exclusive(v_inst_764_);
if (v_isSharedCheck_775_ == 0)
{
v___x_768_ = v_inst_764_;
v_isShared_769_ = v_isSharedCheck_775_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_modifySemiringState_766_);
lean_inc(v_getSemiringState_765_);
lean_dec(v_inst_764_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_775_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___f_770_; lean_object* v___x_771_; lean_object* v___x_773_; 
lean_inc(v_inst_763_);
v___f_770_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_770_, 0, v_modifySemiringState_766_);
lean_closure_set(v___f_770_, 1, v_inst_763_);
v___x_771_ = lean_apply_2(v_inst_763_, lean_box(0), v_getSemiringState_765_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 1, v___f_770_);
lean_ctor_set(v___x_768_, 0, v___x_771_);
v___x_773_ = v___x_768_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_771_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v___f_770_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
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
