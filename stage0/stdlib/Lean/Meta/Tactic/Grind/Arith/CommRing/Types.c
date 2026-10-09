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
uint8_t l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare(lean_object* v_c_u2081_135_, lean_object* v_c_u2082_136_){
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
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_u2081_135_ = stack[0].m_obj;
lean_object* v_c_u2082_136_ = stack[1].m_obj;
uint8_t v_res_158_;
v_res_158_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare(v_c_u2081_135_, v_c_u2082_136_);
stack->m_num = v_res_158_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare___boxed(lean_object* v_c_u2081_159_, lean_object* v_c_u2082_160_){
_start:
{
uint8_t v_res_161_; lean_object* v_r_162_; 
v_res_161_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare(v_c_u2081_159_, v_c_u2082_160_);
lean_dec_ref(v_c_u2082_160_);
lean_dec_ref(v_c_u2081_159_);
v_r_162_ = lean_box(v_res_161_);
return v_r_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorIdx___impl(lean_object* v_x_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = lean_obj_tag_nat(v_x_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorIdx___impl___boxed(lean_object* v_x_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorIdx___impl(v_x_165_);
lean_dec_ref(v_x_165_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim___redArg(lean_object* v_t_167_, lean_object* v_k_168_){
_start:
{
switch(lean_obj_tag(v_t_167_))
{
case 0:
{
lean_object* v_p_169_; lean_object* v___x_170_; 
v_p_169_ = lean_ctor_get(v_t_167_, 0);
lean_inc_ref(v_p_169_);
lean_dec_ref_known(v_t_167_, 1);
v___x_170_ = lean_apply_1(v_k_168_, v_p_169_);
return v___x_170_;
}
case 1:
{
lean_object* v_p_171_; lean_object* v_k_u2081_172_; lean_object* v_d_173_; lean_object* v_k_u2082_174_; lean_object* v_m_u2082_175_; lean_object* v_c_176_; lean_object* v___x_177_; 
v_p_171_ = lean_ctor_get(v_t_167_, 0);
lean_inc_ref(v_p_171_);
v_k_u2081_172_ = lean_ctor_get(v_t_167_, 1);
lean_inc(v_k_u2081_172_);
v_d_173_ = lean_ctor_get(v_t_167_, 2);
lean_inc_ref(v_d_173_);
v_k_u2082_174_ = lean_ctor_get(v_t_167_, 3);
lean_inc(v_k_u2082_174_);
v_m_u2082_175_ = lean_ctor_get(v_t_167_, 4);
lean_inc(v_m_u2082_175_);
v_c_176_ = lean_ctor_get(v_t_167_, 5);
lean_inc_ref(v_c_176_);
lean_dec_ref_known(v_t_167_, 6);
v___x_177_ = lean_apply_6(v_k_168_, v_p_171_, v_k_u2081_172_, v_d_173_, v_k_u2082_174_, v_m_u2082_175_, v_c_176_);
return v___x_177_;
}
default: 
{
lean_object* v_p_178_; lean_object* v_d_179_; lean_object* v_c_180_; lean_object* v___x_181_; 
v_p_178_ = lean_ctor_get(v_t_167_, 0);
lean_inc_ref(v_p_178_);
v_d_179_ = lean_ctor_get(v_t_167_, 1);
lean_inc_ref(v_d_179_);
v_c_180_ = lean_ctor_get(v_t_167_, 2);
lean_inc_ref(v_c_180_);
lean_dec_ref_known(v_t_167_, 3);
v___x_181_ = lean_apply_3(v_k_168_, v_p_178_, v_d_179_, v_c_180_);
return v___x_181_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim(lean_object* v_motive_182_, lean_object* v_ctorIdx_183_, lean_object* v_t_184_, lean_object* v_h_185_, lean_object* v_k_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim___redArg(v_t_184_, v_k_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim___boxed(lean_object* v_motive_188_, lean_object* v_ctorIdx_189_, lean_object* v_t_190_, lean_object* v_h_191_, lean_object* v_k_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim(v_motive_188_, v_ctorIdx_189_, v_t_190_, v_h_191_, v_k_192_);
lean_dec(v_ctorIdx_189_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_input_elim___redArg(lean_object* v_t_194_, lean_object* v_input_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim___redArg(v_t_194_, v_input_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_input_elim(lean_object* v_motive_197_, lean_object* v_t_198_, lean_object* v_h_199_, lean_object* v_input_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim___redArg(v_t_198_, v_input_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_step_elim___redArg(lean_object* v_t_202_, lean_object* v_step_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim___redArg(v_t_202_, v_step_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_step_elim(lean_object* v_motive_205_, lean_object* v_t_206_, lean_object* v_h_207_, lean_object* v_step_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim___redArg(v_t_206_, v_step_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_normEq0_elim___redArg(lean_object* v_t_210_, lean_object* v_normEq0_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim___redArg(v_t_210_, v_normEq0_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_normEq0_elim(lean_object* v_motive_213_, lean_object* v_t_214_, lean_object* v_h_215_, lean_object* v_normEq0_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_ctorElim___redArg(v_t_214_, v_normEq0_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_p(lean_object* v_x_218_){
_start:
{
lean_object* v_p_219_; 
v_p_219_ = lean_ctor_get(v_x_218_, 0);
lean_inc_ref(v_p_219_);
return v_p_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_p___boxed(lean_object* v_x_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_p(v_x_220_);
lean_dec_ref(v_x_220_);
return v_res_221_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__0(void){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_222_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__1(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__0);
v___x_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
return v___x_224_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__2(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_225_ = lean_unsigned_to_nat(32u);
v___x_226_ = lean_mk_empty_array_with_capacity(v___x_225_);
v___x_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
return v___x_227_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__3(void){
_start:
{
size_t v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_228_ = ((size_t)5ULL);
v___x_229_ = lean_unsigned_to_nat(0u);
v___x_230_ = lean_unsigned_to_nat(32u);
v___x_231_ = lean_mk_empty_array_with_capacity(v___x_230_);
v___x_232_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__2);
v___x_233_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_233_, 0, v___x_232_);
lean_ctor_set(v___x_233_, 1, v___x_231_);
lean_ctor_set(v___x_233_, 2, v___x_229_);
lean_ctor_set(v___x_233_, 3, v___x_229_);
lean_ctor_set_usize(v___x_233_, 4, v___x_228_);
return v___x_233_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__4(void){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_234_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__3, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__3_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__3);
v___x_235_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__1);
v___x_236_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
lean_ctor_set(v___x_236_, 1, v___x_234_);
lean_ctor_set(v___x_236_, 2, v___x_235_);
return v___x_236_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default(void){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__4, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__4_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__4);
return v___x_237_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState(void){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default;
return v___x_238_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__0(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__0);
v___x_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
return v___x_240_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__1(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_241_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__0);
v___x_242_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__3, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__3_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__3);
v___x_243_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
lean_ctor_set(v___x_243_, 1, v___x_241_);
lean_ctor_set(v___x_243_, 2, v___x_241_);
return v___x_243_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default(void){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__1);
return v___x_244_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState(void){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default;
return v___x_245_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__0);
v___x_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
return v___x_247_;
}
}
lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___redArg(){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___redArg___closed__0);
return v___x_249_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_250_;
v_res_250_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___redArg();
stack->m_obj
 = v_res_250_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___redArg___boxed(lean_object* v___dummy_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___redArg();
return v_res_252_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___redArg();
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0(lean_object* v_00_u03b2_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___closed__0);
return v___x_255_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__0(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_256_ = lean_unsigned_to_nat(32u);
v___x_257_ = lean_mk_empty_array_with_capacity(v___x_256_);
v___x_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
return v___x_258_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__1(void){
_start:
{
size_t v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_259_ = ((size_t)5ULL);
v___x_260_ = lean_unsigned_to_nat(0u);
v___x_261_ = lean_unsigned_to_nat(32u);
v___x_262_ = lean_mk_empty_array_with_capacity(v___x_261_);
v___x_263_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__0);
v___x_264_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_264_, 0, v___x_263_);
lean_ctor_set(v___x_264_, 1, v___x_262_);
lean_ctor_set(v___x_264_, 2, v___x_260_);
lean_ctor_set(v___x_264_, 3, v___x_260_);
lean_ctor_set_usize(v___x_264_, 4, v___x_259_);
return v___x_264_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__2(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; uint8_t v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_265_ = lean_box(0);
v___x_266_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___closed__0);
v___x_267_ = 0;
v___x_268_ = lean_box(0);
v___x_269_ = lean_box(1);
v___x_270_ = lean_unsigned_to_nat(0u);
v___x_271_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__1);
v___x_272_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default;
v___x_273_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_273_, 0, v___x_272_);
lean_ctor_set(v___x_273_, 1, v___x_271_);
lean_ctor_set(v___x_273_, 2, v___x_270_);
lean_ctor_set(v___x_273_, 3, v___x_270_);
lean_ctor_set(v___x_273_, 4, v___x_269_);
lean_ctor_set(v___x_273_, 5, v___x_268_);
lean_ctor_set(v___x_273_, 6, v___x_271_);
lean_ctor_set(v___x_273_, 7, v___x_266_);
lean_ctor_set(v___x_273_, 8, v___x_270_);
lean_ctor_set(v___x_273_, 9, v___x_265_);
lean_ctor_set_uint8(v___x_273_, sizeof(void*)*10, v___x_267_);
lean_ctor_set_uint8(v___x_273_, sizeof(void*)*10 + 1, v___x_267_);
return v___x_273_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default(void){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default___closed__2);
return v___x_274_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState(void){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default;
return v___x_275_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__1(void){
_start:
{
uint8_t v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_278_ = 0;
v___x_279_ = lean_unsigned_to_nat(0u);
v___x_280_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__0);
v___x_281_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__0));
v___x_282_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_282_, 0, v___x_281_);
lean_ctor_set(v___x_282_, 1, v___x_280_);
lean_ctor_set(v___x_282_, 2, v___x_281_);
lean_ctor_set(v___x_282_, 3, v___x_280_);
lean_ctor_set(v___x_282_, 4, v___x_281_);
lean_ctor_set(v___x_282_, 5, v___x_280_);
lean_ctor_set(v___x_282_, 6, v___x_281_);
lean_ctor_set(v___x_282_, 7, v___x_280_);
lean_ctor_set(v___x_282_, 8, v___x_279_);
lean_ctor_set_uint8(v___x_282_, sizeof(void*)*9, v___x_278_);
return v___x_282_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default(void){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__1);
return v___x_283_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState(void){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default;
return v___x_284_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2_(lean_object* v___x_285_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_287_, 0, v___x_285_);
return v___x_287_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_285_ = stack[0].m_obj;
lean_object* v_res_288_;
v_res_288_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2_(v___x_285_);
stack->m_obj
 = v_res_288_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2____boxed(lean_object* v___x_289_, lean_object* v___y_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2_(v___x_289_);
return v_res_291_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_292_; lean_object* v___f_293_; 
v___x_292_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedState_default___closed__1);
v___f_293_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_293_, 0, v___x_292_);
return v___f_293_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_295_; lean_object* v___x_296_; 
v___f_295_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2_);
v___x_296_ = l_Lean_Meta_Grind_registerSolverExtension___redArg(v___f_295_);
return v___x_296_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_297_;
v_res_297_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2_();
stack->m_obj
 = v_res_297_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2____boxed(lean_object* v_a_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_2273073757____hygCtx___hyg_2_();
return v_res_299_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_304_ = l_Lean_Meta_Grind_SolverExtension_getState___redArg(v___x_303_, v_a_300_, v_a_301_);
return v___x_304_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_300_ = stack[0].m_obj;
lean_object* v_a_301_ = stack[1].m_obj;
lean_object* v_res_305_;
v_res_305_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_300_, v_a_301_);
stack->m_obj
 = v_res_305_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg___boxed(lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_306_, v_a_307_);
lean_dec_ref(v_a_307_);
lean_dec(v_a_306_);
return v_res_309_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_get_x27(lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_310_, v_a_318_);
return v___x_321_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_get_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_310_ = stack[0].m_obj;
lean_object* v_a_311_ = stack[1].m_obj;
lean_object* v_a_312_ = stack[2].m_obj;
lean_object* v_a_313_ = stack[3].m_obj;
lean_object* v_a_314_ = stack[4].m_obj;
lean_object* v_a_315_ = stack[5].m_obj;
lean_object* v_a_316_ = stack[6].m_obj;
lean_object* v_a_317_ = stack[7].m_obj;
lean_object* v_a_318_ = stack[8].m_obj;
lean_object* v_a_319_ = stack[9].m_obj;
lean_object* v_res_322_;
v_res_322_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27(v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_);
stack->m_obj
 = v_res_322_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_get_x27___boxed(lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27(v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_329_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
lean_dec(v_a_326_);
lean_dec_ref(v_a_325_);
lean_dec(v_a_324_);
lean_dec(v_a_323_);
return v_res_334_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_modify_x27___redArg(lean_object* v_f_335_, lean_object* v_a_336_){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_339_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_338_, v_f_335_, v_a_336_);
return v___x_339_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_modify_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_335_ = stack[0].m_obj;
lean_object* v_a_336_ = stack[1].m_obj;
lean_object* v_res_340_;
v_res_340_ = l_Lean_Meta_Grind_Arith_CommRing_modify_x27___redArg(v_f_335_, v_a_336_);
stack->m_obj
 = v_res_340_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_modify_x27___redArg___boxed(lean_object* v_f_341_, lean_object* v_a_342_, lean_object* v_a_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_Meta_Grind_Arith_CommRing_modify_x27___redArg(v_f_341_, v_a_342_);
lean_dec(v_a_342_);
return v_res_344_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_modify_x27(lean_object* v_f_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_358_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_357_, v_f_345_, v_a_346_);
return v___x_358_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_modify_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_345_ = stack[0].m_obj;
lean_object* v_a_346_ = stack[1].m_obj;
lean_object* v_a_347_ = stack[2].m_obj;
lean_object* v_a_348_ = stack[3].m_obj;
lean_object* v_a_349_ = stack[4].m_obj;
lean_object* v_a_350_ = stack[5].m_obj;
lean_object* v_a_351_ = stack[6].m_obj;
lean_object* v_a_352_ = stack[7].m_obj;
lean_object* v_a_353_ = stack[8].m_obj;
lean_object* v_a_354_ = stack[9].m_obj;
lean_object* v_a_355_ = stack[10].m_obj;
lean_object* v_res_359_;
v_res_359_ = l_Lean_Meta_Grind_Arith_CommRing_modify_x27(v_f_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_);
stack->m_obj
 = v_res_359_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_modify_x27___boxed(lean_object* v_f_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lean_Meta_Grind_Arith_CommRing_modify_x27(v_f_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
lean_dec(v_a_366_);
lean_dec_ref(v_a_365_);
lean_dec(v_a_364_);
lean_dec_ref(v_a_363_);
lean_dec(v_a_362_);
lean_dec(v_a_361_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_padAndModify___redArg(lean_object* v_inst_373_, lean_object* v_a_374_, lean_object* v_i_375_, lean_object* v_f_376_){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; uint8_t v___x_381_; 
v___x_377_ = lean_unsigned_to_nat(1u);
v___x_378_ = lean_nat_add(v_i_375_, v___x_377_);
v___x_379_ = l_Array_rightpad___redArg(v___x_378_, v_inst_373_, v_a_374_);
lean_dec(v___x_378_);
v___x_380_ = lean_array_get_size(v___x_379_);
v___x_381_ = lean_nat_dec_lt(v_i_375_, v___x_380_);
if (v___x_381_ == 0)
{
lean_dec(v_f_376_);
return v___x_379_;
}
else
{
lean_object* v_v_382_; lean_object* v___x_383_; lean_object* v_xs_x27_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v_v_382_ = lean_array_fget(v___x_379_, v_i_375_);
v___x_383_ = lean_box(0);
v_xs_x27_384_ = lean_array_fset(v___x_379_, v_i_375_, v___x_383_);
v___x_385_ = lean_apply_1(v_f_376_, v_v_382_);
v___x_386_ = lean_array_fset(v_xs_x27_384_, v_i_375_, v___x_385_);
return v___x_386_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_padAndModify___redArg___boxed(lean_object* v_inst_387_, lean_object* v_a_388_, lean_object* v_i_389_, lean_object* v_f_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_padAndModify___redArg(v_inst_387_, v_a_388_, v_i_389_, v_f_390_);
lean_dec(v_i_389_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_padAndModify(lean_object* v_00_u03b1_392_, lean_object* v_inst_393_, lean_object* v_a_394_, lean_object* v_i_395_, lean_object* v_f_396_){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
v___x_397_ = lean_unsigned_to_nat(1u);
v___x_398_ = lean_nat_add(v_i_395_, v___x_397_);
v___x_399_ = l_Array_rightpad___redArg(v___x_398_, v_inst_393_, v_a_394_);
lean_dec(v___x_398_);
v___x_400_ = lean_array_get_size(v___x_399_);
v___x_401_ = lean_nat_dec_lt(v_i_395_, v___x_400_);
if (v___x_401_ == 0)
{
lean_dec(v_f_396_);
return v___x_399_;
}
else
{
lean_object* v_v_402_; lean_object* v___x_403_; lean_object* v_xs_x27_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v_v_402_ = lean_array_fget(v___x_399_, v_i_395_);
v___x_403_ = lean_box(0);
v_xs_x27_404_ = lean_array_fset(v___x_399_, v_i_395_, v___x_403_);
v___x_405_ = lean_apply_1(v_f_396_, v_v_402_);
v___x_406_ = lean_array_fset(v_xs_x27_404_, v_i_395_, v___x_405_);
return v___x_406_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_padAndModify___boxed(lean_object* v_00_u03b1_407_, lean_object* v_inst_408_, lean_object* v_a_409_, lean_object* v_i_410_, lean_object* v_f_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Types_0__Lean_Meta_Grind_Arith_CommRing_padAndModify(v_00_u03b1_407_, v_inst_408_, v_a_409_, v_i_410_, v_f_411_);
lean_dec(v_i_410_);
return v_res_412_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_State_getRing___closed__0(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; uint8_t v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_413_ = lean_box(0);
v___x_414_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default_spec__0___closed__0);
v___x_415_ = 0;
v___x_416_ = lean_box(0);
v___x_417_ = lean_box(1);
v___x_418_ = lean_unsigned_to_nat(0u);
v___x_419_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__3, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__3_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__3);
v___x_420_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__1);
v___x_421_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_421_, 0, v___x_420_);
lean_ctor_set(v___x_421_, 1, v___x_419_);
lean_ctor_set(v___x_421_, 2, v___x_418_);
lean_ctor_set(v___x_421_, 3, v___x_418_);
lean_ctor_set(v___x_421_, 4, v___x_417_);
lean_ctor_set(v___x_421_, 5, v___x_416_);
lean_ctor_set(v___x_421_, 6, v___x_419_);
lean_ctor_set(v___x_421_, 7, v___x_414_);
lean_ctor_set(v___x_421_, 8, v___x_418_);
lean_ctor_set(v___x_421_, 9, v___x_413_);
lean_ctor_set_uint8(v___x_421_, sizeof(void*)*10, v___x_415_);
lean_ctor_set_uint8(v___x_421_, sizeof(void*)*10 + 1, v___x_415_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_getRing(lean_object* v_s_422_, lean_object* v_ringId_423_){
_start:
{
lean_object* v_rings_424_; lean_object* v___x_425_; lean_object* v___x_426_; uint8_t v___x_427_; 
v_rings_424_ = lean_ctor_get(v_s_422_, 0);
v___x_425_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_State_getRing___closed__0, &l_Lean_Meta_Grind_Arith_CommRing_State_getRing___closed__0_once, _init_l_Lean_Meta_Grind_Arith_CommRing_State_getRing___closed__0);
v___x_426_ = lean_array_get_size(v_rings_424_);
v___x_427_ = lean_nat_dec_lt(v_ringId_423_, v___x_426_);
if (v___x_427_ == 0)
{
return v___x_425_;
}
else
{
lean_object* v___x_428_; 
v___x_428_ = lean_array_fget_borrowed(v_rings_424_, v_ringId_423_);
lean_inc(v___x_428_);
return v___x_428_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_getRing___boxed(lean_object* v_s_429_, lean_object* v_ringId_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lean_Meta_Grind_Arith_CommRing_State_getRing(v_s_429_, v_ringId_430_);
lean_dec(v_ringId_430_);
lean_dec_ref(v_s_429_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_modifyRing(lean_object* v_s_432_, lean_object* v_ringId_433_, lean_object* v_f_434_){
_start:
{
lean_object* v_rings_435_; lean_object* v_exprToRingId_436_; lean_object* v_semirings_437_; lean_object* v_exprToSemiringId_438_; lean_object* v_ncRings_439_; lean_object* v_exprToNCRingId_440_; lean_object* v_ncSemirings_441_; lean_object* v_exprToNCSemiringId_442_; lean_object* v_steps_443_; uint8_t v_reportedMaxDegreeIssue_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_465_; 
v_rings_435_ = lean_ctor_get(v_s_432_, 0);
v_exprToRingId_436_ = lean_ctor_get(v_s_432_, 1);
v_semirings_437_ = lean_ctor_get(v_s_432_, 2);
v_exprToSemiringId_438_ = lean_ctor_get(v_s_432_, 3);
v_ncRings_439_ = lean_ctor_get(v_s_432_, 4);
v_exprToNCRingId_440_ = lean_ctor_get(v_s_432_, 5);
v_ncSemirings_441_ = lean_ctor_get(v_s_432_, 6);
v_exprToNCSemiringId_442_ = lean_ctor_get(v_s_432_, 7);
v_steps_443_ = lean_ctor_get(v_s_432_, 8);
v_reportedMaxDegreeIssue_444_ = lean_ctor_get_uint8(v_s_432_, sizeof(void*)*9);
v_isSharedCheck_465_ = !lean_is_exclusive(v_s_432_);
if (v_isSharedCheck_465_ == 0)
{
v___x_446_ = v_s_432_;
v_isShared_447_ = v_isSharedCheck_465_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_steps_443_);
lean_inc(v_exprToNCSemiringId_442_);
lean_inc(v_ncSemirings_441_);
lean_inc(v_exprToNCRingId_440_);
lean_inc(v_ncRings_439_);
lean_inc(v_exprToSemiringId_438_);
lean_inc(v_semirings_437_);
lean_inc(v_exprToRingId_436_);
lean_inc(v_rings_435_);
lean_dec(v_s_432_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_465_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_448_ = lean_unsigned_to_nat(1u);
v___x_449_ = lean_nat_add(v_ringId_433_, v___x_448_);
v___x_450_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedCommRingState_default;
v___x_451_ = l_Array_rightpad___redArg(v___x_449_, v___x_450_, v_rings_435_);
lean_dec(v___x_449_);
v___x_452_ = lean_array_get_size(v___x_451_);
v___x_453_ = lean_nat_dec_lt(v_ringId_433_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_455_; 
lean_dec_ref(v_f_434_);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 0, v___x_451_);
v___x_455_ = v___x_446_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_451_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v_exprToRingId_436_);
lean_ctor_set(v_reuseFailAlloc_456_, 2, v_semirings_437_);
lean_ctor_set(v_reuseFailAlloc_456_, 3, v_exprToSemiringId_438_);
lean_ctor_set(v_reuseFailAlloc_456_, 4, v_ncRings_439_);
lean_ctor_set(v_reuseFailAlloc_456_, 5, v_exprToNCRingId_440_);
lean_ctor_set(v_reuseFailAlloc_456_, 6, v_ncSemirings_441_);
lean_ctor_set(v_reuseFailAlloc_456_, 7, v_exprToNCSemiringId_442_);
lean_ctor_set(v_reuseFailAlloc_456_, 8, v_steps_443_);
lean_ctor_set_uint8(v_reuseFailAlloc_456_, sizeof(void*)*9, v_reportedMaxDegreeIssue_444_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
else
{
lean_object* v_v_457_; lean_object* v___x_458_; lean_object* v_xs_x27_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_463_; 
v_v_457_ = lean_array_fget(v___x_451_, v_ringId_433_);
v___x_458_ = lean_box(0);
v_xs_x27_459_ = lean_array_fset(v___x_451_, v_ringId_433_, v___x_458_);
v___x_460_ = lean_apply_1(v_f_434_, v_v_457_);
v___x_461_ = lean_array_fset(v_xs_x27_459_, v_ringId_433_, v___x_460_);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 0, v___x_461_);
v___x_463_ = v___x_446_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_461_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v_exprToRingId_436_);
lean_ctor_set(v_reuseFailAlloc_464_, 2, v_semirings_437_);
lean_ctor_set(v_reuseFailAlloc_464_, 3, v_exprToSemiringId_438_);
lean_ctor_set(v_reuseFailAlloc_464_, 4, v_ncRings_439_);
lean_ctor_set(v_reuseFailAlloc_464_, 5, v_exprToNCRingId_440_);
lean_ctor_set(v_reuseFailAlloc_464_, 6, v_ncSemirings_441_);
lean_ctor_set(v_reuseFailAlloc_464_, 7, v_exprToNCSemiringId_442_);
lean_ctor_set(v_reuseFailAlloc_464_, 8, v_steps_443_);
lean_ctor_set_uint8(v_reuseFailAlloc_464_, sizeof(void*)*9, v_reportedMaxDegreeIssue_444_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_modifyRing___boxed(lean_object* v_s_466_, lean_object* v_ringId_467_, lean_object* v_f_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_Meta_Grind_Arith_CommRing_State_modifyRing(v_s_466_, v_ringId_467_, v_f_468_);
lean_dec(v_ringId_467_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_getSemiring(lean_object* v_s_470_, lean_object* v_semiringId_471_){
_start:
{
lean_object* v_semirings_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; uint8_t v___x_476_; 
v_semirings_472_ = lean_ctor_get(v_s_470_, 2);
v___x_473_ = lean_unsigned_to_nat(32u);
v___x_474_ = lean_mk_empty_array_with_capacity(v___x_473_);
lean_dec_ref(v___x_474_);
v___x_475_ = lean_array_get_size(v_semirings_472_);
v___x_476_ = lean_nat_dec_lt(v_semiringId_471_, v___x_475_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; 
v___x_477_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__4, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__4_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__4);
return v___x_477_;
}
else
{
lean_object* v___x_478_; 
v___x_478_ = lean_array_fget_borrowed(v_semirings_472_, v_semiringId_471_);
lean_inc(v___x_478_);
return v___x_478_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_getSemiring___boxed(lean_object* v_s_479_, lean_object* v_semiringId_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Lean_Meta_Grind_Arith_CommRing_State_getSemiring(v_s_479_, v_semiringId_480_);
lean_dec(v_semiringId_480_);
lean_dec_ref(v_s_479_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_modifySemiring(lean_object* v_s_482_, lean_object* v_semiringId_483_, lean_object* v_f_484_){
_start:
{
lean_object* v_rings_485_; lean_object* v_exprToRingId_486_; lean_object* v_semirings_487_; lean_object* v_exprToSemiringId_488_; lean_object* v_ncRings_489_; lean_object* v_exprToNCRingId_490_; lean_object* v_ncSemirings_491_; lean_object* v_exprToNCSemiringId_492_; lean_object* v_steps_493_; uint8_t v_reportedMaxDegreeIssue_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_515_; 
v_rings_485_ = lean_ctor_get(v_s_482_, 0);
v_exprToRingId_486_ = lean_ctor_get(v_s_482_, 1);
v_semirings_487_ = lean_ctor_get(v_s_482_, 2);
v_exprToSemiringId_488_ = lean_ctor_get(v_s_482_, 3);
v_ncRings_489_ = lean_ctor_get(v_s_482_, 4);
v_exprToNCRingId_490_ = lean_ctor_get(v_s_482_, 5);
v_ncSemirings_491_ = lean_ctor_get(v_s_482_, 6);
v_exprToNCSemiringId_492_ = lean_ctor_get(v_s_482_, 7);
v_steps_493_ = lean_ctor_get(v_s_482_, 8);
v_reportedMaxDegreeIssue_494_ = lean_ctor_get_uint8(v_s_482_, sizeof(void*)*9);
v_isSharedCheck_515_ = !lean_is_exclusive(v_s_482_);
if (v_isSharedCheck_515_ == 0)
{
v___x_496_ = v_s_482_;
v_isShared_497_ = v_isSharedCheck_515_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_steps_493_);
lean_inc(v_exprToNCSemiringId_492_);
lean_inc(v_ncSemirings_491_);
lean_inc(v_exprToNCRingId_490_);
lean_inc(v_ncRings_489_);
lean_inc(v_exprToSemiringId_488_);
lean_inc(v_semirings_487_);
lean_inc(v_exprToRingId_486_);
lean_inc(v_rings_485_);
lean_dec(v_s_482_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_515_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_498_ = lean_unsigned_to_nat(1u);
v___x_499_ = lean_nat_add(v_semiringId_483_, v___x_498_);
v___x_500_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default;
v___x_501_ = l_Array_rightpad___redArg(v___x_499_, v___x_500_, v_semirings_487_);
lean_dec(v___x_499_);
v___x_502_ = lean_array_get_size(v___x_501_);
v___x_503_ = lean_nat_dec_lt(v_semiringId_483_, v___x_502_);
if (v___x_503_ == 0)
{
lean_object* v___x_505_; 
lean_dec_ref(v_f_484_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 2, v___x_501_);
v___x_505_ = v___x_496_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_rings_485_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v_exprToRingId_486_);
lean_ctor_set(v_reuseFailAlloc_506_, 2, v___x_501_);
lean_ctor_set(v_reuseFailAlloc_506_, 3, v_exprToSemiringId_488_);
lean_ctor_set(v_reuseFailAlloc_506_, 4, v_ncRings_489_);
lean_ctor_set(v_reuseFailAlloc_506_, 5, v_exprToNCRingId_490_);
lean_ctor_set(v_reuseFailAlloc_506_, 6, v_ncSemirings_491_);
lean_ctor_set(v_reuseFailAlloc_506_, 7, v_exprToNCSemiringId_492_);
lean_ctor_set(v_reuseFailAlloc_506_, 8, v_steps_493_);
lean_ctor_set_uint8(v_reuseFailAlloc_506_, sizeof(void*)*9, v_reportedMaxDegreeIssue_494_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
else
{
lean_object* v_v_507_; lean_object* v___x_508_; lean_object* v_xs_x27_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_513_; 
v_v_507_ = lean_array_fget(v___x_501_, v_semiringId_483_);
v___x_508_ = lean_box(0);
v_xs_x27_509_ = lean_array_fset(v___x_501_, v_semiringId_483_, v___x_508_);
v___x_510_ = lean_apply_1(v_f_484_, v_v_507_);
v___x_511_ = lean_array_fset(v_xs_x27_509_, v_semiringId_483_, v___x_510_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 2, v___x_511_);
v___x_513_ = v___x_496_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_rings_485_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v_exprToRingId_486_);
lean_ctor_set(v_reuseFailAlloc_514_, 2, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_514_, 3, v_exprToSemiringId_488_);
lean_ctor_set(v_reuseFailAlloc_514_, 4, v_ncRings_489_);
lean_ctor_set(v_reuseFailAlloc_514_, 5, v_exprToNCRingId_490_);
lean_ctor_set(v_reuseFailAlloc_514_, 6, v_ncSemirings_491_);
lean_ctor_set(v_reuseFailAlloc_514_, 7, v_exprToNCSemiringId_492_);
lean_ctor_set(v_reuseFailAlloc_514_, 8, v_steps_493_);
lean_ctor_set_uint8(v_reuseFailAlloc_514_, sizeof(void*)*9, v_reportedMaxDegreeIssue_494_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_modifySemiring___boxed(lean_object* v_s_516_, lean_object* v_semiringId_517_, lean_object* v_f_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Lean_Meta_Grind_Arith_CommRing_State_modifySemiring(v_s_516_, v_semiringId_517_, v_f_518_);
lean_dec(v_semiringId_517_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_getNCRing(lean_object* v_s_520_, lean_object* v_ringId_521_){
_start:
{
lean_object* v_ncRings_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v_ncRings_522_ = lean_ctor_get(v_s_520_, 4);
v___x_523_ = lean_unsigned_to_nat(32u);
v___x_524_ = lean_mk_empty_array_with_capacity(v___x_523_);
lean_dec_ref(v___x_524_);
v___x_525_ = lean_array_get_size(v_ncRings_522_);
v___x_526_ = lean_nat_dec_lt(v_ringId_521_, v___x_525_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; 
v___x_527_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default___closed__1);
return v___x_527_;
}
else
{
lean_object* v___x_528_; 
v___x_528_ = lean_array_fget_borrowed(v_ncRings_522_, v_ringId_521_);
lean_inc(v___x_528_);
return v___x_528_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_getNCRing___boxed(lean_object* v_s_529_, lean_object* v_ringId_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_Meta_Grind_Arith_CommRing_State_getNCRing(v_s_529_, v_ringId_530_);
lean_dec(v_ringId_530_);
lean_dec_ref(v_s_529_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_modifyNCRing(lean_object* v_s_532_, lean_object* v_ringId_533_, lean_object* v_f_534_){
_start:
{
lean_object* v_rings_535_; lean_object* v_exprToRingId_536_; lean_object* v_semirings_537_; lean_object* v_exprToSemiringId_538_; lean_object* v_ncRings_539_; lean_object* v_exprToNCRingId_540_; lean_object* v_ncSemirings_541_; lean_object* v_exprToNCSemiringId_542_; lean_object* v_steps_543_; uint8_t v_reportedMaxDegreeIssue_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_565_; 
v_rings_535_ = lean_ctor_get(v_s_532_, 0);
v_exprToRingId_536_ = lean_ctor_get(v_s_532_, 1);
v_semirings_537_ = lean_ctor_get(v_s_532_, 2);
v_exprToSemiringId_538_ = lean_ctor_get(v_s_532_, 3);
v_ncRings_539_ = lean_ctor_get(v_s_532_, 4);
v_exprToNCRingId_540_ = lean_ctor_get(v_s_532_, 5);
v_ncSemirings_541_ = lean_ctor_get(v_s_532_, 6);
v_exprToNCSemiringId_542_ = lean_ctor_get(v_s_532_, 7);
v_steps_543_ = lean_ctor_get(v_s_532_, 8);
v_reportedMaxDegreeIssue_544_ = lean_ctor_get_uint8(v_s_532_, sizeof(void*)*9);
v_isSharedCheck_565_ = !lean_is_exclusive(v_s_532_);
if (v_isSharedCheck_565_ == 0)
{
v___x_546_ = v_s_532_;
v_isShared_547_ = v_isSharedCheck_565_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_steps_543_);
lean_inc(v_exprToNCSemiringId_542_);
lean_inc(v_ncSemirings_541_);
lean_inc(v_exprToNCRingId_540_);
lean_inc(v_ncRings_539_);
lean_inc(v_exprToSemiringId_538_);
lean_inc(v_semirings_537_);
lean_inc(v_exprToRingId_536_);
lean_inc(v_rings_535_);
lean_dec(v_s_532_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_565_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_548_ = lean_unsigned_to_nat(1u);
v___x_549_ = lean_nat_add(v_ringId_533_, v___x_548_);
v___x_550_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedRingState_default;
v___x_551_ = l_Array_rightpad___redArg(v___x_549_, v___x_550_, v_ncRings_539_);
lean_dec(v___x_549_);
v___x_552_ = lean_array_get_size(v___x_551_);
v___x_553_ = lean_nat_dec_lt(v_ringId_533_, v___x_552_);
if (v___x_553_ == 0)
{
lean_object* v___x_555_; 
lean_dec_ref(v_f_534_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 4, v___x_551_);
v___x_555_ = v___x_546_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_rings_535_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v_exprToRingId_536_);
lean_ctor_set(v_reuseFailAlloc_556_, 2, v_semirings_537_);
lean_ctor_set(v_reuseFailAlloc_556_, 3, v_exprToSemiringId_538_);
lean_ctor_set(v_reuseFailAlloc_556_, 4, v___x_551_);
lean_ctor_set(v_reuseFailAlloc_556_, 5, v_exprToNCRingId_540_);
lean_ctor_set(v_reuseFailAlloc_556_, 6, v_ncSemirings_541_);
lean_ctor_set(v_reuseFailAlloc_556_, 7, v_exprToNCSemiringId_542_);
lean_ctor_set(v_reuseFailAlloc_556_, 8, v_steps_543_);
lean_ctor_set_uint8(v_reuseFailAlloc_556_, sizeof(void*)*9, v_reportedMaxDegreeIssue_544_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
else
{
lean_object* v_v_557_; lean_object* v___x_558_; lean_object* v_xs_x27_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_563_; 
v_v_557_ = lean_array_fget(v___x_551_, v_ringId_533_);
v___x_558_ = lean_box(0);
v_xs_x27_559_ = lean_array_fset(v___x_551_, v_ringId_533_, v___x_558_);
v___x_560_ = lean_apply_1(v_f_534_, v_v_557_);
v___x_561_ = lean_array_fset(v_xs_x27_559_, v_ringId_533_, v___x_560_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 4, v___x_561_);
v___x_563_ = v___x_546_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_rings_535_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_exprToRingId_536_);
lean_ctor_set(v_reuseFailAlloc_564_, 2, v_semirings_537_);
lean_ctor_set(v_reuseFailAlloc_564_, 3, v_exprToSemiringId_538_);
lean_ctor_set(v_reuseFailAlloc_564_, 4, v___x_561_);
lean_ctor_set(v_reuseFailAlloc_564_, 5, v_exprToNCRingId_540_);
lean_ctor_set(v_reuseFailAlloc_564_, 6, v_ncSemirings_541_);
lean_ctor_set(v_reuseFailAlloc_564_, 7, v_exprToNCSemiringId_542_);
lean_ctor_set(v_reuseFailAlloc_564_, 8, v_steps_543_);
lean_ctor_set_uint8(v_reuseFailAlloc_564_, sizeof(void*)*9, v_reportedMaxDegreeIssue_544_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_modifyNCRing___boxed(lean_object* v_s_566_, lean_object* v_ringId_567_, lean_object* v_f_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_Meta_Grind_Arith_CommRing_State_modifyNCRing(v_s_566_, v_ringId_567_, v_f_568_);
lean_dec(v_ringId_567_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_getNCSemiring(lean_object* v_s_570_, lean_object* v_semiringId_571_){
_start:
{
lean_object* v_ncSemirings_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; 
v_ncSemirings_572_ = lean_ctor_get(v_s_570_, 6);
v___x_573_ = lean_unsigned_to_nat(32u);
v___x_574_ = lean_mk_empty_array_with_capacity(v___x_573_);
lean_dec_ref(v___x_574_);
v___x_575_ = lean_array_get_size(v_ncSemirings_572_);
v___x_576_ = lean_nat_dec_lt(v_semiringId_571_, v___x_575_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; 
v___x_577_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__4, &l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__4_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default___closed__4);
return v___x_577_;
}
else
{
lean_object* v___x_578_; 
v___x_578_ = lean_array_fget_borrowed(v_ncSemirings_572_, v_semiringId_571_);
lean_inc(v___x_578_);
return v___x_578_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_getNCSemiring___boxed(lean_object* v_s_579_, lean_object* v_semiringId_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Lean_Meta_Grind_Arith_CommRing_State_getNCSemiring(v_s_579_, v_semiringId_580_);
lean_dec(v_semiringId_580_);
lean_dec_ref(v_s_579_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_modifyNCSemiring(lean_object* v_s_582_, lean_object* v_semiringId_583_, lean_object* v_f_584_){
_start:
{
lean_object* v_rings_585_; lean_object* v_exprToRingId_586_; lean_object* v_semirings_587_; lean_object* v_exprToSemiringId_588_; lean_object* v_ncRings_589_; lean_object* v_exprToNCRingId_590_; lean_object* v_ncSemirings_591_; lean_object* v_exprToNCSemiringId_592_; lean_object* v_steps_593_; uint8_t v_reportedMaxDegreeIssue_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_615_; 
v_rings_585_ = lean_ctor_get(v_s_582_, 0);
v_exprToRingId_586_ = lean_ctor_get(v_s_582_, 1);
v_semirings_587_ = lean_ctor_get(v_s_582_, 2);
v_exprToSemiringId_588_ = lean_ctor_get(v_s_582_, 3);
v_ncRings_589_ = lean_ctor_get(v_s_582_, 4);
v_exprToNCRingId_590_ = lean_ctor_get(v_s_582_, 5);
v_ncSemirings_591_ = lean_ctor_get(v_s_582_, 6);
v_exprToNCSemiringId_592_ = lean_ctor_get(v_s_582_, 7);
v_steps_593_ = lean_ctor_get(v_s_582_, 8);
v_reportedMaxDegreeIssue_594_ = lean_ctor_get_uint8(v_s_582_, sizeof(void*)*9);
v_isSharedCheck_615_ = !lean_is_exclusive(v_s_582_);
if (v_isSharedCheck_615_ == 0)
{
v___x_596_ = v_s_582_;
v_isShared_597_ = v_isSharedCheck_615_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_steps_593_);
lean_inc(v_exprToNCSemiringId_592_);
lean_inc(v_ncSemirings_591_);
lean_inc(v_exprToNCRingId_590_);
lean_inc(v_ncRings_589_);
lean_inc(v_exprToSemiringId_588_);
lean_inc(v_semirings_587_);
lean_inc(v_exprToRingId_586_);
lean_inc(v_rings_585_);
lean_dec(v_s_582_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_615_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_598_ = lean_unsigned_to_nat(1u);
v___x_599_ = lean_nat_add(v_semiringId_583_, v___x_598_);
v___x_600_ = l_Lean_Meta_Grind_Arith_CommRing_instInhabitedSemiringState_default;
v___x_601_ = l_Array_rightpad___redArg(v___x_599_, v___x_600_, v_ncSemirings_591_);
lean_dec(v___x_599_);
v___x_602_ = lean_array_get_size(v___x_601_);
v___x_603_ = lean_nat_dec_lt(v_semiringId_583_, v___x_602_);
if (v___x_603_ == 0)
{
lean_object* v___x_605_; 
lean_dec_ref(v_f_584_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 6, v___x_601_);
v___x_605_ = v___x_596_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_rings_585_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v_exprToRingId_586_);
lean_ctor_set(v_reuseFailAlloc_606_, 2, v_semirings_587_);
lean_ctor_set(v_reuseFailAlloc_606_, 3, v_exprToSemiringId_588_);
lean_ctor_set(v_reuseFailAlloc_606_, 4, v_ncRings_589_);
lean_ctor_set(v_reuseFailAlloc_606_, 5, v_exprToNCRingId_590_);
lean_ctor_set(v_reuseFailAlloc_606_, 6, v___x_601_);
lean_ctor_set(v_reuseFailAlloc_606_, 7, v_exprToNCSemiringId_592_);
lean_ctor_set(v_reuseFailAlloc_606_, 8, v_steps_593_);
lean_ctor_set_uint8(v_reuseFailAlloc_606_, sizeof(void*)*9, v_reportedMaxDegreeIssue_594_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
else
{
lean_object* v_v_607_; lean_object* v___x_608_; lean_object* v_xs_x27_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_613_; 
v_v_607_ = lean_array_fget(v___x_601_, v_semiringId_583_);
v___x_608_ = lean_box(0);
v_xs_x27_609_ = lean_array_fset(v___x_601_, v_semiringId_583_, v___x_608_);
v___x_610_ = lean_apply_1(v_f_584_, v_v_607_);
v___x_611_ = lean_array_fset(v_xs_x27_609_, v_semiringId_583_, v___x_610_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 6, v___x_611_);
v___x_613_ = v___x_596_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_rings_585_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_exprToRingId_586_);
lean_ctor_set(v_reuseFailAlloc_614_, 2, v_semirings_587_);
lean_ctor_set(v_reuseFailAlloc_614_, 3, v_exprToSemiringId_588_);
lean_ctor_set(v_reuseFailAlloc_614_, 4, v_ncRings_589_);
lean_ctor_set(v_reuseFailAlloc_614_, 5, v_exprToNCRingId_590_);
lean_ctor_set(v_reuseFailAlloc_614_, 6, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_614_, 7, v_exprToNCSemiringId_592_);
lean_ctor_set(v_reuseFailAlloc_614_, 8, v_steps_593_);
lean_ctor_set_uint8(v_reuseFailAlloc_614_, sizeof(void*)*9, v_reportedMaxDegreeIssue_594_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_State_modifyNCSemiring___boxed(lean_object* v_s_616_, lean_object* v_semiringId_617_, lean_object* v_f_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Lean_Meta_Grind_Arith_CommRing_State_modifyNCSemiring(v_s_616_, v_semiringId_617_, v_f_618_);
lean_dec(v_semiringId_617_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadLift___redArg___lam__0(lean_object* v_modifyRingState_620_, lean_object* v_inst_621_, lean_object* v_f_622_){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = lean_apply_1(v_modifyRingState_620_, v_f_622_);
v___x_624_ = lean_apply_2(v_inst_621_, lean_box(0), v___x_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadLift___redArg(lean_object* v_inst_625_, lean_object* v_inst_626_){
_start:
{
lean_object* v_getRingState_627_; lean_object* v_modifyRingState_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_637_; 
v_getRingState_627_ = lean_ctor_get(v_inst_626_, 0);
v_modifyRingState_628_ = lean_ctor_get(v_inst_626_, 1);
v_isSharedCheck_637_ = !lean_is_exclusive(v_inst_626_);
if (v_isSharedCheck_637_ == 0)
{
v___x_630_ = v_inst_626_;
v_isShared_631_ = v_isSharedCheck_637_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_modifyRingState_628_);
lean_inc(v_getRingState_627_);
lean_dec(v_inst_626_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_637_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___f_632_; lean_object* v___x_633_; lean_object* v___x_635_; 
lean_inc(v_inst_625_);
v___f_632_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_632_, 0, v_modifyRingState_628_);
lean_closure_set(v___f_632_, 1, v_inst_625_);
v___x_633_ = lean_apply_2(v_inst_625_, lean_box(0), v_getRingState_627_);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 1, v___f_632_);
lean_ctor_set(v___x_630_, 0, v___x_633_);
v___x_635_ = v___x_630_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v___f_632_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadLift(lean_object* v_m_638_, lean_object* v_n_639_, lean_object* v_inst_640_, lean_object* v_inst_641_){
_start:
{
lean_object* v_getRingState_642_; lean_object* v_modifyRingState_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_652_; 
v_getRingState_642_ = lean_ctor_get(v_inst_641_, 0);
v_modifyRingState_643_ = lean_ctor_get(v_inst_641_, 1);
v_isSharedCheck_652_ = !lean_is_exclusive(v_inst_641_);
if (v_isSharedCheck_652_ == 0)
{
v___x_645_ = v_inst_641_;
v_isShared_646_ = v_isSharedCheck_652_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_modifyRingState_643_);
lean_inc(v_getRingState_642_);
lean_dec(v_inst_641_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_652_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___f_647_; lean_object* v___x_648_; lean_object* v___x_650_; 
lean_inc(v_inst_640_);
v___f_647_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_647_, 0, v_modifyRingState_643_);
lean_closure_set(v___f_647_, 1, v_inst_640_);
v___x_648_ = lean_apply_2(v_inst_640_, lean_box(0), v_getRingState_642_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 1, v___f_647_);
lean_ctor_set(v___x_645_, 0, v___x_648_);
v___x_650_ = v___x_645_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_648_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v___f_647_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateOfMonadLift___redArg___lam__0(lean_object* v_modifyCommRingState_653_, lean_object* v_inst_654_, lean_object* v_f_655_){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = lean_apply_1(v_modifyCommRingState_653_, v_f_655_);
v___x_657_ = lean_apply_2(v_inst_654_, lean_box(0), v___x_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateOfMonadLift___redArg(lean_object* v_inst_658_, lean_object* v_inst_659_){
_start:
{
lean_object* v_getCommRingState_660_; lean_object* v_modifyCommRingState_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_670_; 
v_getCommRingState_660_ = lean_ctor_get(v_inst_659_, 0);
v_modifyCommRingState_661_ = lean_ctor_get(v_inst_659_, 1);
v_isSharedCheck_670_ = !lean_is_exclusive(v_inst_659_);
if (v_isSharedCheck_670_ == 0)
{
v___x_663_ = v_inst_659_;
v_isShared_664_ = v_isSharedCheck_670_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_modifyCommRingState_661_);
lean_inc(v_getCommRingState_660_);
lean_dec(v_inst_659_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_670_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___f_665_; lean_object* v___x_666_; lean_object* v___x_668_; 
lean_inc(v_inst_658_);
v___f_665_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_665_, 0, v_modifyCommRingState_661_);
lean_closure_set(v___f_665_, 1, v_inst_658_);
v___x_666_ = lean_apply_2(v_inst_658_, lean_box(0), v_getCommRingState_660_);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 1, v___f_665_);
lean_ctor_set(v___x_663_, 0, v___x_666_);
v___x_668_ = v___x_663_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v___f_665_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateOfMonadLift(lean_object* v_m_671_, lean_object* v_n_672_, lean_object* v_inst_673_, lean_object* v_inst_674_){
_start:
{
lean_object* v_getCommRingState_675_; lean_object* v_modifyCommRingState_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_685_; 
v_getCommRingState_675_ = lean_ctor_get(v_inst_674_, 0);
v_modifyCommRingState_676_ = lean_ctor_get(v_inst_674_, 1);
v_isSharedCheck_685_ = !lean_is_exclusive(v_inst_674_);
if (v_isSharedCheck_685_ == 0)
{
v___x_678_ = v_inst_674_;
v_isShared_679_ = v_isSharedCheck_685_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_modifyCommRingState_676_);
lean_inc(v_getCommRingState_675_);
lean_dec(v_inst_674_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_685_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___f_680_; lean_object* v___x_681_; lean_object* v___x_683_; 
lean_inc(v_inst_673_);
v___f_680_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_680_, 0, v_modifyCommRingState_676_);
lean_closure_set(v___f_680_, 1, v_inst_673_);
v___x_681_ = lean_apply_2(v_inst_673_, lean_box(0), v_getCommRingState_675_);
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 1, v___f_680_);
lean_ctor_set(v___x_678_, 0, v___x_681_);
v___x_683_ = v___x_678_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_681_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v___f_680_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__0(lean_object* v_f_686_, lean_object* v_s_687_){
_start:
{
lean_object* v_toRingState_688_; lean_object* v_denoteEntries_689_; lean_object* v_nextId_690_; lean_object* v_steps_691_; lean_object* v_queue_692_; lean_object* v_basis_693_; lean_object* v_diseqs_694_; uint8_t v_recheck_695_; lean_object* v_invSet_696_; lean_object* v_powIdentityVarCount_697_; lean_object* v_numEq0_x3f_698_; uint8_t v_numEq0Updated_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_707_; 
v_toRingState_688_ = lean_ctor_get(v_s_687_, 0);
v_denoteEntries_689_ = lean_ctor_get(v_s_687_, 1);
v_nextId_690_ = lean_ctor_get(v_s_687_, 2);
v_steps_691_ = lean_ctor_get(v_s_687_, 3);
v_queue_692_ = lean_ctor_get(v_s_687_, 4);
v_basis_693_ = lean_ctor_get(v_s_687_, 5);
v_diseqs_694_ = lean_ctor_get(v_s_687_, 6);
v_recheck_695_ = lean_ctor_get_uint8(v_s_687_, sizeof(void*)*10);
v_invSet_696_ = lean_ctor_get(v_s_687_, 7);
v_powIdentityVarCount_697_ = lean_ctor_get(v_s_687_, 8);
v_numEq0_x3f_698_ = lean_ctor_get(v_s_687_, 9);
v_numEq0Updated_699_ = lean_ctor_get_uint8(v_s_687_, sizeof(void*)*10 + 1);
v_isSharedCheck_707_ = !lean_is_exclusive(v_s_687_);
if (v_isSharedCheck_707_ == 0)
{
v___x_701_ = v_s_687_;
v_isShared_702_ = v_isSharedCheck_707_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_numEq0_x3f_698_);
lean_inc(v_powIdentityVarCount_697_);
lean_inc(v_invSet_696_);
lean_inc(v_diseqs_694_);
lean_inc(v_basis_693_);
lean_inc(v_queue_692_);
lean_inc(v_steps_691_);
lean_inc(v_nextId_690_);
lean_inc(v_denoteEntries_689_);
lean_inc(v_toRingState_688_);
lean_dec(v_s_687_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_707_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_703_; lean_object* v___x_705_; 
v___x_703_ = lean_apply_1(v_f_686_, v_toRingState_688_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 0, v___x_703_);
v___x_705_ = v___x_701_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_703_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v_denoteEntries_689_);
lean_ctor_set(v_reuseFailAlloc_706_, 2, v_nextId_690_);
lean_ctor_set(v_reuseFailAlloc_706_, 3, v_steps_691_);
lean_ctor_set(v_reuseFailAlloc_706_, 4, v_queue_692_);
lean_ctor_set(v_reuseFailAlloc_706_, 5, v_basis_693_);
lean_ctor_set(v_reuseFailAlloc_706_, 6, v_diseqs_694_);
lean_ctor_set(v_reuseFailAlloc_706_, 7, v_invSet_696_);
lean_ctor_set(v_reuseFailAlloc_706_, 8, v_powIdentityVarCount_697_);
lean_ctor_set(v_reuseFailAlloc_706_, 9, v_numEq0_x3f_698_);
lean_ctor_set_uint8(v_reuseFailAlloc_706_, sizeof(void*)*10, v_recheck_695_);
lean_ctor_set_uint8(v_reuseFailAlloc_706_, sizeof(void*)*10 + 1, v_numEq0Updated_699_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__1(lean_object* v_modifyCommRingState_708_, lean_object* v_f_709_){
_start:
{
lean_object* v___f_710_; lean_object* v___x_711_; 
v___f_710_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__0), 2, 1);
lean_closure_set(v___f_710_, 0, v_f_709_);
v___x_711_ = lean_apply_1(v_modifyCommRingState_708_, v___f_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__2(lean_object* v_toPure_712_, lean_object* v_____do__lift_713_){
_start:
{
lean_object* v_toRingState_714_; lean_object* v___x_715_; 
v_toRingState_714_ = lean_ctor_get(v_____do__lift_713_, 0);
lean_inc_ref(v_toRingState_714_);
lean_dec_ref(v_____do__lift_713_);
v___x_715_ = lean_apply_2(v_toPure_712_, lean_box(0), v_toRingState_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg(lean_object* v_inst_716_, lean_object* v_inst_717_){
_start:
{
lean_object* v_toApplicative_718_; lean_object* v_toBind_719_; lean_object* v_getCommRingState_720_; lean_object* v_modifyCommRingState_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_732_; 
v_toApplicative_718_ = lean_ctor_get(v_inst_716_, 0);
lean_inc_ref(v_toApplicative_718_);
v_toBind_719_ = lean_ctor_get(v_inst_716_, 1);
lean_inc(v_toBind_719_);
lean_dec_ref(v_inst_716_);
v_getCommRingState_720_ = lean_ctor_get(v_inst_717_, 0);
v_modifyCommRingState_721_ = lean_ctor_get(v_inst_717_, 1);
v_isSharedCheck_732_ = !lean_is_exclusive(v_inst_717_);
if (v_isSharedCheck_732_ == 0)
{
v___x_723_ = v_inst_717_;
v_isShared_724_ = v_isSharedCheck_732_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_modifyCommRingState_721_);
lean_inc(v_getCommRingState_720_);
lean_dec(v_inst_717_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_732_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v_toPure_725_; lean_object* v___f_726_; lean_object* v___f_727_; lean_object* v___x_728_; lean_object* v___x_730_; 
v_toPure_725_ = lean_ctor_get(v_toApplicative_718_, 1);
lean_inc(v_toPure_725_);
lean_dec_ref(v_toApplicative_718_);
v___f_726_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__1), 2, 1);
lean_closure_set(v___f_726_, 0, v_modifyCommRingState_721_);
v___f_727_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__2), 2, 1);
lean_closure_set(v___f_727_, 0, v_toPure_725_);
v___x_728_ = lean_apply_4(v_toBind_719_, lean_box(0), lean_box(0), v_getCommRingState_720_, v___f_727_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 1, v___f_726_);
lean_ctor_set(v___x_723_, 0, v___x_728_);
v___x_730_ = v___x_723_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_728_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v___f_726_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState(lean_object* v_m_733_, lean_object* v_inst_734_, lean_object* v_inst_735_){
_start:
{
lean_object* v_toApplicative_736_; lean_object* v_toBind_737_; lean_object* v_getCommRingState_738_; lean_object* v_modifyCommRingState_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_750_; 
v_toApplicative_736_ = lean_ctor_get(v_inst_734_, 0);
lean_inc_ref(v_toApplicative_736_);
v_toBind_737_ = lean_ctor_get(v_inst_734_, 1);
lean_inc(v_toBind_737_);
lean_dec_ref(v_inst_734_);
v_getCommRingState_738_ = lean_ctor_get(v_inst_735_, 0);
v_modifyCommRingState_739_ = lean_ctor_get(v_inst_735_, 1);
v_isSharedCheck_750_ = !lean_is_exclusive(v_inst_735_);
if (v_isSharedCheck_750_ == 0)
{
v___x_741_ = v_inst_735_;
v_isShared_742_ = v_isSharedCheck_750_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_modifyCommRingState_739_);
lean_inc(v_getCommRingState_738_);
lean_dec(v_inst_735_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_750_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v_toPure_743_; lean_object* v___f_744_; lean_object* v___f_745_; lean_object* v___x_746_; lean_object* v___x_748_; 
v_toPure_743_ = lean_ctor_get(v_toApplicative_736_, 1);
lean_inc(v_toPure_743_);
lean_dec_ref(v_toApplicative_736_);
v___f_744_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__1), 2, 1);
lean_closure_set(v___f_744_, 0, v_modifyCommRingState_739_);
v___f_745_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingStateOfMonadOfMonadCommRingState___redArg___lam__2), 2, 1);
lean_closure_set(v___f_745_, 0, v_toPure_743_);
v___x_746_ = lean_apply_4(v_toBind_737_, lean_box(0), lean_box(0), v_getCommRingState_738_, v___f_745_);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 1, v___f_744_);
lean_ctor_set(v___x_741_, 0, v___x_746_);
v___x_748_ = v___x_741_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_746_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v___f_744_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateOfMonadLift___redArg___lam__0(lean_object* v_modifySemiringState_751_, lean_object* v_inst_752_, lean_object* v_f_753_){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_754_ = lean_apply_1(v_modifySemiringState_751_, v_f_753_);
v___x_755_ = lean_apply_2(v_inst_752_, lean_box(0), v___x_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateOfMonadLift___redArg(lean_object* v_inst_756_, lean_object* v_inst_757_){
_start:
{
lean_object* v_getSemiringState_758_; lean_object* v_modifySemiringState_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_768_; 
v_getSemiringState_758_ = lean_ctor_get(v_inst_757_, 0);
v_modifySemiringState_759_ = lean_ctor_get(v_inst_757_, 1);
v_isSharedCheck_768_ = !lean_is_exclusive(v_inst_757_);
if (v_isSharedCheck_768_ == 0)
{
v___x_761_ = v_inst_757_;
v_isShared_762_ = v_isSharedCheck_768_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_modifySemiringState_759_);
lean_inc(v_getSemiringState_758_);
lean_dec(v_inst_757_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_768_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___f_763_; lean_object* v___x_764_; lean_object* v___x_766_; 
lean_inc(v_inst_756_);
v___f_763_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_763_, 0, v_modifySemiringState_759_);
lean_closure_set(v___f_763_, 1, v_inst_756_);
v___x_764_ = lean_apply_2(v_inst_756_, lean_box(0), v_getSemiringState_758_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 1, v___f_763_);
lean_ctor_set(v___x_761_, 0, v___x_764_);
v___x_766_ = v___x_761_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v___f_763_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateOfMonadLift(lean_object* v_m_769_, lean_object* v_n_770_, lean_object* v_inst_771_, lean_object* v_inst_772_){
_start:
{
lean_object* v_getSemiringState_773_; lean_object* v_modifySemiringState_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_783_; 
v_getSemiringState_773_ = lean_ctor_get(v_inst_772_, 0);
v_modifySemiringState_774_ = lean_ctor_get(v_inst_772_, 1);
v_isSharedCheck_783_ = !lean_is_exclusive(v_inst_772_);
if (v_isSharedCheck_783_ == 0)
{
v___x_776_ = v_inst_772_;
v_isShared_777_ = v_isSharedCheck_783_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_modifySemiringState_774_);
lean_inc(v_getSemiringState_773_);
lean_dec(v_inst_772_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_783_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___f_778_; lean_object* v___x_779_; lean_object* v___x_781_; 
lean_inc(v_inst_771_);
v___f_778_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadSemiringStateOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_778_, 0, v_modifySemiringState_774_);
lean_closure_set(v___f_778_, 1, v_inst_771_);
v___x_779_ = lean_apply_2(v_inst_771_, lean_box(0), v_getSemiringState_773_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 1, v___f_778_);
lean_ctor_set(v___x_776_, 0, v___x_779_);
v___x_781_ = v___x_776_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_779_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v___f_778_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
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
