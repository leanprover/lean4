// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.Var
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Types import Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat import Lean.Meta.IntInstTesters
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
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHMulInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
uint64_t lean_uint64_of_nat(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Meta_Structural_isInstHAddInt___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHDivInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHModInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHPowInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_cutsat_mk_var(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t l_Int_Internal_Linear_Poly_isZero(lean_object*);
lean_object* lean_cutsat_propagate_nonlinear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNonlinearTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hPow"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__1_value),LEAN_SCALAR_PTR_LITERAL(32, 63, 208, 57, 56, 184, 164, 144)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__3_value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__4_value),LEAN_SCALAR_PTR_LITERAL(120, 199, 142, 238, 9, 44, 94, 134)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__6_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__7_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__9_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__10_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lia"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "internalize"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__2_value),LEAN_SCALAR_PTR_LITERAL(87, 130, 109, 65, 232, 6, 169, 172)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__3_value),LEAN_SCALAR_PTR_LITERAL(34, 238, 188, 187, 128, 53, 130, 20)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__5_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 4, .m_data = " ↦ #"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9;
LEAN_EXPORT lean_object* lean_grind_cutsat_mk_var(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "found term with non-standard instance"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "monomial expected, found numeral"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "\ninternalizing as variable"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_propagateNonlinearTerm_0interp(lean_interpreter_value* stack)
{
lean_object* v_y_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
lean_object* v_a_3_ = stack[2].m_obj;
lean_object* v_a_4_ = stack[3].m_obj;
lean_object* v_a_5_ = stack[4].m_obj;
lean_object* v_a_6_ = stack[5].m_obj;
lean_object* v_a_7_ = stack[6].m_obj;
lean_object* v_a_8_ = stack[7].m_obj;
lean_object* v_a_9_ = stack[8].m_obj;
lean_object* v_a_10_ = stack[9].m_obj;
lean_object* v_a_11_ = stack[10].m_obj;
lean_object* v_a_12_ = stack[11].m_obj;
lean_object* v_res_14_;
v_res_14_ = lean_cutsat_propagate_nonlinear(v_y_1_, v_x_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
stack->m_obj
 = v_res_14_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNonlinearTerm___boxed(lean_object* v_y_15_, lean_object* v_x_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_00___x40___internal___hyg_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = lean_cutsat_propagate_nonlinear(v_y_15_, v_x_16_, v_a_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_, v_a_26_);
return v_res_28_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm(lean_object* v_e_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_49_, v_a_51_);
if (lean_obj_tag(v___x_59_) == 0)
{
lean_object* v_a_60_; lean_object* v___x_61_; uint8_t v___x_62_; 
v_a_60_ = lean_ctor_get(v___x_59_, 0);
lean_inc(v_a_60_);
lean_dec_ref_known(v___x_59_, 1);
v___x_61_ = l_Lean_Expr_cleanupAnnotations(v_a_60_);
v___x_62_ = l_Lean_Expr_isApp(v___x_61_);
if (v___x_62_ == 0)
{
lean_dec_ref(v___x_61_);
goto v___jp_55_;
}
else
{
lean_object* v_arg_63_; lean_object* v___x_64_; uint8_t v___x_65_; 
v_arg_63_ = lean_ctor_get(v___x_61_, 1);
lean_inc_ref(v_arg_63_);
v___x_64_ = l_Lean_Expr_appFnCleanup___redArg(v___x_61_);
v___x_65_ = l_Lean_Expr_isApp(v___x_64_);
if (v___x_65_ == 0)
{
lean_dec_ref(v___x_64_);
lean_dec_ref(v_arg_63_);
goto v___jp_55_;
}
else
{
lean_object* v_arg_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
v_arg_66_ = lean_ctor_get(v___x_64_, 1);
lean_inc_ref(v_arg_66_);
v___x_67_ = l_Lean_Expr_appFnCleanup___redArg(v___x_64_);
v___x_68_ = l_Lean_Expr_isApp(v___x_67_);
if (v___x_68_ == 0)
{
lean_dec_ref(v___x_67_);
lean_dec_ref(v_arg_66_);
lean_dec_ref(v_arg_63_);
goto v___jp_55_;
}
else
{
lean_object* v_arg_69_; lean_object* v___x_70_; uint8_t v___x_71_; 
v_arg_69_ = lean_ctor_get(v___x_67_, 1);
lean_inc_ref(v_arg_69_);
v___x_70_ = l_Lean_Expr_appFnCleanup___redArg(v___x_67_);
v___x_71_ = l_Lean_Expr_isApp(v___x_70_);
if (v___x_71_ == 0)
{
lean_dec_ref(v___x_70_);
lean_dec_ref(v_arg_69_);
lean_dec_ref(v_arg_66_);
lean_dec_ref(v_arg_63_);
goto v___jp_55_;
}
else
{
lean_object* v___x_72_; uint8_t v___x_73_; 
v___x_72_ = l_Lean_Expr_appFnCleanup___redArg(v___x_70_);
v___x_73_ = l_Lean_Expr_isApp(v___x_72_);
if (v___x_73_ == 0)
{
lean_dec_ref(v___x_72_);
lean_dec_ref(v_arg_69_);
lean_dec_ref(v_arg_66_);
lean_dec_ref(v_arg_63_);
goto v___jp_55_;
}
else
{
lean_object* v___x_74_; uint8_t v___x_75_; 
v___x_74_ = l_Lean_Expr_appFnCleanup___redArg(v___x_72_);
v___x_75_ = l_Lean_Expr_isApp(v___x_74_);
if (v___x_75_ == 0)
{
lean_dec_ref(v___x_74_);
lean_dec_ref(v_arg_69_);
lean_dec_ref(v_arg_66_);
lean_dec_ref(v_arg_63_);
goto v___jp_55_;
}
else
{
lean_object* v___x_76_; lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_76_ = l_Lean_Expr_appFnCleanup___redArg(v___x_74_);
v___x_77_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__2));
v___x_78_ = l_Lean_Expr_isConstOf(v___x_76_, v___x_77_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; uint8_t v___x_80_; 
lean_dec_ref(v_arg_66_);
v___x_79_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__5));
v___x_80_ = l_Lean_Expr_isConstOf(v___x_76_, v___x_79_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_81_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__8));
v___x_82_ = l_Lean_Expr_isConstOf(v___x_76_, v___x_81_);
if (v___x_82_ == 0)
{
lean_object* v___x_83_; uint8_t v___x_84_; 
lean_dec_ref(v_arg_63_);
v___x_83_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11));
v___x_84_ = l_Lean_Expr_isConstOf(v___x_76_, v___x_83_);
lean_dec_ref(v___x_76_);
if (v___x_84_ == 0)
{
lean_dec_ref(v_arg_69_);
goto v___jp_55_;
}
else
{
lean_object* v___x_85_; 
v___x_85_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_69_, v_a_51_);
return v___x_85_;
}
}
else
{
lean_object* v___x_86_; 
lean_dec_ref(v___x_76_);
v___x_86_ = l_Lean_Meta_getIntValue_x3f(v_arg_63_, v_a_50_, v_a_51_, v_a_52_, v_a_53_);
if (lean_obj_tag(v___x_86_) == 0)
{
lean_object* v_a_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_98_; 
v_a_87_ = lean_ctor_get(v___x_86_, 0);
v_isSharedCheck_98_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_98_ == 0)
{
v___x_89_ = v___x_86_;
v_isShared_90_ = v_isSharedCheck_98_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_a_87_);
lean_dec(v___x_86_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_98_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
uint8_t v___y_92_; 
if (lean_obj_tag(v_a_87_) == 0)
{
v___y_92_ = v___x_82_;
goto v___jp_91_;
}
else
{
lean_dec_ref_known(v_a_87_, 1);
v___y_92_ = v___x_80_;
goto v___jp_91_;
}
v___jp_91_:
{
if (v___y_92_ == 0)
{
lean_object* v___x_93_; lean_object* v___x_95_; 
lean_dec_ref(v_arg_69_);
v___x_93_ = lean_box(v___y_92_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 0, v___x_93_);
v___x_95_ = v___x_89_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v___x_93_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
else
{
lean_object* v___x_97_; 
lean_del_object(v___x_89_);
v___x_97_ = l_Lean_Meta_Structural_isInstHDivInt___redArg(v_arg_69_, v_a_51_);
return v___x_97_;
}
}
}
}
else
{
lean_object* v_a_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_106_; 
lean_dec_ref(v_arg_69_);
v_a_99_ = lean_ctor_get(v___x_86_, 0);
v_isSharedCheck_106_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_106_ == 0)
{
v___x_101_ = v___x_86_;
v_isShared_102_ = v_isSharedCheck_106_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_a_99_);
lean_dec(v___x_86_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_106_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_104_; 
if (v_isShared_102_ == 0)
{
v___x_104_ = v___x_101_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_a_99_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
}
}
}
else
{
lean_object* v___x_107_; 
lean_dec_ref(v___x_76_);
v___x_107_ = l_Lean_Meta_getIntValue_x3f(v_arg_63_, v_a_50_, v_a_51_, v_a_52_, v_a_53_);
if (lean_obj_tag(v___x_107_) == 0)
{
lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_119_; 
v_a_108_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_119_ == 0)
{
v___x_110_ = v___x_107_;
v_isShared_111_ = v_isSharedCheck_119_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_a_108_);
lean_dec(v___x_107_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_119_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
uint8_t v___y_113_; 
if (lean_obj_tag(v_a_108_) == 0)
{
v___y_113_ = v___x_80_;
goto v___jp_112_;
}
else
{
lean_dec_ref_known(v_a_108_, 1);
v___y_113_ = v___x_78_;
goto v___jp_112_;
}
v___jp_112_:
{
if (v___y_113_ == 0)
{
lean_object* v___x_114_; lean_object* v___x_116_; 
lean_dec_ref(v_arg_69_);
v___x_114_ = lean_box(v___y_113_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 0, v___x_114_);
v___x_116_ = v___x_110_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_114_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
else
{
lean_object* v___x_118_; 
lean_del_object(v___x_110_);
v___x_118_ = l_Lean_Meta_Structural_isInstHModInt___redArg(v_arg_69_, v_a_51_);
return v___x_118_;
}
}
}
}
else
{
lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_127_; 
lean_dec_ref(v_arg_69_);
v_a_120_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_127_ == 0)
{
v___x_122_ = v___x_107_;
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v___x_107_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_125_; 
if (v_isShared_123_ == 0)
{
v___x_125_ = v___x_122_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_a_120_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
}
}
else
{
lean_object* v___x_128_; 
lean_dec_ref(v___x_76_);
v___x_128_ = l_Lean_Meta_Structural_isInstHPowInt___redArg(v_arg_69_, v_a_51_);
if (lean_obj_tag(v___x_128_) == 0)
{
lean_object* v_a_129_; uint8_t v___x_130_; 
v_a_129_ = lean_ctor_get(v___x_128_, 0);
v___x_130_ = lean_unbox(v_a_129_);
if (v___x_130_ == 0)
{
lean_dec_ref(v_arg_66_);
lean_dec_ref(v_arg_63_);
return v___x_128_;
}
else
{
lean_object* v___x_131_; 
lean_inc(v_a_129_);
lean_dec_ref_known(v___x_128_, 1);
v___x_131_ = l_Lean_Meta_getIntValue_x3f(v_arg_66_, v_a_50_, v_a_51_, v_a_52_, v_a_53_);
if (lean_obj_tag(v___x_131_) == 0)
{
lean_object* v_a_132_; lean_object* v___x_133_; 
v_a_132_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_a_132_);
lean_dec_ref_known(v___x_131_, 1);
v___x_133_ = l_Lean_Meta_getIntValue_x3f(v_arg_63_, v_a_50_, v_a_51_, v_a_52_, v_a_53_);
if (lean_obj_tag(v___x_133_) == 0)
{
if (lean_obj_tag(v_a_132_) == 0)
{
lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_141_; 
lean_dec(v_a_129_);
v_isSharedCheck_141_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_141_ == 0)
{
lean_object* v_unused_142_; 
v_unused_142_ = lean_ctor_get(v___x_133_, 0);
lean_dec(v_unused_142_);
v___x_135_ = v___x_133_;
v_isShared_136_ = v_isSharedCheck_141_;
goto v_resetjp_134_;
}
else
{
lean_dec(v___x_133_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_141_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_137_; lean_object* v___x_139_; 
v___x_137_ = lean_box(v___x_78_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 0, v___x_137_);
v___x_139_ = v___x_135_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_137_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
else
{
lean_object* v_a_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_155_; 
lean_dec_ref_known(v_a_132_, 1);
v_a_143_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_155_ == 0)
{
v___x_145_ = v___x_133_;
v_isShared_146_ = v_isSharedCheck_155_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_a_143_);
lean_dec(v___x_133_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_155_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
if (lean_obj_tag(v_a_143_) == 0)
{
lean_object* v___x_148_; 
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 0, v_a_129_);
v___x_148_ = v___x_145_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_a_129_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
else
{
uint8_t v___x_150_; lean_object* v___x_151_; lean_object* v___x_153_; 
lean_dec_ref_known(v_a_143_, 1);
lean_dec(v_a_129_);
v___x_150_ = 0;
v___x_151_ = lean_box(v___x_150_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 0, v___x_151_);
v___x_153_ = v___x_145_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_151_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
}
}
else
{
lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_163_; 
lean_dec(v_a_132_);
lean_dec(v_a_129_);
v_a_156_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_163_ == 0)
{
v___x_158_ = v___x_133_;
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_dec(v___x_133_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_161_; 
if (v_isShared_159_ == 0)
{
v___x_161_ = v___x_158_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_a_156_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
}
else
{
lean_object* v_a_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_171_; 
lean_dec(v_a_129_);
lean_dec_ref(v_arg_63_);
v_a_164_ = lean_ctor_get(v___x_131_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_171_ == 0)
{
v___x_166_ = v___x_131_;
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_a_164_);
lean_dec(v___x_131_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_169_; 
if (v_isShared_167_ == 0)
{
v___x_169_ = v___x_166_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_a_164_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
}
}
else
{
lean_dec_ref(v_arg_66_);
lean_dec_ref(v_arg_63_);
return v___x_128_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_179_; 
v_a_172_ = lean_ctor_get(v___x_59_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_59_);
if (v_isSharedCheck_179_ == 0)
{
v___x_174_ = v___x_59_;
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_a_172_);
lean_dec(v___x_59_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_177_; 
if (v_isShared_175_ == 0)
{
v___x_177_ = v___x_174_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_a_172_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
v___jp_55_:
{
uint8_t v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_56_ = 0;
v___x_57_ = lean_box(v___x_56_);
v___x_58_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_58_, 0, v___x_57_);
return v___x_58_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_49_ = stack[0].m_obj;
lean_object* v_a_50_ = stack[1].m_obj;
lean_object* v_a_51_ = stack[2].m_obj;
lean_object* v_a_52_ = stack[3].m_obj;
lean_object* v_a_53_ = stack[4].m_obj;
lean_object* v_res_180_;
v_res_180_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm(v_e_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_);
stack->m_obj
 = v_res_180_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___boxed(lean_object* v_e_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm(v_e_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_);
lean_dec(v_a_185_);
lean_dec_ref(v_a_184_);
lean_dec(v_a_183_);
lean_dec_ref(v_a_182_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_x_188_, lean_object* v_x_189_, lean_object* v_x_190_, lean_object* v_x_191_){
_start:
{
lean_object* v_ks_192_; lean_object* v_vs_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_217_; 
v_ks_192_ = lean_ctor_get(v_x_188_, 0);
v_vs_193_ = lean_ctor_get(v_x_188_, 1);
v_isSharedCheck_217_ = !lean_is_exclusive(v_x_188_);
if (v_isSharedCheck_217_ == 0)
{
v___x_195_ = v_x_188_;
v_isShared_196_ = v_isSharedCheck_217_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_vs_193_);
lean_inc(v_ks_192_);
lean_dec(v_x_188_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_217_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_197_ = lean_array_get_size(v_ks_192_);
v___x_198_ = lean_nat_dec_lt(v_x_189_, v___x_197_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_202_; 
lean_dec(v_x_189_);
v___x_199_ = lean_array_push(v_ks_192_, v_x_190_);
v___x_200_ = lean_array_push(v_vs_193_, v_x_191_);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 1, v___x_200_);
lean_ctor_set(v___x_195_, 0, v___x_199_);
v___x_202_ = v___x_195_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_199_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v___x_200_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
else
{
lean_object* v_k_x27_204_; uint8_t v___x_205_; 
v_k_x27_204_ = lean_array_fget_borrowed(v_ks_192_, v_x_189_);
v___x_205_ = lean_nat_dec_eq(v_x_190_, v_k_x27_204_);
if (v___x_205_ == 0)
{
lean_object* v___x_207_; 
if (v_isShared_196_ == 0)
{
v___x_207_ = v___x_195_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_ks_192_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v_vs_193_);
v___x_207_ = v_reuseFailAlloc_211_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_208_ = lean_unsigned_to_nat(1u);
v___x_209_ = lean_nat_add(v_x_189_, v___x_208_);
lean_dec(v_x_189_);
v_x_188_ = v___x_207_;
v_x_189_ = v___x_209_;
goto _start;
}
}
else
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_215_; 
v___x_212_ = lean_array_fset(v_ks_192_, v_x_189_, v_x_190_);
v___x_213_ = lean_array_fset(v_vs_193_, v_x_189_, v_x_191_);
lean_dec(v_x_189_);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 1, v___x_213_);
lean_ctor_set(v___x_195_, 0, v___x_212_);
v___x_215_ = v___x_195_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v___x_212_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v___x_213_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1___redArg(lean_object* v_n_218_, lean_object* v_k_219_, lean_object* v_v_220_){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = lean_unsigned_to_nat(0u);
v___x_222_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__4___redArg(v_n_218_, v___x_221_, v_k_219_, v_v_220_);
return v___x_222_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_223_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(lean_object* v_x_224_, size_t v_x_225_, size_t v_x_226_, lean_object* v_x_227_, lean_object* v_x_228_){
_start:
{
if (lean_obj_tag(v_x_224_) == 0)
{
lean_object* v_es_229_; size_t v___x_230_; size_t v___x_231_; lean_object* v_j_232_; lean_object* v___x_233_; uint8_t v___x_234_; 
v_es_229_ = lean_ctor_get(v_x_224_, 0);
v___x_230_ = ((size_t)31ULL);
v___x_231_ = lean_usize_land(v_x_225_, v___x_230_);
v_j_232_ = lean_usize_to_nat(v___x_231_);
v___x_233_ = lean_array_get_size(v_es_229_);
v___x_234_ = lean_nat_dec_lt(v_j_232_, v___x_233_);
if (v___x_234_ == 0)
{
lean_dec(v_j_232_);
lean_dec(v_x_228_);
lean_dec(v_x_227_);
return v_x_224_;
}
else
{
lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_273_; 
lean_inc_ref(v_es_229_);
v_isSharedCheck_273_ = !lean_is_exclusive(v_x_224_);
if (v_isSharedCheck_273_ == 0)
{
lean_object* v_unused_274_; 
v_unused_274_ = lean_ctor_get(v_x_224_, 0);
lean_dec(v_unused_274_);
v___x_236_ = v_x_224_;
v_isShared_237_ = v_isSharedCheck_273_;
goto v_resetjp_235_;
}
else
{
lean_dec(v_x_224_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_273_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v_v_238_; lean_object* v___x_239_; lean_object* v_xs_x27_240_; lean_object* v___y_242_; 
v_v_238_ = lean_array_fget(v_es_229_, v_j_232_);
v___x_239_ = lean_box(0);
v_xs_x27_240_ = lean_array_fset(v_es_229_, v_j_232_, v___x_239_);
switch(lean_obj_tag(v_v_238_))
{
case 0:
{
lean_object* v_key_247_; lean_object* v_val_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_258_; 
v_key_247_ = lean_ctor_get(v_v_238_, 0);
v_val_248_ = lean_ctor_get(v_v_238_, 1);
v_isSharedCheck_258_ = !lean_is_exclusive(v_v_238_);
if (v_isSharedCheck_258_ == 0)
{
v___x_250_ = v_v_238_;
v_isShared_251_ = v_isSharedCheck_258_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_val_248_);
lean_inc(v_key_247_);
lean_dec(v_v_238_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_258_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
uint8_t v___x_252_; 
v___x_252_ = lean_nat_dec_eq(v_x_227_, v_key_247_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; lean_object* v___x_254_; 
lean_del_object(v___x_250_);
v___x_253_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_247_, v_val_248_, v_x_227_, v_x_228_);
v___x_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
v___y_242_ = v___x_254_;
goto v___jp_241_;
}
else
{
lean_object* v___x_256_; 
lean_dec(v_val_248_);
lean_dec(v_key_247_);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 1, v_x_228_);
lean_ctor_set(v___x_250_, 0, v_x_227_);
v___x_256_ = v___x_250_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_x_227_);
lean_ctor_set(v_reuseFailAlloc_257_, 1, v_x_228_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
v___y_242_ = v___x_256_;
goto v___jp_241_;
}
}
}
}
case 1:
{
lean_object* v_node_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_271_; 
v_node_259_ = lean_ctor_get(v_v_238_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v_v_238_);
if (v_isSharedCheck_271_ == 0)
{
v___x_261_ = v_v_238_;
v_isShared_262_ = v_isSharedCheck_271_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_node_259_);
lean_dec(v_v_238_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_271_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
size_t v___x_263_; size_t v___x_264_; size_t v___x_265_; size_t v___x_266_; lean_object* v___x_267_; lean_object* v___x_269_; 
v___x_263_ = ((size_t)5ULL);
v___x_264_ = lean_usize_shift_right(v_x_225_, v___x_263_);
v___x_265_ = ((size_t)1ULL);
v___x_266_ = lean_usize_add(v_x_226_, v___x_265_);
v___x_267_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_node_259_, v___x_264_, v___x_266_, v_x_227_, v_x_228_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v___x_267_);
v___x_269_ = v___x_261_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v___x_267_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
v___y_242_ = v___x_269_;
goto v___jp_241_;
}
}
}
default: 
{
lean_object* v___x_272_; 
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v_x_227_);
lean_ctor_set(v___x_272_, 1, v_x_228_);
v___y_242_ = v___x_272_;
goto v___jp_241_;
}
}
v___jp_241_:
{
lean_object* v___x_243_; lean_object* v___x_245_; 
v___x_243_ = lean_array_fset(v_xs_x27_240_, v_j_232_, v___y_242_);
lean_dec(v_j_232_);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 0, v___x_243_);
v___x_245_ = v___x_236_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v___x_243_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
}
else
{
lean_object* v_ks_275_; lean_object* v_vs_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_294_; 
v_ks_275_ = lean_ctor_get(v_x_224_, 0);
v_vs_276_ = lean_ctor_get(v_x_224_, 1);
v_isSharedCheck_294_ = !lean_is_exclusive(v_x_224_);
if (v_isSharedCheck_294_ == 0)
{
v___x_278_ = v_x_224_;
v_isShared_279_ = v_isSharedCheck_294_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_vs_276_);
lean_inc(v_ks_275_);
lean_dec(v_x_224_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_294_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_281_; 
if (v_isShared_279_ == 0)
{
v___x_281_ = v___x_278_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_ks_275_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v_vs_276_);
v___x_281_ = v_reuseFailAlloc_293_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
lean_object* v_newNode_282_; size_t v___x_283_; uint8_t v___x_284_; 
v_newNode_282_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1___redArg(v___x_281_, v_x_227_, v_x_228_);
v___x_283_ = ((size_t)7ULL);
v___x_284_ = lean_usize_dec_le(v___x_283_, v_x_226_);
if (v___x_284_ == 0)
{
lean_object* v___x_285_; lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_285_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_282_);
v___x_286_ = lean_unsigned_to_nat(4u);
v___x_287_ = lean_nat_dec_lt(v___x_285_, v___x_286_);
lean_dec(v___x_285_);
if (v___x_287_ == 0)
{
lean_object* v_ks_288_; lean_object* v_vs_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v_ks_288_ = lean_ctor_get(v_newNode_282_, 0);
lean_inc_ref(v_ks_288_);
v_vs_289_ = lean_ctor_get(v_newNode_282_, 1);
lean_inc_ref(v_vs_289_);
lean_dec_ref(v_newNode_282_);
v___x_290_ = lean_unsigned_to_nat(0u);
v___x_291_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0);
v___x_292_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg(v_x_226_, v_ks_288_, v_vs_289_, v___x_290_, v___x_291_);
lean_dec_ref(v_vs_289_);
lean_dec_ref(v_ks_288_);
return v___x_292_;
}
else
{
return v_newNode_282_;
}
}
else
{
return v_newNode_282_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_224_ = stack[0].m_obj;
size_t v_x_225_ = stack[1].m_num;
size_t v_x_226_ = stack[2].m_num;
lean_object* v_x_227_ = stack[3].m_obj;
lean_object* v_x_228_ = stack[4].m_obj;
lean_object* v_res_295_;
v_res_295_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_x_224_, v_x_225_, v_x_226_, v_x_227_, v_x_228_);
stack->m_obj
 = v_res_295_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg(size_t v_depth_296_, lean_object* v_keys_297_, lean_object* v_vals_298_, lean_object* v_i_299_, lean_object* v_entries_300_){
_start:
{
lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_301_ = lean_array_get_size(v_keys_297_);
v___x_302_ = lean_nat_dec_lt(v_i_299_, v___x_301_);
if (v___x_302_ == 0)
{
lean_dec(v_i_299_);
return v_entries_300_;
}
else
{
lean_object* v_k_303_; lean_object* v_v_304_; uint64_t v___x_305_; size_t v_h_306_; size_t v___x_307_; lean_object* v___x_308_; size_t v___x_309_; size_t v___x_310_; size_t v___x_311_; size_t v_h_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v_k_303_ = lean_array_fget_borrowed(v_keys_297_, v_i_299_);
v_v_304_ = lean_array_fget_borrowed(v_vals_298_, v_i_299_);
v___x_305_ = lean_uint64_of_nat(v_k_303_);
v_h_306_ = lean_uint64_to_usize(v___x_305_);
v___x_307_ = ((size_t)5ULL);
v___x_308_ = lean_unsigned_to_nat(1u);
v___x_309_ = ((size_t)1ULL);
v___x_310_ = lean_usize_sub(v_depth_296_, v___x_309_);
v___x_311_ = lean_usize_mul(v___x_307_, v___x_310_);
v_h_312_ = lean_usize_shift_right(v_h_306_, v___x_311_);
v___x_313_ = lean_nat_add(v_i_299_, v___x_308_);
lean_dec(v_i_299_);
lean_inc(v_v_304_);
lean_inc(v_k_303_);
v___x_314_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_entries_300_, v_h_312_, v_depth_296_, v_k_303_, v_v_304_);
v_i_299_ = v___x_313_;
v_entries_300_ = v___x_314_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_296_ = stack[0].m_num;
lean_object* v_keys_297_ = stack[1].m_obj;
lean_object* v_vals_298_ = stack[2].m_obj;
lean_object* v_i_299_ = stack[3].m_obj;
lean_object* v_entries_300_ = stack[4].m_obj;
lean_object* v_res_316_;
v_res_316_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg(v_depth_296_, v_keys_297_, v_vals_298_, v_i_299_, v_entries_300_);
stack->m_obj
 = v_res_316_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_317_, lean_object* v_keys_318_, lean_object* v_vals_319_, lean_object* v_i_320_, lean_object* v_entries_321_){
_start:
{
size_t v_depth_boxed_322_; lean_object* v_res_323_; 
v_depth_boxed_322_ = lean_unbox_usize(v_depth_317_);
lean_dec(v_depth_317_);
v_res_323_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg(v_depth_boxed_322_, v_keys_318_, v_vals_319_, v_i_320_, v_entries_321_);
lean_dec_ref(v_vals_319_);
lean_dec_ref(v_keys_318_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___boxed(lean_object* v_x_324_, lean_object* v_x_325_, lean_object* v_x_326_, lean_object* v_x_327_, lean_object* v_x_328_){
_start:
{
size_t v_x_7972__boxed_329_; size_t v_x_7973__boxed_330_; lean_object* v_res_331_; 
v_x_7972__boxed_329_ = lean_unbox_usize(v_x_325_);
lean_dec(v_x_325_);
v_x_7973__boxed_330_ = lean_unbox_usize(v_x_326_);
lean_dec(v_x_326_);
v_res_331_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_x_324_, v_x_7972__boxed_329_, v_x_7973__boxed_330_, v_x_327_, v_x_328_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0___redArg(lean_object* v_x_332_, lean_object* v_x_333_, lean_object* v_x_334_){
_start:
{
uint64_t v___x_335_; size_t v___x_336_; size_t v___x_337_; lean_object* v___x_338_; 
v___x_335_ = lean_uint64_of_nat(v_x_333_);
v___x_336_ = lean_uint64_to_usize(v___x_335_);
v___x_337_ = ((size_t)1ULL);
v___x_338_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_x_332_, v___x_336_, v___x_337_, v_x_333_, v_x_334_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___lam__0(lean_object* v_x_339_, lean_object* v___y_340_, lean_object* v_a_341_, lean_object* v_s_342_){
_start:
{
lean_object* v_vars_343_; lean_object* v_varMap_344_; lean_object* v_varsHistory_345_; lean_object* v_natToIntMap_346_; lean_object* v_natDef_347_; lean_object* v_dvds_348_; lean_object* v_lowers_349_; lean_object* v_uppers_350_; lean_object* v_diseqs_351_; lean_object* v_elimEqs_352_; lean_object* v_elimStack_353_; lean_object* v_occurs_354_; lean_object* v_assignment_355_; lean_object* v_nextCnstrId_356_; uint8_t v_caseSplits_357_; lean_object* v_steps_358_; lean_object* v_conflict_x3f_359_; lean_object* v_diseqSplits_360_; lean_object* v_divMod_361_; uint8_t v_usedCommRing_362_; lean_object* v_nonlinearOccs_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_372_; 
v_vars_343_ = lean_ctor_get(v_s_342_, 0);
v_varMap_344_ = lean_ctor_get(v_s_342_, 1);
v_varsHistory_345_ = lean_ctor_get(v_s_342_, 2);
v_natToIntMap_346_ = lean_ctor_get(v_s_342_, 3);
v_natDef_347_ = lean_ctor_get(v_s_342_, 4);
v_dvds_348_ = lean_ctor_get(v_s_342_, 5);
v_lowers_349_ = lean_ctor_get(v_s_342_, 6);
v_uppers_350_ = lean_ctor_get(v_s_342_, 7);
v_diseqs_351_ = lean_ctor_get(v_s_342_, 8);
v_elimEqs_352_ = lean_ctor_get(v_s_342_, 9);
v_elimStack_353_ = lean_ctor_get(v_s_342_, 10);
v_occurs_354_ = lean_ctor_get(v_s_342_, 11);
v_assignment_355_ = lean_ctor_get(v_s_342_, 12);
v_nextCnstrId_356_ = lean_ctor_get(v_s_342_, 13);
v_caseSplits_357_ = lean_ctor_get_uint8(v_s_342_, sizeof(void*)*19);
v_steps_358_ = lean_ctor_get(v_s_342_, 14);
v_conflict_x3f_359_ = lean_ctor_get(v_s_342_, 15);
v_diseqSplits_360_ = lean_ctor_get(v_s_342_, 16);
v_divMod_361_ = lean_ctor_get(v_s_342_, 17);
v_usedCommRing_362_ = lean_ctor_get_uint8(v_s_342_, sizeof(void*)*19 + 1);
v_nonlinearOccs_363_ = lean_ctor_get(v_s_342_, 18);
v_isSharedCheck_372_ = !lean_is_exclusive(v_s_342_);
if (v_isSharedCheck_372_ == 0)
{
v___x_365_ = v_s_342_;
v_isShared_366_ = v_isSharedCheck_372_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_nonlinearOccs_363_);
lean_inc(v_divMod_361_);
lean_inc(v_diseqSplits_360_);
lean_inc(v_conflict_x3f_359_);
lean_inc(v_steps_358_);
lean_inc(v_nextCnstrId_356_);
lean_inc(v_assignment_355_);
lean_inc(v_occurs_354_);
lean_inc(v_elimStack_353_);
lean_inc(v_elimEqs_352_);
lean_inc(v_diseqs_351_);
lean_inc(v_uppers_350_);
lean_inc(v_lowers_349_);
lean_inc(v_dvds_348_);
lean_inc(v_natDef_347_);
lean_inc(v_natToIntMap_346_);
lean_inc(v_varsHistory_345_);
lean_inc(v_varMap_344_);
lean_inc(v_vars_343_);
lean_dec(v_s_342_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_372_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_370_; 
v___x_367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_367_, 0, v_x_339_);
lean_ctor_set(v___x_367_, 1, v___y_340_);
v___x_368_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0___redArg(v_nonlinearOccs_363_, v_a_341_, v___x_367_);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 18, v___x_368_);
v___x_370_ = v___x_365_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_vars_343_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v_varMap_344_);
lean_ctor_set(v_reuseFailAlloc_371_, 2, v_varsHistory_345_);
lean_ctor_set(v_reuseFailAlloc_371_, 3, v_natToIntMap_346_);
lean_ctor_set(v_reuseFailAlloc_371_, 4, v_natDef_347_);
lean_ctor_set(v_reuseFailAlloc_371_, 5, v_dvds_348_);
lean_ctor_set(v_reuseFailAlloc_371_, 6, v_lowers_349_);
lean_ctor_set(v_reuseFailAlloc_371_, 7, v_uppers_350_);
lean_ctor_set(v_reuseFailAlloc_371_, 8, v_diseqs_351_);
lean_ctor_set(v_reuseFailAlloc_371_, 9, v_elimEqs_352_);
lean_ctor_set(v_reuseFailAlloc_371_, 10, v_elimStack_353_);
lean_ctor_set(v_reuseFailAlloc_371_, 11, v_occurs_354_);
lean_ctor_set(v_reuseFailAlloc_371_, 12, v_assignment_355_);
lean_ctor_set(v_reuseFailAlloc_371_, 13, v_nextCnstrId_356_);
lean_ctor_set(v_reuseFailAlloc_371_, 14, v_steps_358_);
lean_ctor_set(v_reuseFailAlloc_371_, 15, v_conflict_x3f_359_);
lean_ctor_set(v_reuseFailAlloc_371_, 16, v_diseqSplits_360_);
lean_ctor_set(v_reuseFailAlloc_371_, 17, v_divMod_361_);
lean_ctor_set(v_reuseFailAlloc_371_, 18, v___x_368_);
lean_ctor_set_uint8(v_reuseFailAlloc_371_, sizeof(void*)*19, v_caseSplits_357_);
lean_ctor_set_uint8(v_reuseFailAlloc_371_, sizeof(void*)*19 + 1, v_usedCommRing_362_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
}
uint8_t l_List_elem___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1(lean_object* v_a_373_, lean_object* v_x_374_){
_start:
{
if (lean_obj_tag(v_x_374_) == 0)
{
uint8_t v___x_375_; 
v___x_375_ = 0;
return v___x_375_;
}
else
{
lean_object* v_head_376_; lean_object* v_tail_377_; uint8_t v___x_378_; 
v_head_376_ = lean_ctor_get(v_x_374_, 0);
v_tail_377_ = lean_ctor_get(v_x_374_, 1);
v___x_378_ = lean_nat_dec_eq(v_a_373_, v_head_376_);
if (v___x_378_ == 0)
{
v_x_374_ = v_tail_377_;
goto _start;
}
else
{
return v___x_378_;
}
}
}
}
LEAN_EXPORT void l_List_elem___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_373_ = stack[0].m_obj;
lean_object* v_x_374_ = stack[1].m_obj;
uint8_t v_res_380_;
v_res_380_ = l_List_elem___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1(v_a_373_, v_x_374_);
stack->m_num = v_res_380_;
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___boxed(lean_object* v_a_381_, lean_object* v_x_382_){
_start:
{
uint8_t v_res_383_; lean_object* v_r_384_; 
v_res_383_ = l_List_elem___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1(v_a_381_, v_x_382_);
lean_dec(v_x_382_);
lean_dec(v_a_381_);
v_r_384_ = lean_box(v_res_383_);
return v_r_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6___redArg(lean_object* v_keys_385_, lean_object* v_vals_386_, lean_object* v_i_387_, lean_object* v_k_388_){
_start:
{
lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_389_ = lean_array_get_size(v_keys_385_);
v___x_390_ = lean_nat_dec_lt(v_i_387_, v___x_389_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; 
lean_dec(v_i_387_);
v___x_391_ = lean_box(0);
return v___x_391_;
}
else
{
lean_object* v_k_x27_392_; uint8_t v___x_393_; 
v_k_x27_392_ = lean_array_fget_borrowed(v_keys_385_, v_i_387_);
v___x_393_ = lean_nat_dec_eq(v_k_388_, v_k_x27_392_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = lean_unsigned_to_nat(1u);
v___x_395_ = lean_nat_add(v_i_387_, v___x_394_);
lean_dec(v_i_387_);
v_i_387_ = v___x_395_;
goto _start;
}
else
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = lean_array_fget_borrowed(v_vals_386_, v_i_387_);
lean_dec(v_i_387_);
lean_inc(v___x_397_);
v___x_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
return v___x_398_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_keys_399_, lean_object* v_vals_400_, lean_object* v_i_401_, lean_object* v_k_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6___redArg(v_keys_399_, v_vals_400_, v_i_401_, v_k_402_);
lean_dec(v_k_402_);
lean_dec_ref(v_vals_400_);
lean_dec_ref(v_keys_399_);
return v_res_403_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___redArg(lean_object* v_x_404_, size_t v_x_405_, lean_object* v_x_406_){
_start:
{
if (lean_obj_tag(v_x_404_) == 0)
{
lean_object* v_es_407_; lean_object* v___x_408_; size_t v___x_409_; size_t v___x_410_; lean_object* v_j_411_; lean_object* v___x_412_; 
v_es_407_ = lean_ctor_get(v_x_404_, 0);
v___x_408_ = lean_box(2);
v___x_409_ = ((size_t)31ULL);
v___x_410_ = lean_usize_land(v_x_405_, v___x_409_);
v_j_411_ = lean_usize_to_nat(v___x_410_);
v___x_412_ = lean_array_get_borrowed(v___x_408_, v_es_407_, v_j_411_);
lean_dec(v_j_411_);
switch(lean_obj_tag(v___x_412_))
{
case 0:
{
lean_object* v_key_413_; lean_object* v_val_414_; uint8_t v___x_415_; 
v_key_413_ = lean_ctor_get(v___x_412_, 0);
v_val_414_ = lean_ctor_get(v___x_412_, 1);
v___x_415_ = lean_nat_dec_eq(v_x_406_, v_key_413_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; 
v___x_416_ = lean_box(0);
return v___x_416_;
}
else
{
lean_object* v___x_417_; 
lean_inc(v_val_414_);
v___x_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_417_, 0, v_val_414_);
return v___x_417_;
}
}
case 1:
{
lean_object* v_node_418_; size_t v___x_419_; size_t v___x_420_; 
v_node_418_ = lean_ctor_get(v___x_412_, 0);
v___x_419_ = ((size_t)5ULL);
v___x_420_ = lean_usize_shift_right(v_x_405_, v___x_419_);
v_x_404_ = v_node_418_;
v_x_405_ = v___x_420_;
goto _start;
}
default: 
{
lean_object* v___x_422_; 
v___x_422_ = lean_box(0);
return v___x_422_;
}
}
}
else
{
lean_object* v_ks_423_; lean_object* v_vs_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v_ks_423_ = lean_ctor_get(v_x_404_, 0);
v_vs_424_ = lean_ctor_get(v_x_404_, 1);
v___x_425_ = lean_unsigned_to_nat(0u);
v___x_426_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6___redArg(v_ks_423_, v_vs_424_, v___x_425_, v_x_406_);
return v___x_426_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_404_ = stack[0].m_obj;
size_t v_x_405_ = stack[1].m_num;
lean_object* v_x_406_ = stack[2].m_obj;
lean_object* v_res_427_;
v_res_427_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___redArg(v_x_404_, v_x_405_, v_x_406_);
stack->m_obj
 = v_res_427_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___redArg___boxed(lean_object* v_x_428_, lean_object* v_x_429_, lean_object* v_x_430_){
_start:
{
size_t v_x_8309__boxed_431_; lean_object* v_res_432_; 
v_x_8309__boxed_431_ = lean_unbox_usize(v_x_429_);
lean_dec(v_x_429_);
v_res_432_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___redArg(v_x_428_, v_x_8309__boxed_431_, v_x_430_);
lean_dec(v_x_430_);
lean_dec_ref(v_x_428_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2___redArg(lean_object* v_x_433_, lean_object* v_x_434_){
_start:
{
uint64_t v___x_435_; size_t v___x_436_; lean_object* v___x_437_; 
v___x_435_ = lean_uint64_of_nat(v_x_434_);
v___x_436_ = lean_uint64_to_usize(v___x_435_);
v___x_437_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___redArg(v_x_433_, v___x_436_, v_x_434_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2___redArg___boxed(lean_object* v_x_438_, lean_object* v_x_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2___redArg(v_x_438_, v_x_439_);
lean_dec(v_x_439_);
lean_dec_ref(v_x_438_);
return v_res_440_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(lean_object* v_arg_441_, lean_object* v_x_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_454_ = lean_box(0);
lean_inc(v_a_452_);
lean_inc_ref(v_a_451_);
lean_inc(v_a_450_);
lean_inc_ref(v_a_449_);
lean_inc(v_a_448_);
lean_inc_ref(v_a_447_);
lean_inc(v_a_446_);
lean_inc_ref(v_a_445_);
lean_inc(v_a_444_);
lean_inc(v_a_443_);
v___x_455_ = lean_grind_cutsat_mk_var(v_arg_441_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_524_; 
v_a_456_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_524_ == 0)
{
v___x_458_ = v___x_455_;
v_isShared_459_ = v_isSharedCheck_524_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_455_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_524_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___y_461_; lean_object* v___y_462_; lean_object* v___y_472_; lean_object* v___y_473_; lean_object* v___x_488_; 
v___x_488_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_443_, v_a_451_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; lean_object* v___y_491_; lean_object* v_elimEqs_511_; lean_object* v_size_512_; uint8_t v___x_513_; 
v_a_489_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_a_489_);
lean_dec_ref_known(v___x_488_, 1);
v_elimEqs_511_ = lean_ctor_get(v_a_489_, 9);
lean_inc_ref(v_elimEqs_511_);
lean_dec(v_a_489_);
v_size_512_ = lean_ctor_get(v_elimEqs_511_, 2);
v___x_513_ = lean_nat_dec_lt(v_a_456_, v_size_512_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; 
lean_dec_ref(v_elimEqs_511_);
v___x_514_ = l_outOfBounds___redArg(v___x_454_);
v___y_491_ = v___x_514_;
goto v___jp_490_;
}
else
{
lean_object* v___x_515_; 
v___x_515_ = l_Lean_PersistentArray_get_x21___redArg(v___x_454_, v_elimEqs_511_, v_a_456_);
lean_dec_ref(v_elimEqs_511_);
v___y_491_ = v___x_515_;
goto v___jp_490_;
}
v___jp_490_:
{
if (lean_obj_tag(v___y_491_) == 0)
{
v___y_472_ = v_a_443_;
v___y_473_ = v_a_451_;
goto v___jp_471_;
}
else
{
lean_object* v___x_492_; 
lean_dec_ref_known(v___y_491_, 1);
lean_inc(v_a_452_);
lean_inc_ref(v_a_451_);
lean_inc(v_a_450_);
lean_inc_ref(v_a_449_);
lean_inc(v_a_448_);
lean_inc_ref(v_a_447_);
lean_inc(v_a_446_);
lean_inc_ref(v_a_445_);
lean_inc(v_a_444_);
lean_inc(v_a_443_);
lean_inc(v_x_442_);
lean_inc(v_a_456_);
v___x_492_ = lean_cutsat_propagate_nonlinear(v_a_456_, v_x_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_502_; 
v_a_493_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_502_ == 0)
{
v___x_495_ = v___x_492_;
v_isShared_496_ = v_isSharedCheck_502_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_492_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_502_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
uint8_t v___x_497_; 
v___x_497_ = lean_unbox(v_a_493_);
lean_dec(v_a_493_);
if (v___x_497_ == 0)
{
lean_del_object(v___x_495_);
v___y_472_ = v_a_443_;
v___y_473_ = v_a_451_;
goto v___jp_471_;
}
else
{
lean_object* v___x_498_; lean_object* v___x_500_; 
lean_del_object(v___x_458_);
lean_dec(v_a_456_);
lean_dec(v_x_442_);
v___x_498_ = lean_box(0);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v___x_498_);
v___x_500_ = v___x_495_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_498_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
else
{
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_510_; 
lean_del_object(v___x_458_);
lean_dec(v_a_456_);
lean_dec(v_x_442_);
v_a_503_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_510_ == 0)
{
v___x_505_ = v___x_492_;
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_492_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_508_; 
if (v_isShared_506_ == 0)
{
v___x_508_ = v___x_505_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_a_503_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
}
}
else
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_523_; 
lean_del_object(v___x_458_);
lean_dec(v_a_456_);
lean_dec(v_x_442_);
v_a_516_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_523_ == 0)
{
v___x_518_ = v___x_488_;
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_488_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_521_; 
if (v_isShared_519_ == 0)
{
v___x_521_ = v___x_518_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_a_516_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
v___jp_460_:
{
uint8_t v___x_463_; 
v___x_463_ = l_List_elem___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1(v_x_442_, v___y_462_);
if (v___x_463_ == 0)
{
lean_object* v___f_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
lean_del_object(v___x_458_);
v___f_464_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___lam__0), 4, 3);
lean_closure_set(v___f_464_, 0, v_x_442_);
lean_closure_set(v___f_464_, 1, v___y_462_);
lean_closure_set(v___f_464_, 2, v_a_456_);
v___x_465_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_466_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_465_, v___f_464_, v___y_461_);
return v___x_466_;
}
else
{
lean_object* v___x_467_; lean_object* v___x_469_; 
lean_dec(v___y_462_);
lean_dec(v_a_456_);
lean_dec(v_x_442_);
v___x_467_ = lean_box(0);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 0, v___x_467_);
v___x_469_ = v___x_458_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_467_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
v___jp_471_:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v___y_472_, v___y_473_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v_a_475_; lean_object* v_nonlinearOccs_476_; lean_object* v___x_477_; 
v_a_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_a_475_);
lean_dec_ref_known(v___x_474_, 1);
v_nonlinearOccs_476_ = lean_ctor_get(v_a_475_, 18);
lean_inc_ref(v_nonlinearOccs_476_);
lean_dec(v_a_475_);
v___x_477_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2___redArg(v_nonlinearOccs_476_, v_a_456_);
lean_dec_ref(v_nonlinearOccs_476_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v___x_478_; 
v___x_478_ = lean_box(0);
v___y_461_ = v___y_472_;
v___y_462_ = v___x_478_;
goto v___jp_460_;
}
else
{
lean_object* v_val_479_; 
v_val_479_ = lean_ctor_get(v___x_477_, 0);
lean_inc(v_val_479_);
lean_dec_ref_known(v___x_477_, 1);
v___y_461_ = v___y_472_;
v___y_462_ = v_val_479_;
goto v___jp_460_;
}
}
else
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
lean_del_object(v___x_458_);
lean_dec(v_a_456_);
lean_dec(v_x_442_);
v_a_480_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v___x_474_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_474_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_483_ == 0)
{
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_a_480_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
}
}
else
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_532_; 
lean_dec(v_x_442_);
v_a_525_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_532_ == 0)
{
v___x_527_ = v___x_455_;
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_455_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_530_; 
if (v_isShared_528_ == 0)
{
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_525_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_0interp(lean_interpreter_value* stack)
{
lean_object* v_arg_441_ = stack[0].m_obj;
lean_object* v_x_442_ = stack[1].m_obj;
lean_object* v_a_443_ = stack[2].m_obj;
lean_object* v_a_444_ = stack[3].m_obj;
lean_object* v_a_445_ = stack[4].m_obj;
lean_object* v_a_446_ = stack[5].m_obj;
lean_object* v_a_447_ = stack[6].m_obj;
lean_object* v_a_448_ = stack[7].m_obj;
lean_object* v_a_449_ = stack[8].m_obj;
lean_object* v_a_450_ = stack[9].m_obj;
lean_object* v_a_451_ = stack[10].m_obj;
lean_object* v_a_452_ = stack[11].m_obj;
lean_object* v_res_533_;
v_res_533_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_arg_441_, v_x_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_);
stack->m_obj
 = v_res_533_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___boxed(lean_object* v_arg_534_, lean_object* v_x_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_arg_534_, v_x_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_);
lean_dec(v_a_545_);
lean_dec_ref(v_a_544_);
lean_dec(v_a_543_);
lean_dec_ref(v_a_542_);
lean_dec(v_a_541_);
lean_dec_ref(v_a_540_);
lean_dec(v_a_539_);
lean_dec_ref(v_a_538_);
lean_dec(v_a_537_);
lean_dec(v_a_536_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0(lean_object* v_00_u03b2_548_, lean_object* v_x_549_, lean_object* v_x_550_, lean_object* v_x_551_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0___redArg(v_x_549_, v_x_550_, v_x_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2(lean_object* v_00_u03b2_553_, lean_object* v_x_554_, lean_object* v_x_555_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2___redArg(v_x_554_, v_x_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2___boxed(lean_object* v_00_u03b2_557_, lean_object* v_x_558_, lean_object* v_x_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2(v_00_u03b2_557_, v_x_558_, v_x_559_);
lean_dec(v_x_559_);
lean_dec_ref(v_x_558_);
return v_res_560_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0(lean_object* v_00_u03b2_561_, lean_object* v_x_562_, size_t v_x_563_, size_t v_x_564_, lean_object* v_x_565_, lean_object* v_x_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_x_562_, v_x_563_, v_x_564_, v_x_565_, v_x_566_);
return v___x_567_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_562_ = stack[1].m_obj;
size_t v_x_563_ = stack[2].m_num;
size_t v_x_564_ = stack[3].m_num;
lean_object* v_x_565_ = stack[4].m_obj;
lean_object* v_x_566_ = stack[5].m_obj;
lean_object* v_res_568_;
v_res_568_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0(lean_box(0), v_x_562_, v_x_563_, v_x_564_, v_x_565_, v_x_566_);
stack->m_obj
 = v_res_568_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___boxed(lean_object* v_00_u03b2_569_, lean_object* v_x_570_, lean_object* v_x_571_, lean_object* v_x_572_, lean_object* v_x_573_, lean_object* v_x_574_){
_start:
{
size_t v_x_8659__boxed_575_; size_t v_x_8660__boxed_576_; lean_object* v_res_577_; 
v_x_8659__boxed_575_ = lean_unbox_usize(v_x_571_);
lean_dec(v_x_571_);
v_x_8660__boxed_576_ = lean_unbox_usize(v_x_572_);
lean_dec(v_x_572_);
v_res_577_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0(v_00_u03b2_569_, v_x_570_, v_x_8659__boxed_575_, v_x_8660__boxed_576_, v_x_573_, v_x_574_);
return v_res_577_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3(lean_object* v_00_u03b2_578_, lean_object* v_x_579_, size_t v_x_580_, lean_object* v_x_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___redArg(v_x_579_, v_x_580_, v_x_581_);
return v___x_582_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_579_ = stack[1].m_obj;
size_t v_x_580_ = stack[2].m_num;
lean_object* v_x_581_ = stack[3].m_obj;
lean_object* v_res_583_;
v_res_583_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3(lean_box(0), v_x_579_, v_x_580_, v_x_581_);
stack->m_obj
 = v_res_583_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___boxed(lean_object* v_00_u03b2_584_, lean_object* v_x_585_, lean_object* v_x_586_, lean_object* v_x_587_){
_start:
{
size_t v_x_8687__boxed_588_; lean_object* v_res_589_; 
v_x_8687__boxed_588_ = lean_unbox_usize(v_x_586_);
lean_dec(v_x_586_);
v_res_589_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3(v_00_u03b2_584_, v_x_585_, v_x_8687__boxed_588_, v_x_587_);
lean_dec(v_x_587_);
lean_dec_ref(v_x_585_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_590_, lean_object* v_n_591_, lean_object* v_k_592_, lean_object* v_v_593_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1___redArg(v_n_591_, v_k_592_, v_v_593_);
return v___x_594_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_595_, size_t v_depth_596_, lean_object* v_keys_597_, lean_object* v_vals_598_, lean_object* v_heq_599_, lean_object* v_i_600_, lean_object* v_entries_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg(v_depth_596_, v_keys_597_, v_vals_598_, v_i_600_, v_entries_601_);
return v___x_602_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_depth_596_ = stack[1].m_num;
lean_object* v_keys_597_ = stack[2].m_obj;
lean_object* v_vals_598_ = stack[3].m_obj;
lean_object* v_i_600_ = stack[5].m_obj;
lean_object* v_entries_601_ = stack[6].m_obj;
lean_object* v_res_603_;
v_res_603_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2(lean_box(0), v_depth_596_, v_keys_597_, v_vals_598_, lean_box(0), v_i_600_, v_entries_601_);
stack->m_obj
 = v_res_603_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_604_, lean_object* v_depth_605_, lean_object* v_keys_606_, lean_object* v_vals_607_, lean_object* v_heq_608_, lean_object* v_i_609_, lean_object* v_entries_610_){
_start:
{
size_t v_depth_boxed_611_; lean_object* v_res_612_; 
v_depth_boxed_611_ = lean_unbox_usize(v_depth_605_);
lean_dec(v_depth_605_);
v_res_612_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2(v_00_u03b2_604_, v_depth_boxed_611_, v_keys_606_, v_vals_607_, v_heq_608_, v_i_609_, v_entries_610_);
lean_dec_ref(v_vals_607_);
lean_dec_ref(v_keys_606_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_613_, lean_object* v_keys_614_, lean_object* v_vals_615_, lean_object* v_heq_616_, lean_object* v_i_617_, lean_object* v_k_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6___redArg(v_keys_614_, v_vals_615_, v_i_617_, v_k_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_620_, lean_object* v_keys_621_, lean_object* v_vals_622_, lean_object* v_heq_623_, lean_object* v_i_624_, lean_object* v_k_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6(v_00_u03b2_620_, v_keys_621_, v_vals_622_, v_heq_623_, v_i_624_, v_k_625_);
lean_dec(v_k_625_);
lean_dec_ref(v_vals_622_);
lean_dec_ref(v_keys_621_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_627_, lean_object* v_x_628_, lean_object* v_x_629_, lean_object* v_x_630_, lean_object* v_x_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__4___redArg(v_x_628_, v_x_629_, v_x_630_, v_x_631_);
return v___x_632_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(lean_object* v_x_633_, lean_object* v_e_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_){
_start:
{
lean_object* v___x_646_; 
lean_inc_ref(v_e_634_);
v___x_646_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_634_, v_a_642_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_a_647_);
lean_dec_ref_known(v___x_646_, 1);
v___x_648_ = l_Lean_Expr_cleanupAnnotations(v_a_647_);
v___x_649_ = l_Lean_Expr_isApp(v___x_648_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; 
lean_dec_ref(v___x_648_);
v___x_650_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_634_, v_x_633_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_);
return v___x_650_;
}
else
{
lean_object* v_arg_651_; lean_object* v___x_652_; uint8_t v___x_653_; 
v_arg_651_ = lean_ctor_get(v___x_648_, 1);
lean_inc_ref(v_arg_651_);
v___x_652_ = l_Lean_Expr_appFnCleanup___redArg(v___x_648_);
v___x_653_ = l_Lean_Expr_isApp(v___x_652_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; 
lean_dec_ref(v___x_652_);
lean_dec_ref(v_arg_651_);
v___x_654_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_634_, v_x_633_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_);
return v___x_654_;
}
else
{
lean_object* v_arg_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v_arg_655_ = lean_ctor_get(v___x_652_, 1);
lean_inc_ref(v_arg_655_);
v___x_656_ = l_Lean_Expr_appFnCleanup___redArg(v___x_652_);
v___x_657_ = l_Lean_Expr_isApp(v___x_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; 
lean_dec_ref(v___x_656_);
lean_dec_ref(v_arg_655_);
lean_dec_ref(v_arg_651_);
v___x_658_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_634_, v_x_633_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_);
return v___x_658_;
}
else
{
lean_object* v_arg_659_; lean_object* v___x_660_; uint8_t v___x_661_; 
v_arg_659_ = lean_ctor_get(v___x_656_, 1);
lean_inc_ref(v_arg_659_);
v___x_660_ = l_Lean_Expr_appFnCleanup___redArg(v___x_656_);
v___x_661_ = l_Lean_Expr_isApp(v___x_660_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; 
lean_dec_ref(v___x_660_);
lean_dec_ref(v_arg_659_);
lean_dec_ref(v_arg_655_);
lean_dec_ref(v_arg_651_);
v___x_662_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_634_, v_x_633_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_);
return v___x_662_;
}
else
{
lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_663_ = l_Lean_Expr_appFnCleanup___redArg(v___x_660_);
v___x_664_ = l_Lean_Expr_isApp(v___x_663_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; 
lean_dec_ref(v___x_663_);
lean_dec_ref(v_arg_659_);
lean_dec_ref(v_arg_655_);
lean_dec_ref(v_arg_651_);
v___x_665_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_634_, v_x_633_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_);
return v___x_665_;
}
else
{
lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_666_ = l_Lean_Expr_appFnCleanup___redArg(v___x_663_);
v___x_667_ = l_Lean_Expr_isApp(v___x_666_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; 
lean_dec_ref(v___x_666_);
lean_dec_ref(v_arg_659_);
lean_dec_ref(v_arg_655_);
lean_dec_ref(v_arg_651_);
v___x_668_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_634_, v_x_633_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_);
return v___x_668_;
}
else
{
lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v___x_671_; 
v___x_669_ = l_Lean_Expr_appFnCleanup___redArg(v___x_666_);
v___x_670_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11));
v___x_671_ = l_Lean_Expr_isConstOf(v___x_669_, v___x_670_);
lean_dec_ref(v___x_669_);
if (v___x_671_ == 0)
{
lean_object* v___x_672_; 
lean_dec_ref(v_arg_659_);
lean_dec_ref(v_arg_655_);
lean_dec_ref(v_arg_651_);
v___x_672_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_634_, v_x_633_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_);
return v___x_672_;
}
else
{
lean_object* v___x_673_; 
v___x_673_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_659_, v_a_642_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; uint8_t v___x_675_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_a_674_);
lean_dec_ref_known(v___x_673_, 1);
v___x_675_ = lean_unbox(v_a_674_);
lean_dec(v_a_674_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; 
lean_dec_ref(v_arg_655_);
lean_dec_ref(v_arg_651_);
v___x_676_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_634_, v_x_633_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_);
return v___x_676_;
}
else
{
lean_object* v___x_677_; 
lean_dec_ref(v_e_634_);
lean_inc(v_x_633_);
v___x_677_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(v_x_633_, v_arg_655_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_dec_ref_known(v___x_677_, 1);
v_e_634_ = v_arg_651_;
goto _start;
}
else
{
lean_dec_ref(v_arg_651_);
lean_dec(v_x_633_);
return v___x_677_;
}
}
}
else
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
lean_dec_ref(v_arg_655_);
lean_dec_ref(v_arg_651_);
lean_dec_ref(v_e_634_);
lean_dec(v_x_633_);
v_a_679_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_673_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_673_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_679_);
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
}
}
}
}
}
}
}
else
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_694_; 
lean_dec_ref(v_e_634_);
lean_dec(v_x_633_);
v_a_687_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_694_ == 0)
{
v___x_689_ = v___x_646_;
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_646_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_692_; 
if (v_isShared_690_ == 0)
{
v___x_692_ = v___x_689_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_a_687_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_633_ = stack[0].m_obj;
lean_object* v_e_634_ = stack[1].m_obj;
lean_object* v_a_635_ = stack[2].m_obj;
lean_object* v_a_636_ = stack[3].m_obj;
lean_object* v_a_637_ = stack[4].m_obj;
lean_object* v_a_638_ = stack[5].m_obj;
lean_object* v_a_639_ = stack[6].m_obj;
lean_object* v_a_640_ = stack[7].m_obj;
lean_object* v_a_641_ = stack[8].m_obj;
lean_object* v_a_642_ = stack[9].m_obj;
lean_object* v_a_643_ = stack[10].m_obj;
lean_object* v_a_644_ = stack[11].m_obj;
lean_object* v_res_695_;
v_res_695_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(v_x_633_, v_e_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_);
stack->m_obj
 = v_res_695_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go___boxed(lean_object* v_x_696_, lean_object* v_e_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(v_x_696_, v_e_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_);
lean_dec(v_a_707_);
lean_dec_ref(v_a_706_);
lean_dec(v_a_705_);
lean_dec_ref(v_a_704_);
lean_dec(v_a_703_);
lean_dec_ref(v_a_702_);
lean_dec(v_a_701_);
lean_dec_ref(v_a_700_);
lean_dec(v_a_699_);
lean_dec(v_a_698_);
return v_res_709_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt(lean_object* v_e_710_, lean_object* v_x_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_710_, v_a_719_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; lean_object* v___x_731_; uint8_t v___x_732_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_a_730_);
lean_dec_ref_known(v___x_729_, 1);
v___x_731_ = l_Lean_Expr_cleanupAnnotations(v_a_730_);
v___x_732_ = l_Lean_Expr_isApp(v___x_731_);
if (v___x_732_ == 0)
{
lean_dec_ref(v___x_731_);
lean_dec(v_x_711_);
goto v___jp_723_;
}
else
{
lean_object* v_arg_733_; lean_object* v___x_734_; uint8_t v___x_735_; 
v_arg_733_ = lean_ctor_get(v___x_731_, 1);
lean_inc_ref(v_arg_733_);
v___x_734_ = l_Lean_Expr_appFnCleanup___redArg(v___x_731_);
v___x_735_ = l_Lean_Expr_isApp(v___x_734_);
if (v___x_735_ == 0)
{
lean_dec_ref(v___x_734_);
lean_dec_ref(v_arg_733_);
lean_dec(v_x_711_);
goto v___jp_723_;
}
else
{
lean_object* v_arg_736_; lean_object* v___x_737_; uint8_t v___x_738_; 
v_arg_736_ = lean_ctor_get(v___x_734_, 1);
lean_inc_ref(v_arg_736_);
v___x_737_ = l_Lean_Expr_appFnCleanup___redArg(v___x_734_);
v___x_738_ = l_Lean_Expr_isApp(v___x_737_);
if (v___x_738_ == 0)
{
lean_dec_ref(v___x_737_);
lean_dec_ref(v_arg_736_);
lean_dec_ref(v_arg_733_);
lean_dec(v_x_711_);
goto v___jp_723_;
}
else
{
lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_739_ = l_Lean_Expr_appFnCleanup___redArg(v___x_737_);
v___x_740_ = l_Lean_Expr_isApp(v___x_739_);
if (v___x_740_ == 0)
{
lean_dec_ref(v___x_739_);
lean_dec_ref(v_arg_736_);
lean_dec_ref(v_arg_733_);
lean_dec(v_x_711_);
goto v___jp_723_;
}
else
{
lean_object* v___x_741_; uint8_t v___x_742_; 
v___x_741_ = l_Lean_Expr_appFnCleanup___redArg(v___x_739_);
v___x_742_ = l_Lean_Expr_isApp(v___x_741_);
if (v___x_742_ == 0)
{
lean_dec_ref(v___x_741_);
lean_dec_ref(v_arg_736_);
lean_dec_ref(v_arg_733_);
lean_dec(v_x_711_);
goto v___jp_723_;
}
else
{
lean_object* v___x_743_; uint8_t v___x_744_; 
v___x_743_ = l_Lean_Expr_appFnCleanup___redArg(v___x_741_);
v___x_744_ = l_Lean_Expr_isApp(v___x_743_);
if (v___x_744_ == 0)
{
lean_dec_ref(v___x_743_);
lean_dec_ref(v_arg_736_);
lean_dec_ref(v_arg_733_);
lean_dec(v_x_711_);
goto v___jp_723_;
}
else
{
lean_object* v___x_745_; lean_object* v___x_746_; uint8_t v___x_747_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_758_; 
v___x_745_ = l_Lean_Expr_appFnCleanup___redArg(v___x_743_);
v___x_746_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__2));
v___x_747_ = l_Lean_Expr_isConstOf(v___x_745_, v___x_746_);
if (v___x_747_ == 0)
{
lean_object* v___x_803_; uint8_t v___x_804_; 
v___x_803_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__5));
v___x_804_ = l_Lean_Expr_isConstOf(v___x_745_, v___x_803_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; uint8_t v___x_806_; 
v___x_805_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__8));
v___x_806_ = l_Lean_Expr_isConstOf(v___x_745_, v___x_805_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; uint8_t v___x_808_; 
v___x_807_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11));
v___x_808_ = l_Lean_Expr_isConstOf(v___x_745_, v___x_807_);
lean_dec_ref(v___x_745_);
if (v___x_808_ == 0)
{
lean_dec_ref(v_arg_736_);
lean_dec_ref(v_arg_733_);
lean_dec(v_x_711_);
goto v___jp_723_;
}
else
{
lean_object* v___x_809_; 
lean_inc(v_x_711_);
v___x_809_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(v_x_711_, v_arg_736_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v___x_810_; 
lean_dec_ref_known(v___x_809_, 1);
v___x_810_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(v_x_711_, v_arg_733_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
return v___x_810_;
}
else
{
lean_dec_ref(v_arg_733_);
lean_dec(v_x_711_);
return v___x_809_;
}
}
}
else
{
lean_object* v___x_811_; 
lean_dec_ref(v___x_745_);
lean_dec_ref(v_arg_736_);
v___x_811_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_arg_733_, v_x_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
return v___x_811_;
}
}
else
{
lean_object* v___x_812_; 
lean_dec_ref(v___x_745_);
lean_dec_ref(v_arg_736_);
v___x_812_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_arg_733_, v_x_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
return v___x_812_;
}
}
else
{
lean_object* v___x_813_; 
lean_dec_ref(v___x_745_);
lean_inc_ref(v_arg_736_);
v___x_813_ = l_Lean_Meta_getIntValue_x3f(v_arg_736_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v_a_814_; 
v_a_814_ = lean_ctor_get(v___x_813_, 0);
lean_inc(v_a_814_);
lean_dec_ref_known(v___x_813_, 1);
if (lean_obj_tag(v_a_814_) == 0)
{
if (v___x_747_ == 0)
{
lean_dec_ref(v_arg_736_);
v___y_749_ = v_a_712_;
v___y_750_ = v_a_713_;
v___y_751_ = v_a_714_;
v___y_752_ = v_a_715_;
v___y_753_ = v_a_716_;
v___y_754_ = v_a_717_;
v___y_755_ = v_a_718_;
v___y_756_ = v_a_719_;
v___y_757_ = v_a_720_;
v___y_758_ = v_a_721_;
goto v___jp_748_;
}
else
{
lean_object* v___x_815_; 
lean_inc(v_x_711_);
v___x_815_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_arg_736_, v_x_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_dec_ref_known(v___x_815_, 1);
v___y_749_ = v_a_712_;
v___y_750_ = v_a_713_;
v___y_751_ = v_a_714_;
v___y_752_ = v_a_715_;
v___y_753_ = v_a_716_;
v___y_754_ = v_a_717_;
v___y_755_ = v_a_718_;
v___y_756_ = v_a_719_;
v___y_757_ = v_a_720_;
v___y_758_ = v_a_721_;
goto v___jp_748_;
}
else
{
lean_dec_ref(v_arg_733_);
lean_dec(v_x_711_);
return v___x_815_;
}
}
}
else
{
lean_dec_ref_known(v_a_814_, 1);
lean_dec_ref(v_arg_736_);
v___y_749_ = v_a_712_;
v___y_750_ = v_a_713_;
v___y_751_ = v_a_714_;
v___y_752_ = v_a_715_;
v___y_753_ = v_a_716_;
v___y_754_ = v_a_717_;
v___y_755_ = v_a_718_;
v___y_756_ = v_a_719_;
v___y_757_ = v_a_720_;
v___y_758_ = v_a_721_;
goto v___jp_748_;
}
}
else
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_823_; 
lean_dec_ref(v_arg_736_);
lean_dec_ref(v_arg_733_);
lean_dec(v_x_711_);
v_a_816_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_823_ == 0)
{
v___x_818_ = v___x_813_;
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_813_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_819_ == 0)
{
v___x_821_ = v___x_818_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_a_816_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
v___jp_748_:
{
lean_object* v___x_759_; 
lean_inc_ref(v_arg_733_);
v___x_759_ = l_Lean_Meta_getIntValue_x3f(v_arg_733_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; lean_object* v___x_761_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_a_760_);
lean_dec_ref_known(v___x_759_, 1);
v___x_761_ = l_Lean_Meta_getNatValue_x3f(v_arg_733_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
if (lean_obj_tag(v___x_761_) == 0)
{
if (lean_obj_tag(v_a_760_) == 0)
{
if (v___x_747_ == 0)
{
lean_dec_ref_known(v___x_761_, 1);
lean_dec_ref(v_arg_733_);
lean_dec(v_x_711_);
goto v___jp_726_;
}
else
{
lean_object* v_a_762_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_a_762_);
lean_dec_ref_known(v___x_761_, 1);
if (lean_obj_tag(v_a_762_) == 0)
{
lean_object* v___x_763_; 
lean_inc_ref(v_arg_733_);
v___x_763_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_arg_733_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; lean_object* v_fst_765_; lean_object* v___x_766_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v___x_763_, 1);
v_fst_765_ = lean_ctor_get(v_a_764_, 0);
lean_inc(v_fst_765_);
lean_dec(v_a_764_);
v___x_766_ = l_Lean_Meta_Grind_getGeneration___redArg(v_arg_733_, v___y_749_);
lean_dec_ref(v_arg_733_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_a_767_);
lean_dec_ref_known(v___x_766_, 1);
v___x_768_ = lean_box(0);
lean_inc(v___y_758_);
lean_inc_ref(v___y_757_);
lean_inc(v___y_756_);
lean_inc_ref(v___y_755_);
lean_inc(v___y_754_);
lean_inc_ref(v___y_753_);
lean_inc(v___y_752_);
lean_inc_ref(v___y_751_);
lean_inc(v___y_750_);
lean_inc(v___y_749_);
lean_inc(v_fst_765_);
v___x_769_ = lean_grind_internalize(v_fst_765_, v_a_767_, v___x_768_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v___x_770_; 
lean_dec_ref_known(v___x_769_, 1);
v___x_770_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_fst_765_, v_x_711_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
return v___x_770_;
}
else
{
lean_dec(v_fst_765_);
lean_dec(v_x_711_);
return v___x_769_;
}
}
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_dec(v_fst_765_);
lean_dec(v_x_711_);
v_a_771_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_766_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_766_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
else
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_786_; 
lean_dec_ref(v_arg_733_);
lean_dec(v_x_711_);
v_a_779_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_786_ == 0)
{
v___x_781_ = v___x_763_;
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_763_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_784_; 
if (v_isShared_782_ == 0)
{
v___x_784_ = v___x_781_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_a_779_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_762_, 1);
lean_dec_ref(v_arg_733_);
lean_dec(v_x_711_);
goto v___jp_726_;
}
}
}
else
{
lean_dec_ref_known(v_a_760_, 1);
lean_dec_ref_known(v___x_761_, 1);
lean_dec_ref(v_arg_733_);
lean_dec(v_x_711_);
goto v___jp_726_;
}
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
lean_dec(v_a_760_);
lean_dec_ref(v_arg_733_);
lean_dec(v_x_711_);
v_a_787_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_761_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_761_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
else
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
lean_dec_ref(v_arg_733_);
lean_dec(v_x_711_);
v_a_795_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_759_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_759_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_795_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_831_; 
lean_dec(v_x_711_);
v_a_824_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_831_ == 0)
{
v___x_826_ = v___x_729_;
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_729_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_824_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
v___jp_723_:
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = lean_box(0);
v___x_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
return v___x_725_;
}
v___jp_726_:
{
lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_727_ = lean_box(0);
v___x_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
return v___x_728_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_710_ = stack[0].m_obj;
lean_object* v_x_711_ = stack[1].m_obj;
lean_object* v_a_712_ = stack[2].m_obj;
lean_object* v_a_713_ = stack[3].m_obj;
lean_object* v_a_714_ = stack[4].m_obj;
lean_object* v_a_715_ = stack[5].m_obj;
lean_object* v_a_716_ = stack[6].m_obj;
lean_object* v_a_717_ = stack[7].m_obj;
lean_object* v_a_718_ = stack[8].m_obj;
lean_object* v_a_719_ = stack[9].m_obj;
lean_object* v_a_720_ = stack[10].m_obj;
lean_object* v_a_721_ = stack[11].m_obj;
lean_object* v_res_832_;
v_res_832_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt(v_e_710_, v_x_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
stack->m_obj
 = v_res_832_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt___boxed(lean_object* v_e_833_, lean_object* v_x_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt(v_e_833_, v_x_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
lean_dec(v_a_844_);
lean_dec_ref(v_a_843_);
lean_dec(v_a_842_);
lean_dec_ref(v_a_841_);
lean_dec(v_a_840_);
lean_dec_ref(v_a_839_);
lean_dec(v_a_838_);
lean_dec_ref(v_a_837_);
lean_dec(v_a_836_);
lean_dec(v_a_835_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_x_847_, lean_object* v_x_848_, lean_object* v_x_849_, lean_object* v_x_850_){
_start:
{
lean_object* v_ks_851_; lean_object* v_vs_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_878_; 
v_ks_851_ = lean_ctor_get(v_x_847_, 0);
v_vs_852_ = lean_ctor_get(v_x_847_, 1);
v_isSharedCheck_878_ = !lean_is_exclusive(v_x_847_);
if (v_isSharedCheck_878_ == 0)
{
v___x_854_ = v_x_847_;
v_isShared_855_ = v_isSharedCheck_878_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_vs_852_);
lean_inc(v_ks_851_);
lean_dec(v_x_847_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_878_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_856_; uint8_t v___x_857_; 
v___x_856_ = lean_array_get_size(v_ks_851_);
v___x_857_ = lean_nat_dec_lt(v_x_848_, v___x_856_);
if (v___x_857_ == 0)
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_861_; 
lean_dec(v_x_848_);
v___x_858_ = lean_array_push(v_ks_851_, v_x_849_);
v___x_859_ = lean_array_push(v_vs_852_, v_x_850_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 1, v___x_859_);
lean_ctor_set(v___x_854_, 0, v___x_858_);
v___x_861_ = v___x_854_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_858_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v___x_859_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
else
{
lean_object* v_k_x27_863_; size_t v___x_864_; size_t v___x_865_; uint8_t v___x_866_; 
v_k_x27_863_ = lean_array_fget_borrowed(v_ks_851_, v_x_848_);
v___x_864_ = lean_ptr_addr(v_x_849_);
v___x_865_ = lean_ptr_addr(v_k_x27_863_);
v___x_866_ = lean_usize_dec_eq(v___x_864_, v___x_865_);
if (v___x_866_ == 0)
{
lean_object* v___x_868_; 
if (v_isShared_855_ == 0)
{
v___x_868_ = v___x_854_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_ks_851_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v_vs_852_);
v___x_868_ = v_reuseFailAlloc_872_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_869_ = lean_unsigned_to_nat(1u);
v___x_870_ = lean_nat_add(v_x_848_, v___x_869_);
lean_dec(v_x_848_);
v_x_847_ = v___x_868_;
v_x_848_ = v___x_870_;
goto _start;
}
}
else
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_876_; 
v___x_873_ = lean_array_fset(v_ks_851_, v_x_848_, v_x_849_);
v___x_874_ = lean_array_fset(v_vs_852_, v_x_848_, v_x_850_);
lean_dec(v_x_848_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 1, v___x_874_);
lean_ctor_set(v___x_854_, 0, v___x_873_);
v___x_876_ = v___x_854_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_873_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v___x_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4___redArg(lean_object* v_n_879_, lean_object* v_k_880_, lean_object* v_v_881_){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = lean_unsigned_to_nat(0u);
v___x_883_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7___redArg(v_n_879_, v___x_882_, v_k_880_, v_v_881_);
return v___x_883_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(lean_object* v_x_884_, size_t v_x_885_, size_t v_x_886_, lean_object* v_x_887_, lean_object* v_x_888_){
_start:
{
if (lean_obj_tag(v_x_884_) == 0)
{
lean_object* v_es_889_; size_t v___x_890_; size_t v___x_891_; lean_object* v_j_892_; lean_object* v___x_893_; uint8_t v___x_894_; 
v_es_889_ = lean_ctor_get(v_x_884_, 0);
v___x_890_ = ((size_t)31ULL);
v___x_891_ = lean_usize_land(v_x_885_, v___x_890_);
v_j_892_ = lean_usize_to_nat(v___x_891_);
v___x_893_ = lean_array_get_size(v_es_889_);
v___x_894_ = lean_nat_dec_lt(v_j_892_, v___x_893_);
if (v___x_894_ == 0)
{
lean_dec(v_j_892_);
lean_dec(v_x_888_);
lean_dec_ref(v_x_887_);
return v_x_884_;
}
else
{
lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_935_; 
lean_inc_ref(v_es_889_);
v_isSharedCheck_935_ = !lean_is_exclusive(v_x_884_);
if (v_isSharedCheck_935_ == 0)
{
lean_object* v_unused_936_; 
v_unused_936_ = lean_ctor_get(v_x_884_, 0);
lean_dec(v_unused_936_);
v___x_896_ = v_x_884_;
v_isShared_897_ = v_isSharedCheck_935_;
goto v_resetjp_895_;
}
else
{
lean_dec(v_x_884_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_935_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v_v_898_; lean_object* v___x_899_; lean_object* v_xs_x27_900_; lean_object* v___y_902_; 
v_v_898_ = lean_array_fget(v_es_889_, v_j_892_);
v___x_899_ = lean_box(0);
v_xs_x27_900_ = lean_array_fset(v_es_889_, v_j_892_, v___x_899_);
switch(lean_obj_tag(v_v_898_))
{
case 0:
{
lean_object* v_key_907_; lean_object* v_val_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_920_; 
v_key_907_ = lean_ctor_get(v_v_898_, 0);
v_val_908_ = lean_ctor_get(v_v_898_, 1);
v_isSharedCheck_920_ = !lean_is_exclusive(v_v_898_);
if (v_isSharedCheck_920_ == 0)
{
v___x_910_ = v_v_898_;
v_isShared_911_ = v_isSharedCheck_920_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_val_908_);
lean_inc(v_key_907_);
lean_dec(v_v_898_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_920_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
size_t v___x_912_; size_t v___x_913_; uint8_t v___x_914_; 
v___x_912_ = lean_ptr_addr(v_x_887_);
v___x_913_ = lean_ptr_addr(v_key_907_);
v___x_914_ = lean_usize_dec_eq(v___x_912_, v___x_913_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; lean_object* v___x_916_; 
lean_del_object(v___x_910_);
v___x_915_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_907_, v_val_908_, v_x_887_, v_x_888_);
v___x_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
v___y_902_ = v___x_916_;
goto v___jp_901_;
}
else
{
lean_object* v___x_918_; 
lean_dec(v_val_908_);
lean_dec(v_key_907_);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 1, v_x_888_);
lean_ctor_set(v___x_910_, 0, v_x_887_);
v___x_918_ = v___x_910_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_x_887_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v_x_888_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
v___y_902_ = v___x_918_;
goto v___jp_901_;
}
}
}
}
case 1:
{
lean_object* v_node_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_933_; 
v_node_921_ = lean_ctor_get(v_v_898_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v_v_898_);
if (v_isSharedCheck_933_ == 0)
{
v___x_923_ = v_v_898_;
v_isShared_924_ = v_isSharedCheck_933_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_node_921_);
lean_dec(v_v_898_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_933_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
size_t v___x_925_; size_t v___x_926_; size_t v___x_927_; size_t v___x_928_; lean_object* v___x_929_; lean_object* v___x_931_; 
v___x_925_ = ((size_t)5ULL);
v___x_926_ = lean_usize_shift_right(v_x_885_, v___x_925_);
v___x_927_ = ((size_t)1ULL);
v___x_928_ = lean_usize_add(v_x_886_, v___x_927_);
v___x_929_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_node_921_, v___x_926_, v___x_928_, v_x_887_, v_x_888_);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 0, v___x_929_);
v___x_931_ = v___x_923_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_929_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
v___y_902_ = v___x_931_;
goto v___jp_901_;
}
}
}
default: 
{
lean_object* v___x_934_; 
v___x_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_934_, 0, v_x_887_);
lean_ctor_set(v___x_934_, 1, v_x_888_);
v___y_902_ = v___x_934_;
goto v___jp_901_;
}
}
v___jp_901_:
{
lean_object* v___x_903_; lean_object* v___x_905_; 
v___x_903_ = lean_array_fset(v_xs_x27_900_, v_j_892_, v___y_902_);
lean_dec(v_j_892_);
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v___x_903_);
v___x_905_ = v___x_896_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_903_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
}
else
{
lean_object* v_ks_937_; lean_object* v_vs_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_956_; 
v_ks_937_ = lean_ctor_get(v_x_884_, 0);
v_vs_938_ = lean_ctor_get(v_x_884_, 1);
v_isSharedCheck_956_ = !lean_is_exclusive(v_x_884_);
if (v_isSharedCheck_956_ == 0)
{
v___x_940_ = v_x_884_;
v_isShared_941_ = v_isSharedCheck_956_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_vs_938_);
lean_inc(v_ks_937_);
lean_dec(v_x_884_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_956_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_943_; 
if (v_isShared_941_ == 0)
{
v___x_943_ = v___x_940_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_ks_937_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v_vs_938_);
v___x_943_ = v_reuseFailAlloc_955_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_object* v_newNode_944_; size_t v___x_945_; uint8_t v___x_946_; 
v_newNode_944_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4___redArg(v___x_943_, v_x_887_, v_x_888_);
v___x_945_ = ((size_t)7ULL);
v___x_946_ = lean_usize_dec_le(v___x_945_, v_x_886_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; lean_object* v___x_948_; uint8_t v___x_949_; 
v___x_947_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_944_);
v___x_948_ = lean_unsigned_to_nat(4u);
v___x_949_ = lean_nat_dec_lt(v___x_947_, v___x_948_);
lean_dec(v___x_947_);
if (v___x_949_ == 0)
{
lean_object* v_ks_950_; lean_object* v_vs_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v_ks_950_ = lean_ctor_get(v_newNode_944_, 0);
lean_inc_ref(v_ks_950_);
v_vs_951_ = lean_ctor_get(v_newNode_944_, 1);
lean_inc_ref(v_vs_951_);
lean_dec_ref(v_newNode_944_);
v___x_952_ = lean_unsigned_to_nat(0u);
v___x_953_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0);
v___x_954_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(v_x_886_, v_ks_950_, v_vs_951_, v___x_952_, v___x_953_);
lean_dec_ref(v_vs_951_);
lean_dec_ref(v_ks_950_);
return v___x_954_;
}
else
{
return v_newNode_944_;
}
}
else
{
return v_newNode_944_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_884_ = stack[0].m_obj;
size_t v_x_885_ = stack[1].m_num;
size_t v_x_886_ = stack[2].m_num;
lean_object* v_x_887_ = stack[3].m_obj;
lean_object* v_x_888_ = stack[4].m_obj;
lean_object* v_res_957_;
v_res_957_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_x_884_, v_x_885_, v_x_886_, v_x_887_, v_x_888_);
stack->m_obj
 = v_res_957_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(size_t v_depth_958_, lean_object* v_keys_959_, lean_object* v_vals_960_, lean_object* v_i_961_, lean_object* v_entries_962_){
_start:
{
lean_object* v___x_963_; uint8_t v___x_964_; 
v___x_963_ = lean_array_get_size(v_keys_959_);
v___x_964_ = lean_nat_dec_lt(v_i_961_, v___x_963_);
if (v___x_964_ == 0)
{
lean_dec(v_i_961_);
return v_entries_962_;
}
else
{
lean_object* v_k_965_; lean_object* v_v_966_; size_t v___x_967_; size_t v___x_968_; size_t v___x_969_; uint64_t v___x_970_; size_t v_h_971_; size_t v___x_972_; lean_object* v___x_973_; size_t v___x_974_; size_t v___x_975_; size_t v___x_976_; size_t v_h_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v_k_965_ = lean_array_fget_borrowed(v_keys_959_, v_i_961_);
v_v_966_ = lean_array_fget_borrowed(v_vals_960_, v_i_961_);
v___x_967_ = lean_ptr_addr(v_k_965_);
v___x_968_ = ((size_t)3ULL);
v___x_969_ = lean_usize_shift_right(v___x_967_, v___x_968_);
v___x_970_ = lean_usize_to_uint64(v___x_969_);
v_h_971_ = lean_uint64_to_usize(v___x_970_);
v___x_972_ = ((size_t)5ULL);
v___x_973_ = lean_unsigned_to_nat(1u);
v___x_974_ = ((size_t)1ULL);
v___x_975_ = lean_usize_sub(v_depth_958_, v___x_974_);
v___x_976_ = lean_usize_mul(v___x_972_, v___x_975_);
v_h_977_ = lean_usize_shift_right(v_h_971_, v___x_976_);
v___x_978_ = lean_nat_add(v_i_961_, v___x_973_);
lean_dec(v_i_961_);
lean_inc(v_v_966_);
lean_inc(v_k_965_);
v___x_979_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_entries_962_, v_h_977_, v_depth_958_, v_k_965_, v_v_966_);
v_i_961_ = v___x_978_;
v_entries_962_ = v___x_979_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_958_ = stack[0].m_num;
lean_object* v_keys_959_ = stack[1].m_obj;
lean_object* v_vals_960_ = stack[2].m_obj;
lean_object* v_i_961_ = stack[3].m_obj;
lean_object* v_entries_962_ = stack[4].m_obj;
lean_object* v_res_981_;
v_res_981_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(v_depth_958_, v_keys_959_, v_vals_960_, v_i_961_, v_entries_962_);
stack->m_obj
 = v_res_981_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_982_, lean_object* v_keys_983_, lean_object* v_vals_984_, lean_object* v_i_985_, lean_object* v_entries_986_){
_start:
{
size_t v_depth_boxed_987_; lean_object* v_res_988_; 
v_depth_boxed_987_ = lean_unbox_usize(v_depth_982_);
lean_dec(v_depth_982_);
v_res_988_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(v_depth_boxed_987_, v_keys_983_, v_vals_984_, v_i_985_, v_entries_986_);
lean_dec_ref(v_vals_984_);
lean_dec_ref(v_keys_983_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg___boxed(lean_object* v_x_989_, lean_object* v_x_990_, lean_object* v_x_991_, lean_object* v_x_992_, lean_object* v_x_993_){
_start:
{
size_t v_x_27498__boxed_994_; size_t v_x_27499__boxed_995_; lean_object* v_res_996_; 
v_x_27498__boxed_994_ = lean_unbox_usize(v_x_990_);
lean_dec(v_x_990_);
v_x_27499__boxed_995_ = lean_unbox_usize(v_x_991_);
lean_dec(v_x_991_);
v_res_996_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_x_989_, v_x_27498__boxed_994_, v_x_27499__boxed_995_, v_x_992_, v_x_993_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg(lean_object* v_x_997_, lean_object* v_x_998_, lean_object* v_x_999_){
_start:
{
size_t v___x_1000_; size_t v___x_1001_; size_t v___x_1002_; uint64_t v___x_1003_; size_t v___x_1004_; size_t v___x_1005_; lean_object* v___x_1006_; 
v___x_1000_ = lean_ptr_addr(v_x_998_);
v___x_1001_ = ((size_t)3ULL);
v___x_1002_ = lean_usize_shift_right(v___x_1000_, v___x_1001_);
v___x_1003_ = lean_usize_to_uint64(v___x_1002_);
v___x_1004_ = lean_uint64_to_usize(v___x_1003_);
v___x_1005_ = ((size_t)1ULL);
v___x_1006_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_x_997_, v___x_1004_, v___x_1005_, v_x_998_, v_x_999_);
return v___x_1006_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1007_ = lean_unsigned_to_nat(32u);
v___x_1008_ = lean_mk_empty_array_with_capacity(v___x_1007_);
v___x_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
return v___x_1009_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1(void){
_start:
{
size_t v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1010_ = ((size_t)5ULL);
v___x_1011_ = lean_unsigned_to_nat(0u);
v___x_1012_ = lean_unsigned_to_nat(32u);
v___x_1013_ = lean_mk_empty_array_with_capacity(v___x_1012_);
v___x_1014_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0);
v___x_1015_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
lean_ctor_set(v___x_1015_, 1, v___x_1013_);
lean_ctor_set(v___x_1015_, 2, v___x_1011_);
lean_ctor_set(v___x_1015_, 3, v___x_1011_);
lean_ctor_set_usize(v___x_1015_, 4, v___x_1010_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0(lean_object* v_expr_1016_, lean_object* v_size_1017_, lean_object* v_s_1018_){
_start:
{
lean_object* v_vars_1019_; lean_object* v_varMap_1020_; lean_object* v_varsHistory_1021_; lean_object* v_natToIntMap_1022_; lean_object* v_natDef_1023_; lean_object* v_dvds_1024_; lean_object* v_lowers_1025_; lean_object* v_uppers_1026_; lean_object* v_diseqs_1027_; lean_object* v_elimEqs_1028_; lean_object* v_elimStack_1029_; lean_object* v_occurs_1030_; lean_object* v_assignment_1031_; lean_object* v_nextCnstrId_1032_; uint8_t v_caseSplits_1033_; lean_object* v_steps_1034_; lean_object* v_conflict_x3f_1035_; lean_object* v_diseqSplits_1036_; lean_object* v_divMod_1037_; uint8_t v_usedCommRing_1038_; lean_object* v_nonlinearOccs_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1057_; 
v_vars_1019_ = lean_ctor_get(v_s_1018_, 0);
v_varMap_1020_ = lean_ctor_get(v_s_1018_, 1);
v_varsHistory_1021_ = lean_ctor_get(v_s_1018_, 2);
v_natToIntMap_1022_ = lean_ctor_get(v_s_1018_, 3);
v_natDef_1023_ = lean_ctor_get(v_s_1018_, 4);
v_dvds_1024_ = lean_ctor_get(v_s_1018_, 5);
v_lowers_1025_ = lean_ctor_get(v_s_1018_, 6);
v_uppers_1026_ = lean_ctor_get(v_s_1018_, 7);
v_diseqs_1027_ = lean_ctor_get(v_s_1018_, 8);
v_elimEqs_1028_ = lean_ctor_get(v_s_1018_, 9);
v_elimStack_1029_ = lean_ctor_get(v_s_1018_, 10);
v_occurs_1030_ = lean_ctor_get(v_s_1018_, 11);
v_assignment_1031_ = lean_ctor_get(v_s_1018_, 12);
v_nextCnstrId_1032_ = lean_ctor_get(v_s_1018_, 13);
v_caseSplits_1033_ = lean_ctor_get_uint8(v_s_1018_, sizeof(void*)*19);
v_steps_1034_ = lean_ctor_get(v_s_1018_, 14);
v_conflict_x3f_1035_ = lean_ctor_get(v_s_1018_, 15);
v_diseqSplits_1036_ = lean_ctor_get(v_s_1018_, 16);
v_divMod_1037_ = lean_ctor_get(v_s_1018_, 17);
v_usedCommRing_1038_ = lean_ctor_get_uint8(v_s_1018_, sizeof(void*)*19 + 1);
v_nonlinearOccs_1039_ = lean_ctor_get(v_s_1018_, 18);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_s_1018_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1041_ = v_s_1018_;
v_isShared_1042_ = v_isSharedCheck_1057_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_nonlinearOccs_1039_);
lean_inc(v_divMod_1037_);
lean_inc(v_diseqSplits_1036_);
lean_inc(v_conflict_x3f_1035_);
lean_inc(v_steps_1034_);
lean_inc(v_nextCnstrId_1032_);
lean_inc(v_assignment_1031_);
lean_inc(v_occurs_1030_);
lean_inc(v_elimStack_1029_);
lean_inc(v_elimEqs_1028_);
lean_inc(v_diseqs_1027_);
lean_inc(v_uppers_1026_);
lean_inc(v_lowers_1025_);
lean_inc(v_dvds_1024_);
lean_inc(v_natDef_1023_);
lean_inc(v_natToIntMap_1022_);
lean_inc(v_varsHistory_1021_);
lean_inc(v_varMap_1020_);
lean_inc(v_vars_1019_);
lean_dec(v_s_1018_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1057_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1055_; 
lean_inc_ref(v_expr_1016_);
v___x_1043_ = l_Lean_PersistentArray_push___redArg(v_vars_1019_, v_expr_1016_);
v___x_1044_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg(v_varMap_1020_, v_expr_1016_, v_size_1017_);
v___x_1045_ = lean_box(0);
v___x_1046_ = l_Lean_PersistentArray_push___redArg(v_dvds_1024_, v___x_1045_);
v___x_1047_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1);
v___x_1048_ = l_Lean_PersistentArray_push___redArg(v_lowers_1025_, v___x_1047_);
v___x_1049_ = l_Lean_PersistentArray_push___redArg(v_uppers_1026_, v___x_1047_);
v___x_1050_ = l_Lean_PersistentArray_push___redArg(v_diseqs_1027_, v___x_1047_);
v___x_1051_ = l_Lean_PersistentArray_push___redArg(v_elimEqs_1028_, v___x_1045_);
v___x_1052_ = lean_box(1);
v___x_1053_ = l_Lean_PersistentArray_push___redArg(v_occurs_1030_, v___x_1052_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 11, v___x_1053_);
lean_ctor_set(v___x_1041_, 9, v___x_1051_);
lean_ctor_set(v___x_1041_, 8, v___x_1050_);
lean_ctor_set(v___x_1041_, 7, v___x_1049_);
lean_ctor_set(v___x_1041_, 6, v___x_1048_);
lean_ctor_set(v___x_1041_, 5, v___x_1046_);
lean_ctor_set(v___x_1041_, 1, v___x_1044_);
lean_ctor_set(v___x_1041_, 0, v___x_1043_);
v___x_1055_ = v___x_1041_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1043_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v___x_1044_);
lean_ctor_set(v_reuseFailAlloc_1056_, 2, v_varsHistory_1021_);
lean_ctor_set(v_reuseFailAlloc_1056_, 3, v_natToIntMap_1022_);
lean_ctor_set(v_reuseFailAlloc_1056_, 4, v_natDef_1023_);
lean_ctor_set(v_reuseFailAlloc_1056_, 5, v___x_1046_);
lean_ctor_set(v_reuseFailAlloc_1056_, 6, v___x_1048_);
lean_ctor_set(v_reuseFailAlloc_1056_, 7, v___x_1049_);
lean_ctor_set(v_reuseFailAlloc_1056_, 8, v___x_1050_);
lean_ctor_set(v_reuseFailAlloc_1056_, 9, v___x_1051_);
lean_ctor_set(v_reuseFailAlloc_1056_, 10, v_elimStack_1029_);
lean_ctor_set(v_reuseFailAlloc_1056_, 11, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1056_, 12, v_assignment_1031_);
lean_ctor_set(v_reuseFailAlloc_1056_, 13, v_nextCnstrId_1032_);
lean_ctor_set(v_reuseFailAlloc_1056_, 14, v_steps_1034_);
lean_ctor_set(v_reuseFailAlloc_1056_, 15, v_conflict_x3f_1035_);
lean_ctor_set(v_reuseFailAlloc_1056_, 16, v_diseqSplits_1036_);
lean_ctor_set(v_reuseFailAlloc_1056_, 17, v_divMod_1037_);
lean_ctor_set(v_reuseFailAlloc_1056_, 18, v_nonlinearOccs_1039_);
lean_ctor_set_uint8(v_reuseFailAlloc_1056_, sizeof(void*)*19, v_caseSplits_1033_);
lean_ctor_set_uint8(v_reuseFailAlloc_1056_, sizeof(void*)*19 + 1, v_usedCommRing_1038_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1058_, lean_object* v_vals_1059_, lean_object* v_i_1060_, lean_object* v_k_1061_){
_start:
{
lean_object* v___x_1062_; uint8_t v___x_1063_; 
v___x_1062_ = lean_array_get_size(v_keys_1058_);
v___x_1063_ = lean_nat_dec_lt(v_i_1060_, v___x_1062_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; 
lean_dec(v_i_1060_);
v___x_1064_ = lean_box(0);
return v___x_1064_;
}
else
{
lean_object* v_k_x27_1065_; size_t v___x_1066_; size_t v___x_1067_; uint8_t v___x_1068_; 
v_k_x27_1065_ = lean_array_fget_borrowed(v_keys_1058_, v_i_1060_);
v___x_1066_ = lean_ptr_addr(v_k_1061_);
v___x_1067_ = lean_ptr_addr(v_k_x27_1065_);
v___x_1068_ = lean_usize_dec_eq(v___x_1066_, v___x_1067_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = lean_unsigned_to_nat(1u);
v___x_1070_ = lean_nat_add(v_i_1060_, v___x_1069_);
lean_dec(v_i_1060_);
v_i_1060_ = v___x_1070_;
goto _start;
}
else
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = lean_array_fget_borrowed(v_vals_1059_, v_i_1060_);
lean_dec(v_i_1060_);
lean_inc(v___x_1072_);
v___x_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
return v___x_1073_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1074_, lean_object* v_vals_1075_, lean_object* v_i_1076_, lean_object* v_k_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(v_keys_1074_, v_vals_1075_, v_i_1076_, v_k_1077_);
lean_dec_ref(v_k_1077_);
lean_dec_ref(v_vals_1075_);
lean_dec_ref(v_keys_1074_);
return v_res_1078_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(lean_object* v_x_1079_, size_t v_x_1080_, lean_object* v_x_1081_){
_start:
{
if (lean_obj_tag(v_x_1079_) == 0)
{
lean_object* v_es_1082_; lean_object* v___x_1083_; size_t v___x_1084_; size_t v___x_1085_; lean_object* v_j_1086_; lean_object* v___x_1087_; 
v_es_1082_ = lean_ctor_get(v_x_1079_, 0);
v___x_1083_ = lean_box(2);
v___x_1084_ = ((size_t)31ULL);
v___x_1085_ = lean_usize_land(v_x_1080_, v___x_1084_);
v_j_1086_ = lean_usize_to_nat(v___x_1085_);
v___x_1087_ = lean_array_get_borrowed(v___x_1083_, v_es_1082_, v_j_1086_);
lean_dec(v_j_1086_);
switch(lean_obj_tag(v___x_1087_))
{
case 0:
{
lean_object* v_key_1088_; lean_object* v_val_1089_; size_t v___x_1090_; size_t v___x_1091_; uint8_t v___x_1092_; 
v_key_1088_ = lean_ctor_get(v___x_1087_, 0);
v_val_1089_ = lean_ctor_get(v___x_1087_, 1);
v___x_1090_ = lean_ptr_addr(v_x_1081_);
v___x_1091_ = lean_ptr_addr(v_key_1088_);
v___x_1092_ = lean_usize_dec_eq(v___x_1090_, v___x_1091_);
if (v___x_1092_ == 0)
{
lean_object* v___x_1093_; 
v___x_1093_ = lean_box(0);
return v___x_1093_;
}
else
{
lean_object* v___x_1094_; 
lean_inc(v_val_1089_);
v___x_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1094_, 0, v_val_1089_);
return v___x_1094_;
}
}
case 1:
{
lean_object* v_node_1095_; size_t v___x_1096_; size_t v___x_1097_; 
v_node_1095_ = lean_ctor_get(v___x_1087_, 0);
v___x_1096_ = ((size_t)5ULL);
v___x_1097_ = lean_usize_shift_right(v_x_1080_, v___x_1096_);
v_x_1079_ = v_node_1095_;
v_x_1080_ = v___x_1097_;
goto _start;
}
default: 
{
lean_object* v___x_1099_; 
v___x_1099_ = lean_box(0);
return v___x_1099_;
}
}
}
else
{
lean_object* v_ks_1100_; lean_object* v_vs_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v_ks_1100_ = lean_ctor_get(v_x_1079_, 0);
v_vs_1101_ = lean_ctor_get(v_x_1079_, 1);
v___x_1102_ = lean_unsigned_to_nat(0u);
v___x_1103_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(v_ks_1100_, v_vs_1101_, v___x_1102_, v_x_1081_);
return v___x_1103_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1079_ = stack[0].m_obj;
size_t v_x_1080_ = stack[1].m_num;
lean_object* v_x_1081_ = stack[2].m_obj;
lean_object* v_res_1104_;
v_res_1104_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(v_x_1079_, v_x_1080_, v_x_1081_);
stack->m_obj
 = v_res_1104_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg___boxed(lean_object* v_x_1105_, lean_object* v_x_1106_, lean_object* v_x_1107_){
_start:
{
size_t v_x_27899__boxed_1108_; lean_object* v_res_1109_; 
v_x_27899__boxed_1108_ = lean_unbox_usize(v_x_1106_);
lean_dec(v_x_1106_);
v_res_1109_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(v_x_1105_, v_x_27899__boxed_1108_, v_x_1107_);
lean_dec_ref(v_x_1107_);
lean_dec_ref(v_x_1105_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(lean_object* v_x_1110_, lean_object* v_x_1111_){
_start:
{
size_t v___x_1112_; size_t v___x_1113_; size_t v___x_1114_; uint64_t v___x_1115_; size_t v___x_1116_; lean_object* v___x_1117_; 
v___x_1112_ = lean_ptr_addr(v_x_1111_);
v___x_1113_ = ((size_t)3ULL);
v___x_1114_ = lean_usize_shift_right(v___x_1112_, v___x_1113_);
v___x_1115_ = lean_usize_to_uint64(v___x_1114_);
v___x_1116_ = lean_uint64_to_usize(v___x_1115_);
v___x_1117_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(v_x_1110_, v___x_1116_, v_x_1111_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg___boxed(lean_object* v_x_1118_, lean_object* v_x_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(v_x_1118_, v_x_1119_);
lean_dec_ref(v_x_1119_);
lean_dec_ref(v_x_1118_);
return v_res_1120_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4(lean_object* v_msgData_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v___x_1127_; lean_object* v_env_1128_; uint8_t v___x_1129_; lean_object* v_env_1130_; lean_object* v___x_1131_; lean_object* v_toCold_1132_; lean_object* v_mctx_1133_; lean_object* v_lctx_1134_; lean_object* v_options_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1127_ = lean_st_ref_get(v___y_1125_);
v_env_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc_ref(v_env_1128_);
lean_dec(v___x_1127_);
v___x_1129_ = 0;
v_env_1130_ = l_Lean_Environment_setRecordingDeps(v_env_1128_, v___x_1129_);
v___x_1131_ = lean_st_ref_get(v___y_1123_);
v_toCold_1132_ = lean_ctor_get(v___y_1124_, 0);
v_mctx_1133_ = lean_ctor_get(v___x_1131_, 0);
lean_inc_ref(v_mctx_1133_);
lean_dec(v___x_1131_);
v_lctx_1134_ = lean_ctor_get(v___y_1122_, 2);
v_options_1135_ = lean_ctor_get(v_toCold_1132_, 2);
lean_inc_ref(v_options_1135_);
lean_inc_ref(v_lctx_1134_);
v___x_1136_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1136_, 0, v_env_1130_);
lean_ctor_set(v___x_1136_, 1, v_mctx_1133_);
lean_ctor_set(v___x_1136_, 2, v_lctx_1134_);
lean_ctor_set(v___x_1136_, 3, v_options_1135_);
v___x_1137_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
lean_ctor_set(v___x_1137_, 1, v_msgData_1121_);
v___x_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1121_ = stack[0].m_obj;
lean_object* v___y_1122_ = stack[1].m_obj;
lean_object* v___y_1123_ = stack[2].m_obj;
lean_object* v___y_1124_ = stack[3].m_obj;
lean_object* v___y_1125_ = stack[4].m_obj;
lean_object* v_res_1139_;
v_res_1139_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4(v_msgData_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
stack->m_obj
 = v_res_1139_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4___boxed(lean_object* v_msgData_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4(v_msgData_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
return v_res_1146_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1147_; double v___x_1148_; 
v___x_1147_ = lean_unsigned_to_nat(0u);
v___x_1148_ = lean_float_of_nat(v___x_1147_);
return v___x_1148_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(lean_object* v_cls_1152_, lean_object* v_msg_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
lean_object* v_ref_1159_; lean_object* v___x_1160_; lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1206_; 
v_ref_1159_ = lean_ctor_get(v___y_1156_, 2);
v___x_1160_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4(v_msg_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1163_ = v___x_1160_;
v_isShared_1164_ = v_isSharedCheck_1206_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1160_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1206_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1165_; lean_object* v_traceState_1166_; lean_object* v_env_1167_; lean_object* v_nextMacroScope_1168_; lean_object* v_ngen_1169_; lean_object* v_auxDeclNGen_1170_; lean_object* v_cache_1171_; lean_object* v_recordedDeps_1172_; lean_object* v_messages_1173_; lean_object* v_infoState_1174_; lean_object* v_snapshotTasks_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1205_; 
v___x_1165_ = lean_st_ref_take(v___y_1157_);
v_traceState_1166_ = lean_ctor_get(v___x_1165_, 4);
v_env_1167_ = lean_ctor_get(v___x_1165_, 0);
v_nextMacroScope_1168_ = lean_ctor_get(v___x_1165_, 1);
v_ngen_1169_ = lean_ctor_get(v___x_1165_, 2);
v_auxDeclNGen_1170_ = lean_ctor_get(v___x_1165_, 3);
v_cache_1171_ = lean_ctor_get(v___x_1165_, 5);
v_recordedDeps_1172_ = lean_ctor_get(v___x_1165_, 6);
v_messages_1173_ = lean_ctor_get(v___x_1165_, 7);
v_infoState_1174_ = lean_ctor_get(v___x_1165_, 8);
v_snapshotTasks_1175_ = lean_ctor_get(v___x_1165_, 9);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1177_ = v___x_1165_;
v_isShared_1178_ = v_isSharedCheck_1205_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_snapshotTasks_1175_);
lean_inc(v_infoState_1174_);
lean_inc(v_messages_1173_);
lean_inc(v_recordedDeps_1172_);
lean_inc(v_cache_1171_);
lean_inc(v_traceState_1166_);
lean_inc(v_auxDeclNGen_1170_);
lean_inc(v_ngen_1169_);
lean_inc(v_nextMacroScope_1168_);
lean_inc(v_env_1167_);
lean_dec(v___x_1165_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1205_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
uint64_t v_tid_1179_; lean_object* v_traces_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1204_; 
v_tid_1179_ = lean_ctor_get_uint64(v_traceState_1166_, sizeof(void*)*1);
v_traces_1180_ = lean_ctor_get(v_traceState_1166_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v_traceState_1166_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1182_ = v_traceState_1166_;
v_isShared_1183_ = v_isSharedCheck_1204_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_traces_1180_);
lean_dec(v_traceState_1166_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1204_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; double v___x_1186_; uint8_t v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1195_; 
v___x_1184_ = lean_box(0);
v___x_1185_ = lean_box(0);
v___x_1186_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0);
v___x_1187_ = 0;
v___x_1188_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__1));
v___x_1189_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1189_, 0, v_cls_1152_);
lean_ctor_set(v___x_1189_, 1, v___x_1185_);
lean_ctor_set(v___x_1189_, 2, v___x_1188_);
lean_ctor_set_float(v___x_1189_, sizeof(void*)*3, v___x_1186_);
lean_ctor_set_float(v___x_1189_, sizeof(void*)*3 + 8, v___x_1186_);
lean_ctor_set_uint8(v___x_1189_, sizeof(void*)*3 + 16, v___x_1187_);
v___x_1190_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__2));
v___x_1191_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1189_);
lean_ctor_set(v___x_1191_, 1, v_a_1161_);
lean_ctor_set(v___x_1191_, 2, v___x_1190_);
lean_inc(v_ref_1159_);
v___x_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1192_, 0, v_ref_1159_);
lean_ctor_set(v___x_1192_, 1, v___x_1191_);
v___x_1193_ = l_Lean_PersistentArray_push___redArg(v_traces_1180_, v___x_1192_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 0, v___x_1193_);
v___x_1195_ = v___x_1182_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1193_);
lean_ctor_set_uint64(v_reuseFailAlloc_1203_, sizeof(void*)*1, v_tid_1179_);
v___x_1195_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
lean_object* v___x_1197_; 
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 4, v___x_1195_);
v___x_1197_ = v___x_1177_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_env_1167_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v_nextMacroScope_1168_);
lean_ctor_set(v_reuseFailAlloc_1202_, 2, v_ngen_1169_);
lean_ctor_set(v_reuseFailAlloc_1202_, 3, v_auxDeclNGen_1170_);
lean_ctor_set(v_reuseFailAlloc_1202_, 4, v___x_1195_);
lean_ctor_set(v_reuseFailAlloc_1202_, 5, v_cache_1171_);
lean_ctor_set(v_reuseFailAlloc_1202_, 6, v_recordedDeps_1172_);
lean_ctor_set(v_reuseFailAlloc_1202_, 7, v_messages_1173_);
lean_ctor_set(v_reuseFailAlloc_1202_, 8, v_infoState_1174_);
lean_ctor_set(v_reuseFailAlloc_1202_, 9, v_snapshotTasks_1175_);
v___x_1197_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
lean_object* v___x_1198_; lean_object* v___x_1200_; 
v___x_1198_ = lean_st_ref_put(v___y_1157_, v___x_1197_);
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 0, v___x_1184_);
v___x_1200_ = v___x_1163_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1184_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1152_ = stack[0].m_obj;
lean_object* v_msg_1153_ = stack[1].m_obj;
lean_object* v___y_1154_ = stack[2].m_obj;
lean_object* v___y_1155_ = stack[3].m_obj;
lean_object* v___y_1156_ = stack[4].m_obj;
lean_object* v___y_1157_ = stack[5].m_obj;
lean_object* v_res_1207_;
v_res_1207_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(v_cls_1152_, v_msg_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
stack->m_obj
 = v_res_1207_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___boxed(lean_object* v_cls_1208_, lean_object* v_msg_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(v_cls_1208_, v_msg_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
return v_res_1215_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7(void){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1228_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4));
v___x_1229_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__6));
v___x_1230_ = l_Lean_Name_append(v___x_1229_, v___x_1228_);
return v___x_1230_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9(void){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1232_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__8));
v___x_1233_ = l_Lean_stringToMessageData(v___x_1232_);
return v___x_1233_;
}
}
lean_object* lean_grind_cutsat_mk_var(lean_object* v_expr_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v___x_1246_; 
v___x_1246_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1235_, v_a_1243_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1376_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1249_ = v___x_1246_;
v_isShared_1250_ = v_isSharedCheck_1376_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1246_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1376_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v_varMap_1251_; lean_object* v___x_1252_; 
v_varMap_1251_ = lean_ctor_get(v_a_1247_, 1);
lean_inc_ref(v_varMap_1251_);
lean_dec(v_a_1247_);
v___x_1252_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(v_varMap_1251_, v_expr_1234_);
lean_dec_ref(v_varMap_1251_);
if (lean_obj_tag(v___x_1252_) == 1)
{
lean_object* v_val_1253_; lean_object* v___x_1255_; 
lean_dec(v_a_1244_);
lean_dec_ref(v_a_1243_);
lean_dec(v_a_1242_);
lean_dec_ref(v_a_1241_);
lean_dec(v_a_1240_);
lean_dec_ref(v_a_1239_);
lean_dec(v_a_1238_);
lean_dec_ref(v_a_1237_);
lean_dec(v_a_1236_);
lean_dec(v_a_1235_);
lean_dec_ref(v_expr_1234_);
v_val_1253_ = lean_ctor_get(v___x_1252_, 0);
lean_inc(v_val_1253_);
lean_dec_ref_known(v___x_1252_, 1);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 0, v_val_1253_);
v___x_1255_ = v___x_1249_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_val_1253_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
else
{
lean_object* v___x_1257_; 
lean_dec(v___x_1252_);
lean_del_object(v___x_1249_);
v___x_1257_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1235_, v_a_1243_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v_a_1258_; lean_object* v_vars_1259_; lean_object* v_toCold_1260_; lean_object* v_options_1261_; lean_object* v_size_1262_; lean_object* v_inheritedTraceOptions_1263_; uint8_t v_hasTrace_1264_; lean_object* v___f_1265_; lean_object* v___y_1267_; lean_object* v___y_1268_; lean_object* v___y_1269_; lean_object* v___y_1270_; lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1276_; 
v_a_1258_ = lean_ctor_get(v___x_1257_, 0);
lean_inc(v_a_1258_);
lean_dec_ref_known(v___x_1257_, 1);
v_vars_1259_ = lean_ctor_get(v_a_1258_, 0);
lean_inc_ref(v_vars_1259_);
lean_dec(v_a_1258_);
v_toCold_1260_ = lean_ctor_get(v_a_1243_, 0);
v_options_1261_ = lean_ctor_get(v_toCold_1260_, 2);
v_size_1262_ = lean_ctor_get(v_vars_1259_, 2);
lean_inc_n(v_size_1262_, 2);
lean_dec_ref(v_vars_1259_);
v_inheritedTraceOptions_1263_ = lean_ctor_get(v_toCold_1260_, 11);
v_hasTrace_1264_ = lean_ctor_get_uint8(v_options_1261_, sizeof(void*)*1);
lean_inc_ref(v_expr_1234_);
v___f_1265_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0), 3, 2);
lean_closure_set(v___f_1265_, 0, v_expr_1234_);
lean_closure_set(v___f_1265_, 1, v_size_1262_);
if (v_hasTrace_1264_ == 0)
{
v___y_1267_ = v_a_1235_;
v___y_1268_ = v_a_1236_;
v___y_1269_ = v_a_1237_;
v___y_1270_ = v_a_1238_;
v___y_1271_ = v_a_1239_;
v___y_1272_ = v_a_1240_;
v___y_1273_ = v_a_1241_;
v___y_1274_ = v_a_1242_;
v___y_1275_ = v_a_1243_;
v___y_1276_ = v_a_1244_;
goto v___jp_1266_;
}
else
{
lean_object* v___x_1349_; lean_object* v___x_1350_; uint8_t v___x_1351_; 
v___x_1349_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4));
v___x_1350_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7);
v___x_1351_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1263_, v_options_1261_, v___x_1350_);
if (v___x_1351_ == 0)
{
v___y_1267_ = v_a_1235_;
v___y_1268_ = v_a_1236_;
v___y_1269_ = v_a_1237_;
v___y_1270_ = v_a_1238_;
v___y_1271_ = v_a_1239_;
v___y_1272_ = v_a_1240_;
v___y_1273_ = v_a_1241_;
v___y_1274_ = v_a_1242_;
v___y_1275_ = v_a_1243_;
v___y_1276_ = v_a_1244_;
goto v___jp_1266_;
}
else
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
lean_inc_ref(v_expr_1234_);
v___x_1352_ = l_Lean_MessageData_ofExpr(v_expr_1234_);
v___x_1353_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9);
v___x_1354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1352_);
lean_ctor_set(v___x_1354_, 1, v___x_1353_);
lean_inc(v_size_1262_);
v___x_1355_ = l_Nat_reprFast(v_size_1262_);
v___x_1356_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1355_);
v___x_1357_ = l_Lean_MessageData_ofFormat(v___x_1356_);
v___x_1358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1354_);
lean_ctor_set(v___x_1358_, 1, v___x_1357_);
v___x_1359_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(v___x_1349_, v___x_1358_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_dec_ref_known(v___x_1359_, 1);
v___y_1267_ = v_a_1235_;
v___y_1268_ = v_a_1236_;
v___y_1269_ = v_a_1237_;
v___y_1270_ = v_a_1238_;
v___y_1271_ = v_a_1239_;
v___y_1272_ = v_a_1240_;
v___y_1273_ = v_a_1241_;
v___y_1274_ = v_a_1242_;
v___y_1275_ = v_a_1243_;
v___y_1276_ = v_a_1244_;
goto v___jp_1266_;
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
lean_dec_ref(v___f_1265_);
lean_dec(v_size_1262_);
lean_dec(v_a_1244_);
lean_dec_ref(v_a_1243_);
lean_dec(v_a_1242_);
lean_dec_ref(v_a_1241_);
lean_dec(v_a_1240_);
lean_dec_ref(v_a_1239_);
lean_dec(v_a_1238_);
lean_dec_ref(v_a_1237_);
lean_dec(v_a_1236_);
lean_dec(v_a_1235_);
lean_dec_ref(v_expr_1234_);
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1359_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1359_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
}
v___jp_1266_:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1277_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_1278_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1277_, v___f_1265_, v___y_1267_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v___x_1279_; 
lean_dec_ref_known(v___x_1278_, 1);
lean_inc_ref(v_expr_1234_);
v___x_1279_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_1277_, v_expr_1234_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v___x_1280_; 
lean_dec_ref_known(v___x_1279_, 1);
lean_inc(v_size_1262_);
lean_inc_ref(v_expr_1234_);
v___x_1280_ = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(v_expr_1234_, v_size_1262_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v___x_1281_; 
lean_dec_ref_known(v___x_1280_, 1);
lean_inc(v_size_1262_);
lean_inc_ref(v_expr_1234_);
v___x_1281_ = l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg(v_expr_1234_, v_size_1262_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v___x_1282_; 
lean_dec_ref_known(v___x_1281_, 1);
lean_inc_ref(v_expr_1234_);
v___x_1282_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm(v_expr_1234_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1308_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1285_ = v___x_1282_;
v_isShared_1286_ = v_isSharedCheck_1308_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1282_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1308_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
uint8_t v___x_1287_; 
v___x_1287_ = lean_unbox(v_a_1283_);
lean_dec(v_a_1283_);
if (v___x_1287_ == 0)
{
lean_object* v___x_1289_; 
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v_expr_1234_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 0, v_size_1262_);
v___x_1289_ = v___x_1285_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_size_1262_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
else
{
lean_object* v___x_1291_; 
lean_del_object(v___x_1285_);
lean_inc(v_size_1262_);
v___x_1291_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt(v_expr_1234_, v_size_1262_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec(v___y_1267_);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1298_ == 0)
{
lean_object* v_unused_1299_; 
v_unused_1299_ = lean_ctor_get(v___x_1291_, 0);
lean_dec(v_unused_1299_);
v___x_1293_ = v___x_1291_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_dec(v___x_1291_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 0, v_size_1262_);
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_size_1262_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
else
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
lean_dec(v_size_1262_);
v_a_1300_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1291_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1291_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1300_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
}
}
else
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec(v_size_1262_);
lean_dec_ref(v_expr_1234_);
v_a_1309_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1311_ = v___x_1282_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1282_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1309_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
else
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec(v_size_1262_);
lean_dec_ref(v_expr_1234_);
v_a_1317_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1281_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1281_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_a_1317_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
else
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec(v_size_1262_);
lean_dec_ref(v_expr_1234_);
v_a_1325_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1280_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1280_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec(v_size_1262_);
lean_dec_ref(v_expr_1234_);
v_a_1333_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1279_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1279_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1333_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
else
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec(v_size_1262_);
lean_dec_ref(v_expr_1234_);
v_a_1341_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___x_1278_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1278_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1341_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
lean_dec(v_a_1244_);
lean_dec_ref(v_a_1243_);
lean_dec(v_a_1242_);
lean_dec_ref(v_a_1241_);
lean_dec(v_a_1240_);
lean_dec_ref(v_a_1239_);
lean_dec(v_a_1238_);
lean_dec_ref(v_a_1237_);
lean_dec(v_a_1236_);
lean_dec(v_a_1235_);
lean_dec_ref(v_expr_1234_);
v_a_1368_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1257_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1257_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
}
}
else
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
lean_dec(v_a_1244_);
lean_dec_ref(v_a_1243_);
lean_dec(v_a_1242_);
lean_dec_ref(v_a_1241_);
lean_dec(v_a_1240_);
lean_dec_ref(v_a_1239_);
lean_dec(v_a_1238_);
lean_dec_ref(v_a_1237_);
lean_dec(v_a_1236_);
lean_dec(v_a_1235_);
lean_dec_ref(v_expr_1234_);
v_a_1377_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1379_ = v___x_1246_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1246_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1377_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
}
LEAN_EXPORT void lean_grind_cutsat_mk_var_0interp(lean_interpreter_value* stack)
{
lean_object* v_expr_1234_ = stack[0].m_obj;
lean_object* v_a_1235_ = stack[1].m_obj;
lean_object* v_a_1236_ = stack[2].m_obj;
lean_object* v_a_1237_ = stack[3].m_obj;
lean_object* v_a_1238_ = stack[4].m_obj;
lean_object* v_a_1239_ = stack[5].m_obj;
lean_object* v_a_1240_ = stack[6].m_obj;
lean_object* v_a_1241_ = stack[7].m_obj;
lean_object* v_a_1242_ = stack[8].m_obj;
lean_object* v_a_1243_ = stack[9].m_obj;
lean_object* v_a_1244_ = stack[10].m_obj;
lean_object* v_res_1385_;
v_res_1385_ = lean_grind_cutsat_mk_var(v_expr_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_);
stack->m_obj
 = v_res_1385_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___boxed(lean_object* v_expr_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = lean_grind_cutsat_mk_var(v_expr_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0(lean_object* v_00_u03b2_1399_, lean_object* v_x_1400_, lean_object* v_x_1401_){
_start:
{
lean_object* v___x_1402_; 
v___x_1402_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(v_x_1400_, v_x_1401_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___boxed(lean_object* v_00_u03b2_1403_, lean_object* v_x_1404_, lean_object* v_x_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0(v_00_u03b2_1403_, v_x_1404_, v_x_1405_);
lean_dec_ref(v_x_1405_);
lean_dec_ref(v_x_1404_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1(lean_object* v_00_u03b2_1407_, lean_object* v_x_1408_, lean_object* v_x_1409_, lean_object* v_x_1410_){
_start:
{
lean_object* v___x_1411_; 
v___x_1411_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg(v_x_1408_, v_x_1409_, v_x_1410_);
return v___x_1411_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2(lean_object* v_cls_1412_, lean_object* v_msg_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v___x_1425_; 
v___x_1425_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(v_cls_1412_, v_msg_1413_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
return v___x_1425_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1412_ = stack[0].m_obj;
lean_object* v_msg_1413_ = stack[1].m_obj;
lean_object* v___y_1414_ = stack[2].m_obj;
lean_object* v___y_1415_ = stack[3].m_obj;
lean_object* v___y_1416_ = stack[4].m_obj;
lean_object* v___y_1417_ = stack[5].m_obj;
lean_object* v___y_1418_ = stack[6].m_obj;
lean_object* v___y_1419_ = stack[7].m_obj;
lean_object* v___y_1420_ = stack[8].m_obj;
lean_object* v___y_1421_ = stack[9].m_obj;
lean_object* v___y_1422_ = stack[10].m_obj;
lean_object* v___y_1423_ = stack[11].m_obj;
lean_object* v_res_1426_;
v_res_1426_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2(v_cls_1412_, v_msg_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
stack->m_obj
 = v_res_1426_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___boxed(lean_object* v_cls_1427_, lean_object* v_msg_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2(v_cls_1427_, v_msg_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec(v___y_1429_);
return v_res_1440_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0(lean_object* v_00_u03b2_1441_, lean_object* v_x_1442_, size_t v_x_1443_, lean_object* v_x_1444_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(v_x_1442_, v_x_1443_, v_x_1444_);
return v___x_1445_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1442_ = stack[1].m_obj;
size_t v_x_1443_ = stack[2].m_num;
lean_object* v_x_1444_ = stack[3].m_obj;
lean_object* v_res_1446_;
v_res_1446_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0(lean_box(0), v_x_1442_, v_x_1443_, v_x_1444_);
stack->m_obj
 = v_res_1446_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1447_, lean_object* v_x_1448_, lean_object* v_x_1449_, lean_object* v_x_1450_){
_start:
{
size_t v_x_28761__boxed_1451_; lean_object* v_res_1452_; 
v_x_28761__boxed_1451_ = lean_unbox_usize(v_x_1449_);
lean_dec(v_x_1449_);
v_res_1452_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0(v_00_u03b2_1447_, v_x_1448_, v_x_28761__boxed_1451_, v_x_1450_);
lean_dec_ref(v_x_1450_);
lean_dec_ref(v_x_1448_);
return v_res_1452_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2(lean_object* v_00_u03b2_1453_, lean_object* v_x_1454_, size_t v_x_1455_, size_t v_x_1456_, lean_object* v_x_1457_, lean_object* v_x_1458_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_x_1454_, v_x_1455_, v_x_1456_, v_x_1457_, v_x_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1454_ = stack[1].m_obj;
size_t v_x_1455_ = stack[2].m_num;
size_t v_x_1456_ = stack[3].m_num;
lean_object* v_x_1457_ = stack[4].m_obj;
lean_object* v_x_1458_ = stack[5].m_obj;
lean_object* v_res_1460_;
v_res_1460_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2(lean_box(0), v_x_1454_, v_x_1455_, v_x_1456_, v_x_1457_, v_x_1458_);
stack->m_obj
 = v_res_1460_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1461_, lean_object* v_x_1462_, lean_object* v_x_1463_, lean_object* v_x_1464_, lean_object* v_x_1465_, lean_object* v_x_1466_){
_start:
{
size_t v_x_28779__boxed_1467_; size_t v_x_28780__boxed_1468_; lean_object* v_res_1469_; 
v_x_28779__boxed_1467_ = lean_unbox_usize(v_x_1463_);
lean_dec(v_x_1463_);
v_x_28780__boxed_1468_ = lean_unbox_usize(v_x_1464_);
lean_dec(v_x_1464_);
v_res_1469_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2(v_00_u03b2_1461_, v_x_1462_, v_x_28779__boxed_1467_, v_x_28780__boxed_1468_, v_x_1465_, v_x_1466_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1470_, lean_object* v_keys_1471_, lean_object* v_vals_1472_, lean_object* v_heq_1473_, lean_object* v_i_1474_, lean_object* v_k_1475_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(v_keys_1471_, v_vals_1472_, v_i_1474_, v_k_1475_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1477_, lean_object* v_keys_1478_, lean_object* v_vals_1479_, lean_object* v_heq_1480_, lean_object* v_i_1481_, lean_object* v_k_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1(v_00_u03b2_1477_, v_keys_1478_, v_vals_1479_, v_heq_1480_, v_i_1481_, v_k_1482_);
lean_dec_ref(v_k_1482_);
lean_dec_ref(v_vals_1479_);
lean_dec_ref(v_keys_1478_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1484_, lean_object* v_n_1485_, lean_object* v_k_1486_, lean_object* v_v_1487_){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4___redArg(v_n_1485_, v_k_1486_, v_v_1487_);
return v___x_1488_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1489_, size_t v_depth_1490_, lean_object* v_keys_1491_, lean_object* v_vals_1492_, lean_object* v_heq_1493_, lean_object* v_i_1494_, lean_object* v_entries_1495_){
_start:
{
lean_object* v___x_1496_; 
v___x_1496_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(v_depth_1490_, v_keys_1491_, v_vals_1492_, v_i_1494_, v_entries_1495_);
return v___x_1496_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1490_ = stack[1].m_num;
lean_object* v_keys_1491_ = stack[2].m_obj;
lean_object* v_vals_1492_ = stack[3].m_obj;
lean_object* v_i_1494_ = stack[5].m_obj;
lean_object* v_entries_1495_ = stack[6].m_obj;
lean_object* v_res_1497_;
v_res_1497_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5(lean_box(0), v_depth_1490_, v_keys_1491_, v_vals_1492_, lean_box(0), v_i_1494_, v_entries_1495_);
stack->m_obj
 = v_res_1497_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1498_, lean_object* v_depth_1499_, lean_object* v_keys_1500_, lean_object* v_vals_1501_, lean_object* v_heq_1502_, lean_object* v_i_1503_, lean_object* v_entries_1504_){
_start:
{
size_t v_depth_boxed_1505_; lean_object* v_res_1506_; 
v_depth_boxed_1505_ = lean_unbox_usize(v_depth_1499_);
lean_dec(v_depth_1499_);
v_res_1506_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5(v_00_u03b2_1498_, v_depth_boxed_1505_, v_keys_1500_, v_vals_1501_, v_heq_1502_, v_i_1503_, v_entries_1504_);
lean_dec_ref(v_vals_1501_);
lean_dec_ref(v_keys_1500_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_1507_, lean_object* v_x_1508_, lean_object* v_x_1509_, lean_object* v_x_1510_, lean_object* v_x_1511_){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7___redArg(v_x_1508_, v_x_1509_, v_x_1510_, v_x_1511_);
return v___x_1512_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2(void){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1516_ = lean_box(0);
v___x_1517_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__1));
v___x_1518_ = l_Lean_mkConst(v___x_1517_, v___x_1516_);
return v___x_1518_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(lean_object* v_e_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_){
_start:
{
lean_object* v___x_1525_; 
lean_inc(v_a_1523_);
lean_inc_ref(v_a_1522_);
lean_inc(v_a_1521_);
lean_inc_ref(v_a_1520_);
v___x_1525_ = lean_infer_type(v_e_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_);
if (lean_obj_tag(v___x_1525_) == 0)
{
lean_object* v_a_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v_a_1526_ = lean_ctor_get(v___x_1525_, 0);
lean_inc(v_a_1526_);
lean_dec_ref_known(v___x_1525_, 1);
v___x_1527_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2);
v___x_1528_ = l_Lean_Meta_isExprDefEq(v_a_1526_, v___x_1527_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_);
return v___x_1528_;
}
else
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1536_; 
v_a_1529_ = lean_ctor_get(v___x_1525_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1531_ = v___x_1525_;
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v___x_1525_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1534_; 
if (v_isShared_1532_ == 0)
{
v___x_1534_ = v___x_1531_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_a_1529_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1519_ = stack[0].m_obj;
lean_object* v_a_1520_ = stack[1].m_obj;
lean_object* v_a_1521_ = stack[2].m_obj;
lean_object* v_a_1522_ = stack[3].m_obj;
lean_object* v_a_1523_ = stack[4].m_obj;
lean_object* v_res_1537_;
v_res_1537_ = l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(v_e_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_);
stack->m_obj
 = v_res_1537_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___boxed(lean_object* v_e_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(v_e_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_);
lean_dec(v_a_1542_);
lean_dec_ref(v_a_1541_);
lean_dec(v_a_1540_);
lean_dec_ref(v_a_1539_);
return v_res_1544_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt(lean_object* v_e_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(v_e_1545_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
return v___x_1557_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_isInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1545_ = stack[0].m_obj;
lean_object* v_a_1546_ = stack[1].m_obj;
lean_object* v_a_1547_ = stack[2].m_obj;
lean_object* v_a_1548_ = stack[3].m_obj;
lean_object* v_a_1549_ = stack[4].m_obj;
lean_object* v_a_1550_ = stack[5].m_obj;
lean_object* v_a_1551_ = stack[6].m_obj;
lean_object* v_a_1552_ = stack[7].m_obj;
lean_object* v_a_1553_ = stack[8].m_obj;
lean_object* v_a_1554_ = stack[9].m_obj;
lean_object* v_a_1555_ = stack[10].m_obj;
lean_object* v_res_1558_;
v_res_1558_ = l_Lean_Meta_Grind_Arith_Cutsat_isInt(v_e_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_);
stack->m_obj
 = v_res_1558_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___boxed(lean_object* v_e_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Lean_Meta_Grind_Arith_Cutsat_isInt(v_e_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_);
lean_dec(v_a_1569_);
lean_dec_ref(v_a_1568_);
lean_dec(v_a_1567_);
lean_dec_ref(v_a_1566_);
lean_dec(v_a_1565_);
lean_dec_ref(v_a_1564_);
lean_dec(v_a_1563_);
lean_dec_ref(v_a_1562_);
lean_dec(v_a_1561_);
lean_dec(v_a_1560_);
return v_res_1571_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4(void){
_start:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1578_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__3));
v___x_1579_ = l_Lean_stringToMessageData(v___x_1578_);
return v___x_1579_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(lean_object* v_e_1580_, uint8_t v_report_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_){
_start:
{
lean_object* v___x_1595_; 
lean_inc_ref(v_e_1580_);
v___x_1595_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1580_, v_a_1585_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; lean_object* v___x_1597_; uint8_t v___x_1598_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_a_1596_);
lean_dec_ref_known(v___x_1595_, 1);
v___x_1597_ = l_Lean_Expr_cleanupAnnotations(v_a_1596_);
v___x_1598_ = l_Lean_Expr_isApp(v___x_1597_);
if (v___x_1598_ == 0)
{
lean_dec_ref(v___x_1597_);
lean_dec_ref(v_e_1580_);
goto v___jp_1589_;
}
else
{
lean_object* v_arg_1599_; lean_object* v___x_1600_; uint8_t v___x_1601_; 
v_arg_1599_ = lean_ctor_get(v___x_1597_, 1);
lean_inc_ref(v_arg_1599_);
v___x_1600_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1597_);
v___x_1601_ = l_Lean_Expr_isApp(v___x_1600_);
if (v___x_1601_ == 0)
{
lean_dec_ref(v___x_1600_);
lean_dec_ref(v_arg_1599_);
lean_dec_ref(v_e_1580_);
goto v___jp_1589_;
}
else
{
lean_object* v_arg_1602_; lean_object* v___x_1603_; uint8_t v___x_1604_; 
v_arg_1602_ = lean_ctor_get(v___x_1600_, 1);
lean_inc_ref(v_arg_1602_);
v___x_1603_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1600_);
v___x_1604_ = l_Lean_Expr_isApp(v___x_1603_);
if (v___x_1604_ == 0)
{
lean_dec_ref(v___x_1603_);
lean_dec_ref(v_arg_1602_);
lean_dec_ref(v_arg_1599_);
lean_dec_ref(v_e_1580_);
goto v___jp_1589_;
}
else
{
lean_object* v_arg_1605_; lean_object* v___x_1606_; uint8_t v___x_1607_; 
v_arg_1605_ = lean_ctor_get(v___x_1603_, 1);
lean_inc_ref(v_arg_1605_);
v___x_1606_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1603_);
v___x_1607_ = l_Lean_Expr_isApp(v___x_1606_);
if (v___x_1607_ == 0)
{
lean_dec_ref(v___x_1606_);
lean_dec_ref(v_arg_1605_);
lean_dec_ref(v_arg_1602_);
lean_dec_ref(v_arg_1599_);
lean_dec_ref(v_e_1580_);
goto v___jp_1589_;
}
else
{
lean_object* v___x_1608_; uint8_t v___x_1609_; 
v___x_1608_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1606_);
v___x_1609_ = l_Lean_Expr_isApp(v___x_1608_);
if (v___x_1609_ == 0)
{
lean_dec_ref(v___x_1608_);
lean_dec_ref(v_arg_1605_);
lean_dec_ref(v_arg_1602_);
lean_dec_ref(v_arg_1599_);
lean_dec_ref(v_e_1580_);
goto v___jp_1589_;
}
else
{
lean_object* v___x_1610_; uint8_t v___x_1611_; 
v___x_1610_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1608_);
v___x_1611_ = l_Lean_Expr_isApp(v___x_1610_);
if (v___x_1611_ == 0)
{
lean_dec_ref(v___x_1610_);
lean_dec_ref(v_arg_1605_);
lean_dec_ref(v_arg_1602_);
lean_dec_ref(v_arg_1599_);
lean_dec_ref(v_e_1580_);
goto v___jp_1589_;
}
else
{
lean_object* v___x_1612_; lean_object* v___x_1613_; uint8_t v___x_1614_; 
v___x_1612_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1610_);
v___x_1613_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__2));
v___x_1614_ = l_Lean_Expr_isConstOf(v___x_1612_, v___x_1613_);
lean_dec_ref(v___x_1612_);
if (v___x_1614_ == 0)
{
lean_dec_ref(v_arg_1605_);
lean_dec_ref(v_arg_1602_);
lean_dec_ref(v_arg_1599_);
lean_dec_ref(v_e_1580_);
goto v___jp_1589_;
}
else
{
lean_object* v___x_1615_; 
v___x_1615_ = l_Lean_Meta_Structural_isInstHAddInt___redArg(v_arg_1605_, v_a_1585_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1649_; 
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1618_ = v___x_1615_;
v_isShared_1619_ = v_isSharedCheck_1649_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1615_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1649_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
uint8_t v___x_1620_; 
v___x_1620_ = lean_unbox(v_a_1616_);
lean_dec(v_a_1616_);
if (v___x_1620_ == 0)
{
lean_del_object(v___x_1618_);
lean_dec_ref(v_arg_1602_);
lean_dec_ref(v_arg_1599_);
if (v_report_1581_ == 0)
{
lean_dec_ref(v_e_1580_);
goto v___jp_1592_;
}
else
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1621_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4);
v___x_1622_ = l_Lean_indentExpr(v_e_1580_);
v___x_1623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1621_);
lean_ctor_set(v___x_1623_, 1, v___x_1622_);
v___x_1624_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1582_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_a_1625_; uint8_t v_verbose_1626_; 
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_a_1625_);
lean_dec_ref_known(v___x_1624_, 1);
v_verbose_1626_ = lean_ctor_get_uint8(v_a_1625_, 0);
lean_dec(v_a_1625_);
if (v_verbose_1626_ == 0)
{
lean_dec_ref_known(v___x_1623_, 2);
goto v___jp_1592_;
}
else
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Lean_Meta_Sym_reportIssue(v___x_1623_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_dec_ref_known(v___x_1627_, 1);
goto v___jp_1592_;
}
else
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1635_; 
v_a_1628_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1630_ = v___x_1627_;
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v___x_1627_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1633_; 
if (v_isShared_1631_ == 0)
{
v___x_1633_ = v___x_1630_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_a_1628_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
}
}
else
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
lean_dec_ref_known(v___x_1623_, 2);
v_a_1636_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1624_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1624_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
}
else
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1647_; 
lean_dec_ref(v_e_1580_);
v___x_1644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1644_, 0, v_arg_1602_);
lean_ctor_set(v___x_1644_, 1, v_arg_1599_);
v___x_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1644_);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 0, v___x_1645_);
v___x_1647_ = v___x_1618_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v___x_1645_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
}
else
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1657_; 
lean_dec_ref(v_arg_1602_);
lean_dec_ref(v_arg_1599_);
lean_dec_ref(v_e_1580_);
v_a_1650_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1652_ = v___x_1615_;
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1615_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1650_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1665_; 
lean_dec_ref(v_e_1580_);
v_a_1658_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1660_ = v___x_1595_;
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1595_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1663_; 
if (v_isShared_1661_ == 0)
{
v___x_1663_ = v___x_1660_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_a_1658_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
v___jp_1589_:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = lean_box(0);
v___x_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1590_);
return v___x_1591_;
}
v___jp_1592_:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1593_ = lean_box(0);
v___x_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1593_);
return v___x_1594_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1580_ = stack[0].m_obj;
uint8_t v_report_1581_ = stack[1].m_num;
lean_object* v_a_1582_ = stack[2].m_obj;
lean_object* v_a_1583_ = stack[3].m_obj;
lean_object* v_a_1584_ = stack[4].m_obj;
lean_object* v_a_1585_ = stack[5].m_obj;
lean_object* v_a_1586_ = stack[6].m_obj;
lean_object* v_a_1587_ = stack[7].m_obj;
lean_object* v_res_1666_;
v_res_1666_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_1580_, v_report_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
stack->m_obj
 = v_res_1666_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___boxed(lean_object* v_e_1667_, lean_object* v_report_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_){
_start:
{
uint8_t v_report_boxed_1676_; lean_object* v_res_1677_; 
v_report_boxed_1676_ = lean_unbox(v_report_1668_);
v_res_1677_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_1667_, v_report_boxed_1676_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_);
lean_dec(v_a_1674_);
lean_dec_ref(v_a_1673_);
lean_dec(v_a_1672_);
lean_dec_ref(v_a_1671_);
lean_dec(v_a_1670_);
lean_dec_ref(v_a_1669_);
return v_res_1677_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f(lean_object* v_e_1678_, uint8_t v_report_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_){
_start:
{
lean_object* v___x_1691_; 
v___x_1691_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_1678_, v_report_1679_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_);
return v___x_1691_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1678_ = stack[0].m_obj;
uint8_t v_report_1679_ = stack[1].m_num;
lean_object* v_a_1680_ = stack[2].m_obj;
lean_object* v_a_1681_ = stack[3].m_obj;
lean_object* v_a_1682_ = stack[4].m_obj;
lean_object* v_a_1683_ = stack[5].m_obj;
lean_object* v_a_1684_ = stack[6].m_obj;
lean_object* v_a_1685_ = stack[7].m_obj;
lean_object* v_a_1686_ = stack[8].m_obj;
lean_object* v_a_1687_ = stack[9].m_obj;
lean_object* v_a_1688_ = stack[10].m_obj;
lean_object* v_a_1689_ = stack[11].m_obj;
lean_object* v_res_1692_;
v_res_1692_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f(v_e_1678_, v_report_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_);
stack->m_obj
 = v_res_1692_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___boxed(lean_object* v_e_1693_, lean_object* v_report_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_){
_start:
{
uint8_t v_report_boxed_1706_; lean_object* v_res_1707_; 
v_report_boxed_1706_ = lean_unbox(v_report_1694_);
v_res_1707_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f(v_e_1693_, v_report_boxed_1706_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
lean_dec(v_a_1704_);
lean_dec_ref(v_a_1703_);
lean_dec(v_a_1702_);
lean_dec_ref(v_a_1701_);
lean_dec(v_a_1700_);
lean_dec_ref(v_a_1699_);
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
lean_dec(v_a_1696_);
lean_dec(v_a_1695_);
return v_res_1707_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(lean_object* v_e_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_){
_start:
{
uint8_t v___x_1716_; lean_object* v___x_1717_; 
v___x_1716_ = 0;
v___x_1717_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_1708_, v___x_1716_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1731_; 
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1720_ = v___x_1717_;
v_isShared_1721_ = v_isSharedCheck_1731_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1717_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1731_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
if (lean_obj_tag(v_a_1718_) == 0)
{
lean_object* v___x_1722_; lean_object* v___x_1724_; 
v___x_1722_ = lean_box(v___x_1716_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 0, v___x_1722_);
v___x_1724_ = v___x_1720_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1722_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
else
{
uint8_t v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1729_; 
lean_dec_ref_known(v_a_1718_, 1);
v___x_1726_ = 1;
v___x_1727_ = lean_box(v___x_1726_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 0, v___x_1727_);
v___x_1729_ = v___x_1720_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___x_1727_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
else
{
lean_object* v_a_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1739_; 
v_a_1732_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1734_ = v___x_1717_;
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v___x_1717_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1737_; 
if (v_isShared_1735_ == 0)
{
v___x_1737_ = v___x_1734_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_a_1732_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1708_ = stack[0].m_obj;
lean_object* v_a_1709_ = stack[1].m_obj;
lean_object* v_a_1710_ = stack[2].m_obj;
lean_object* v_a_1711_ = stack[3].m_obj;
lean_object* v_a_1712_ = stack[4].m_obj;
lean_object* v_a_1713_ = stack[5].m_obj;
lean_object* v_a_1714_ = stack[6].m_obj;
lean_object* v_res_1740_;
v_res_1740_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(v_e_1708_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_);
stack->m_obj
 = v_res_1740_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg___boxed(lean_object* v_e_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(v_e_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_);
lean_dec(v_a_1747_);
lean_dec_ref(v_a_1746_);
lean_dec(v_a_1745_);
lean_dec_ref(v_a_1744_);
lean_dec(v_a_1743_);
lean_dec_ref(v_a_1742_);
return v_res_1749_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd(lean_object* v_e_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(v_e_1750_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_);
return v___x_1762_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_isAdd_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1750_ = stack[0].m_obj;
lean_object* v_a_1751_ = stack[1].m_obj;
lean_object* v_a_1752_ = stack[2].m_obj;
lean_object* v_a_1753_ = stack[3].m_obj;
lean_object* v_a_1754_ = stack[4].m_obj;
lean_object* v_a_1755_ = stack[5].m_obj;
lean_object* v_a_1756_ = stack[6].m_obj;
lean_object* v_a_1757_ = stack[7].m_obj;
lean_object* v_a_1758_ = stack[8].m_obj;
lean_object* v_a_1759_ = stack[9].m_obj;
lean_object* v_a_1760_ = stack[10].m_obj;
lean_object* v_res_1763_;
v_res_1763_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd(v_e_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_);
stack->m_obj
 = v_res_1763_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___boxed(lean_object* v_e_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd(v_e_1764_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_, v_a_1773_, v_a_1774_);
lean_dec(v_a_1774_);
lean_dec_ref(v_a_1773_);
lean_dec(v_a_1772_);
lean_dec_ref(v_a_1771_);
lean_dec(v_a_1770_);
lean_dec_ref(v_a_1769_);
lean_dec(v_a_1768_);
lean_dec_ref(v_a_1767_);
lean_dec(v_a_1766_);
lean_dec(v_a_1765_);
return v_res_1776_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(lean_object* v_e_1777_, uint8_t v_report_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_){
_start:
{
lean_object* v___x_1792_; 
lean_inc_ref(v_e_1777_);
v___x_1792_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1777_, v_a_1782_);
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_object* v_a_1793_; lean_object* v___x_1794_; uint8_t v___x_1795_; 
v_a_1793_ = lean_ctor_get(v___x_1792_, 0);
lean_inc(v_a_1793_);
lean_dec_ref_known(v___x_1792_, 1);
v___x_1794_ = l_Lean_Expr_cleanupAnnotations(v_a_1793_);
v___x_1795_ = l_Lean_Expr_isApp(v___x_1794_);
if (v___x_1795_ == 0)
{
lean_dec_ref(v___x_1794_);
lean_dec_ref(v_e_1777_);
goto v___jp_1786_;
}
else
{
lean_object* v_arg_1796_; lean_object* v___x_1797_; uint8_t v___x_1798_; 
v_arg_1796_ = lean_ctor_get(v___x_1794_, 1);
lean_inc_ref(v_arg_1796_);
v___x_1797_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1794_);
v___x_1798_ = l_Lean_Expr_isApp(v___x_1797_);
if (v___x_1798_ == 0)
{
lean_dec_ref(v___x_1797_);
lean_dec_ref(v_arg_1796_);
lean_dec_ref(v_e_1777_);
goto v___jp_1786_;
}
else
{
lean_object* v_arg_1799_; lean_object* v___x_1800_; uint8_t v___x_1801_; 
v_arg_1799_ = lean_ctor_get(v___x_1797_, 1);
lean_inc_ref(v_arg_1799_);
v___x_1800_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1797_);
v___x_1801_ = l_Lean_Expr_isApp(v___x_1800_);
if (v___x_1801_ == 0)
{
lean_dec_ref(v___x_1800_);
lean_dec_ref(v_arg_1799_);
lean_dec_ref(v_arg_1796_);
lean_dec_ref(v_e_1777_);
goto v___jp_1786_;
}
else
{
lean_object* v_arg_1802_; lean_object* v___x_1803_; uint8_t v___x_1804_; 
v_arg_1802_ = lean_ctor_get(v___x_1800_, 1);
lean_inc_ref(v_arg_1802_);
v___x_1803_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1800_);
v___x_1804_ = l_Lean_Expr_isApp(v___x_1803_);
if (v___x_1804_ == 0)
{
lean_dec_ref(v___x_1803_);
lean_dec_ref(v_arg_1802_);
lean_dec_ref(v_arg_1799_);
lean_dec_ref(v_arg_1796_);
lean_dec_ref(v_e_1777_);
goto v___jp_1786_;
}
else
{
lean_object* v___x_1805_; uint8_t v___x_1806_; 
v___x_1805_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1803_);
v___x_1806_ = l_Lean_Expr_isApp(v___x_1805_);
if (v___x_1806_ == 0)
{
lean_dec_ref(v___x_1805_);
lean_dec_ref(v_arg_1802_);
lean_dec_ref(v_arg_1799_);
lean_dec_ref(v_arg_1796_);
lean_dec_ref(v_e_1777_);
goto v___jp_1786_;
}
else
{
lean_object* v___x_1807_; uint8_t v___x_1808_; 
v___x_1807_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1805_);
v___x_1808_ = l_Lean_Expr_isApp(v___x_1807_);
if (v___x_1808_ == 0)
{
lean_dec_ref(v___x_1807_);
lean_dec_ref(v_arg_1802_);
lean_dec_ref(v_arg_1799_);
lean_dec_ref(v_arg_1796_);
lean_dec_ref(v_e_1777_);
goto v___jp_1786_;
}
else
{
lean_object* v___x_1809_; lean_object* v___x_1810_; uint8_t v___x_1811_; 
v___x_1809_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1807_);
v___x_1810_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11));
v___x_1811_ = l_Lean_Expr_isConstOf(v___x_1809_, v___x_1810_);
lean_dec_ref(v___x_1809_);
if (v___x_1811_ == 0)
{
lean_dec_ref(v_arg_1802_);
lean_dec_ref(v_arg_1799_);
lean_dec_ref(v_arg_1796_);
lean_dec_ref(v_e_1777_);
goto v___jp_1786_;
}
else
{
lean_object* v___x_1812_; 
v___x_1812_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_1802_, v_a_1782_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v_a_1813_; uint8_t v___x_1814_; 
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
lean_inc(v_a_1813_);
lean_dec_ref_known(v___x_1812_, 1);
v___x_1814_ = lean_unbox(v_a_1813_);
lean_dec(v_a_1813_);
if (v___x_1814_ == 0)
{
lean_dec_ref(v_arg_1799_);
lean_dec_ref(v_arg_1796_);
if (v_report_1778_ == 0)
{
lean_dec_ref(v_e_1777_);
goto v___jp_1789_;
}
else
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1815_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4);
v___x_1816_ = l_Lean_indentExpr(v_e_1777_);
v___x_1817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1815_);
lean_ctor_set(v___x_1817_, 1, v___x_1816_);
v___x_1818_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1779_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v_a_1819_; uint8_t v_verbose_1820_; 
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
lean_inc(v_a_1819_);
lean_dec_ref_known(v___x_1818_, 1);
v_verbose_1820_ = lean_ctor_get_uint8(v_a_1819_, 0);
lean_dec(v_a_1819_);
if (v_verbose_1820_ == 0)
{
lean_dec_ref_known(v___x_1817_, 2);
goto v___jp_1789_;
}
else
{
lean_object* v___x_1821_; 
v___x_1821_ = l_Lean_Meta_Sym_reportIssue(v___x_1817_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_dec_ref_known(v___x_1821_, 1);
goto v___jp_1789_;
}
else
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1829_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1824_ = v___x_1821_;
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1821_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1822_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
}
}
else
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1837_; 
lean_dec_ref_known(v___x_1817_, 2);
v_a_1830_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1832_ = v___x_1818_;
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1818_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1835_; 
if (v_isShared_1833_ == 0)
{
v___x_1835_ = v___x_1832_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_a_1830_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
}
}
}
else
{
lean_object* v___x_1838_; 
lean_dec_ref(v_e_1777_);
v___x_1838_ = l_Lean_Meta_getIntValue_x3f(v_arg_1799_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1859_; 
v_a_1839_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1841_ = v___x_1838_;
v_isShared_1842_ = v_isSharedCheck_1859_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1838_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1859_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
if (lean_obj_tag(v_a_1839_) == 1)
{
lean_object* v_val_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1854_; 
v_val_1843_ = lean_ctor_get(v_a_1839_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v_a_1839_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1845_ = v_a_1839_;
v_isShared_1846_ = v_isSharedCheck_1854_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_val_1843_);
lean_dec(v_a_1839_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1854_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1847_; lean_object* v___x_1849_; 
v___x_1847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1847_, 0, v_val_1843_);
lean_ctor_set(v___x_1847_, 1, v_arg_1796_);
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 0, v___x_1847_);
v___x_1849_ = v___x_1845_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1847_);
v___x_1849_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
lean_object* v___x_1851_; 
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 0, v___x_1849_);
v___x_1851_ = v___x_1841_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v___x_1849_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
}
}
else
{
lean_object* v___x_1855_; lean_object* v___x_1857_; 
lean_dec(v_a_1839_);
lean_dec_ref(v_arg_1796_);
v___x_1855_ = lean_box(0);
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 0, v___x_1855_);
v___x_1857_ = v___x_1841_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1855_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
else
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
lean_dec_ref(v_arg_1796_);
v_a_1860_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1838_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1838_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1865_; 
if (v_isShared_1863_ == 0)
{
v___x_1865_ = v___x_1862_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_a_1860_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
}
}
else
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1875_; 
lean_dec_ref(v_arg_1799_);
lean_dec_ref(v_arg_1796_);
lean_dec_ref(v_e_1777_);
v_a_1868_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1870_ = v___x_1812_;
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1812_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1875_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1873_; 
if (v_isShared_1871_ == 0)
{
v___x_1873_ = v___x_1870_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_a_1868_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1883_; 
lean_dec_ref(v_e_1777_);
v_a_1876_ = lean_ctor_get(v___x_1792_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1792_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1878_ = v___x_1792_;
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1792_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1879_ == 0)
{
v___x_1881_ = v___x_1878_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_a_1876_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
v___jp_1786_:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1787_ = lean_box(0);
v___x_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1787_);
return v___x_1788_;
}
v___jp_1789_:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1790_ = lean_box(0);
v___x_1791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1790_);
return v___x_1791_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1777_ = stack[0].m_obj;
uint8_t v_report_1778_ = stack[1].m_num;
lean_object* v_a_1779_ = stack[2].m_obj;
lean_object* v_a_1780_ = stack[3].m_obj;
lean_object* v_a_1781_ = stack[4].m_obj;
lean_object* v_a_1782_ = stack[5].m_obj;
lean_object* v_a_1783_ = stack[6].m_obj;
lean_object* v_a_1784_ = stack[7].m_obj;
lean_object* v_res_1884_;
v_res_1884_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1777_, v_report_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_);
stack->m_obj
 = v_res_1884_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg___boxed(lean_object* v_e_1885_, lean_object* v_report_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_){
_start:
{
uint8_t v_report_boxed_1894_; lean_object* v_res_1895_; 
v_report_boxed_1894_ = lean_unbox(v_report_1886_);
v_res_1895_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1885_, v_report_boxed_1894_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_);
lean_dec(v_a_1892_);
lean_dec_ref(v_a_1891_);
lean_dec(v_a_1890_);
lean_dec_ref(v_a_1889_);
lean_dec(v_a_1888_);
lean_dec_ref(v_a_1887_);
return v_res_1895_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f(lean_object* v_e_1896_, uint8_t v_report_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_){
_start:
{
lean_object* v___x_1909_; 
v___x_1909_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1896_, v_report_1897_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
return v___x_1909_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1896_ = stack[0].m_obj;
uint8_t v_report_1897_ = stack[1].m_num;
lean_object* v_a_1898_ = stack[2].m_obj;
lean_object* v_a_1899_ = stack[3].m_obj;
lean_object* v_a_1900_ = stack[4].m_obj;
lean_object* v_a_1901_ = stack[5].m_obj;
lean_object* v_a_1902_ = stack[6].m_obj;
lean_object* v_a_1903_ = stack[7].m_obj;
lean_object* v_a_1904_ = stack[8].m_obj;
lean_object* v_a_1905_ = stack[9].m_obj;
lean_object* v_a_1906_ = stack[10].m_obj;
lean_object* v_a_1907_ = stack[11].m_obj;
lean_object* v_res_1910_;
v_res_1910_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f(v_e_1896_, v_report_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
stack->m_obj
 = v_res_1910_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___boxed(lean_object* v_e_1911_, lean_object* v_report_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_){
_start:
{
uint8_t v_report_boxed_1924_; lean_object* v_res_1925_; 
v_report_boxed_1924_ = lean_unbox(v_report_1912_);
v_res_1925_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f(v_e_1911_, v_report_boxed_1924_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_);
lean_dec(v_a_1922_);
lean_dec_ref(v_a_1921_);
lean_dec(v_a_1920_);
lean_dec_ref(v_a_1919_);
lean_dec(v_a_1918_);
lean_dec_ref(v_a_1917_);
lean_dec(v_a_1916_);
lean_dec_ref(v_a_1915_);
lean_dec(v_a_1914_);
lean_dec(v_a_1913_);
return v_res_1925_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(lean_object* v_e_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_){
_start:
{
uint8_t v___x_1934_; lean_object* v___x_1935_; 
v___x_1934_ = 0;
v___x_1935_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1926_, v___x_1934_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1949_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1938_ = v___x_1935_;
v_isShared_1939_ = v_isSharedCheck_1949_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1935_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1949_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
if (lean_obj_tag(v_a_1936_) == 0)
{
lean_object* v___x_1940_; lean_object* v___x_1942_; 
v___x_1940_ = lean_box(v___x_1934_);
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 0, v___x_1940_);
v___x_1942_ = v___x_1938_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v___x_1940_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
else
{
uint8_t v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1947_; 
lean_dec_ref_known(v_a_1936_, 1);
v___x_1944_ = 1;
v___x_1945_ = lean_box(v___x_1944_);
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 0, v___x_1945_);
v___x_1947_ = v___x_1938_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1945_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
else
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
v_a_1950_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1952_ = v___x_1935_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1935_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1950_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1926_ = stack[0].m_obj;
lean_object* v_a_1927_ = stack[1].m_obj;
lean_object* v_a_1928_ = stack[2].m_obj;
lean_object* v_a_1929_ = stack[3].m_obj;
lean_object* v_a_1930_ = stack[4].m_obj;
lean_object* v_a_1931_ = stack[5].m_obj;
lean_object* v_a_1932_ = stack[6].m_obj;
lean_object* v_res_1958_;
v_res_1958_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(v_e_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_);
stack->m_obj
 = v_res_1958_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg___boxed(lean_object* v_e_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(v_e_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_);
lean_dec(v_a_1965_);
lean_dec_ref(v_a_1964_);
lean_dec(v_a_1963_);
lean_dec_ref(v_a_1962_);
lean_dec(v_a_1961_);
lean_dec_ref(v_a_1960_);
return v_res_1967_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul(lean_object* v_e_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_){
_start:
{
lean_object* v___x_1980_; 
v___x_1980_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(v_e_1968_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_);
return v___x_1980_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_isMul_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1968_ = stack[0].m_obj;
lean_object* v_a_1969_ = stack[1].m_obj;
lean_object* v_a_1970_ = stack[2].m_obj;
lean_object* v_a_1971_ = stack[3].m_obj;
lean_object* v_a_1972_ = stack[4].m_obj;
lean_object* v_a_1973_ = stack[5].m_obj;
lean_object* v_a_1974_ = stack[6].m_obj;
lean_object* v_a_1975_ = stack[7].m_obj;
lean_object* v_a_1976_ = stack[8].m_obj;
lean_object* v_a_1977_ = stack[9].m_obj;
lean_object* v_a_1978_ = stack[10].m_obj;
lean_object* v_res_1981_;
v_res_1981_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul(v_e_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_);
stack->m_obj
 = v_res_1981_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___boxed(lean_object* v_e_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul(v_e_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_);
lean_dec(v_a_1992_);
lean_dec_ref(v_a_1991_);
lean_dec(v_a_1990_);
lean_dec_ref(v_a_1989_);
lean_dec(v_a_1988_);
lean_dec_ref(v_a_1987_);
lean_dec(v_a_1986_);
lean_dec_ref(v_a_1985_);
lean_dec(v_a_1984_);
lean_dec(v_a_1983_);
return v_res_1994_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0(void){
_start:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1995_ = lean_unsigned_to_nat(1u);
v___x_1996_ = lean_nat_to_int(v___x_1995_);
return v___x_1996_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2(void){
_start:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1998_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__1));
v___x_1999_ = l_Lean_stringToMessageData(v___x_1998_);
return v___x_1999_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4(void){
_start:
{
lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_2001_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__3));
v___x_2002_ = l_Lean_stringToMessageData(v___x_2001_);
return v___x_2002_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(lean_object* v_e_2003_, lean_object* v_p_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_){
_start:
{
lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v___y_2021_; lean_object* v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; lean_object* v___y_2025_; lean_object* v___y_2026_; uint8_t v___x_2046_; lean_object* v___x_2047_; 
v___x_2046_ = 1;
lean_inc_ref(v_e_2003_);
v___x_2047_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_2003_, v___x_2046_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_a_2048_; 
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_a_2048_);
lean_dec_ref_known(v___x_2047_, 1);
if (lean_obj_tag(v_a_2048_) == 1)
{
lean_object* v_val_2049_; lean_object* v_fst_2050_; lean_object* v_snd_2051_; lean_object* v___x_2052_; 
lean_dec_ref(v_e_2003_);
v_val_2049_ = lean_ctor_get(v_a_2048_, 0);
lean_inc(v_val_2049_);
lean_dec_ref_known(v_a_2048_, 1);
v_fst_2050_ = lean_ctor_get(v_val_2049_, 0);
lean_inc(v_fst_2050_);
v_snd_2051_ = lean_ctor_get(v_val_2049_, 1);
lean_inc(v_snd_2051_);
lean_dec(v_val_2049_);
lean_inc(v_a_2014_);
lean_inc_ref(v_a_2013_);
lean_inc(v_a_2012_);
lean_inc_ref(v_a_2011_);
lean_inc(v_a_2010_);
lean_inc_ref(v_a_2009_);
lean_inc(v_a_2008_);
lean_inc_ref(v_a_2007_);
lean_inc(v_a_2006_);
lean_inc(v_a_2005_);
v___x_2052_ = lean_grind_cutsat_mk_var(v_snd_2051_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2061_; 
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2055_ = v___x_2052_;
v_isShared_2056_ = v_isSharedCheck_2061_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_2052_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2061_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2057_; lean_object* v___x_2059_; 
v___x_2057_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2057_, 0, v_fst_2050_);
lean_ctor_set(v___x_2057_, 1, v_a_2053_);
lean_ctor_set(v___x_2057_, 2, v_p_2004_);
if (v_isShared_2056_ == 0)
{
lean_ctor_set(v___x_2055_, 0, v___x_2057_);
v___x_2059_ = v___x_2055_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_2057_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
else
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2069_; 
lean_dec(v_fst_2050_);
lean_dec_ref(v_p_2004_);
v_a_2062_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2064_ = v___x_2052_;
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2052_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2067_; 
if (v_isShared_2065_ == 0)
{
v___x_2067_ = v___x_2064_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2062_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
else
{
lean_object* v___x_2070_; 
lean_dec(v_a_2048_);
lean_inc_ref(v_e_2003_);
v___x_2070_ = l_Lean_Meta_getIntValue_x3f(v_e_2003_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2112_; 
v_a_2071_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2073_ = v___x_2070_;
v_isShared_2074_ = v_isSharedCheck_2112_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2070_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2112_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
if (lean_obj_tag(v_a_2071_) == 1)
{
lean_object* v_val_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2111_; 
v_val_2075_ = lean_ctor_get(v_a_2071_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v_a_2071_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2077_ = v_a_2071_;
v_isShared_2078_ = v_isSharedCheck_2111_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_val_2075_);
lean_dec(v_a_2071_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2111_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
uint8_t v___x_2079_; 
v___x_2079_ = l_Int_Internal_Linear_Poly_isZero(v_p_2004_);
if (v___x_2079_ == 0)
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
lean_del_object(v___x_2077_);
lean_dec(v_val_2075_);
lean_del_object(v___x_2073_);
v___x_2080_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2);
lean_inc_ref(v_e_2003_);
v___x_2081_ = l_Lean_indentExpr(v_e_2003_);
v___x_2082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2080_);
lean_ctor_set(v___x_2082_, 1, v___x_2081_);
v___x_2083_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4);
v___x_2084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2082_);
lean_ctor_set(v___x_2084_, 1, v___x_2083_);
v___x_2085_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_2009_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; uint8_t v_verbose_2087_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
lean_inc(v_a_2086_);
lean_dec_ref_known(v___x_2085_, 1);
v_verbose_2087_ = lean_ctor_get_uint8(v_a_2086_, 0);
lean_dec(v_a_2086_);
if (v_verbose_2087_ == 0)
{
lean_dec_ref_known(v___x_2084_, 2);
v___y_2017_ = v_a_2005_;
v___y_2018_ = v_a_2006_;
v___y_2019_ = v_a_2007_;
v___y_2020_ = v_a_2008_;
v___y_2021_ = v_a_2009_;
v___y_2022_ = v_a_2010_;
v___y_2023_ = v_a_2011_;
v___y_2024_ = v_a_2012_;
v___y_2025_ = v_a_2013_;
v___y_2026_ = v_a_2014_;
goto v___jp_2016_;
}
else
{
lean_object* v___x_2088_; 
v___x_2088_ = l_Lean_Meta_Sym_reportIssue(v___x_2084_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_dec_ref_known(v___x_2088_, 1);
v___y_2017_ = v_a_2005_;
v___y_2018_ = v_a_2006_;
v___y_2019_ = v_a_2007_;
v___y_2020_ = v_a_2008_;
v___y_2021_ = v_a_2009_;
v___y_2022_ = v_a_2010_;
v___y_2023_ = v_a_2011_;
v___y_2024_ = v_a_2012_;
v___y_2025_ = v_a_2013_;
v___y_2026_ = v_a_2014_;
goto v___jp_2016_;
}
else
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
lean_dec_ref(v_p_2004_);
lean_dec_ref(v_e_2003_);
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2088_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2088_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
}
else
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
lean_dec_ref_known(v___x_2084_, 2);
lean_dec_ref(v_p_2004_);
lean_dec_ref(v_e_2003_);
v_a_2097_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2099_ = v___x_2085_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2085_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2097_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
else
{
lean_object* v___x_2106_; 
lean_dec_ref(v_p_2004_);
lean_dec_ref(v_e_2003_);
if (v_isShared_2078_ == 0)
{
lean_ctor_set_tag(v___x_2077_, 0);
v___x_2106_ = v___x_2077_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_val_2075_);
v___x_2106_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
lean_object* v___x_2108_; 
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 0, v___x_2106_);
v___x_2108_ = v___x_2073_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2106_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
}
}
else
{
lean_del_object(v___x_2073_);
lean_dec(v_a_2071_);
v___y_2017_ = v_a_2005_;
v___y_2018_ = v_a_2006_;
v___y_2019_ = v_a_2007_;
v___y_2020_ = v_a_2008_;
v___y_2021_ = v_a_2009_;
v___y_2022_ = v_a_2010_;
v___y_2023_ = v_a_2011_;
v___y_2024_ = v_a_2012_;
v___y_2025_ = v_a_2013_;
v___y_2026_ = v_a_2014_;
goto v___jp_2016_;
}
}
}
else
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2120_; 
lean_dec_ref(v_p_2004_);
lean_dec_ref(v_e_2003_);
v_a_2113_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2115_ = v___x_2070_;
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2070_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2118_; 
if (v_isShared_2116_ == 0)
{
v___x_2118_ = v___x_2115_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_a_2113_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
}
}
else
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2128_; 
lean_dec_ref(v_p_2004_);
lean_dec_ref(v_e_2003_);
v_a_2121_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2123_ = v___x_2047_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2047_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2124_ == 0)
{
v___x_2126_ = v___x_2123_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2121_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
v___jp_2016_:
{
lean_object* v___x_2027_; 
lean_inc(v___y_2026_);
lean_inc_ref(v___y_2025_);
lean_inc(v___y_2024_);
lean_inc_ref(v___y_2023_);
lean_inc(v___y_2022_);
lean_inc_ref(v___y_2021_);
lean_inc(v___y_2020_);
lean_inc_ref(v___y_2019_);
lean_inc(v___y_2018_);
lean_inc(v___y_2017_);
v___x_2027_ = lean_grind_cutsat_mk_var(v_e_2003_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2037_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2030_ = v___x_2027_;
v_isShared_2031_ = v_isSharedCheck_2037_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2027_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2037_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2035_; 
v___x_2032_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0);
v___x_2033_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2032_);
lean_ctor_set(v___x_2033_, 1, v_a_2028_);
lean_ctor_set(v___x_2033_, 2, v_p_2004_);
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 0, v___x_2033_);
v___x_2035_ = v___x_2030_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_2033_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
else
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
lean_dec_ref(v_p_2004_);
v_a_2038_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_2027_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2027_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_addMonomial_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2003_ = stack[0].m_obj;
lean_object* v_p_2004_ = stack[1].m_obj;
lean_object* v_a_2005_ = stack[2].m_obj;
lean_object* v_a_2006_ = stack[3].m_obj;
lean_object* v_a_2007_ = stack[4].m_obj;
lean_object* v_a_2008_ = stack[5].m_obj;
lean_object* v_a_2009_ = stack[6].m_obj;
lean_object* v_a_2010_ = stack[7].m_obj;
lean_object* v_a_2011_ = stack[8].m_obj;
lean_object* v_a_2012_ = stack[9].m_obj;
lean_object* v_a_2013_ = stack[10].m_obj;
lean_object* v_a_2014_ = stack[11].m_obj;
lean_object* v_res_2129_;
v_res_2129_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_e_2003_, v_p_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
stack->m_obj
 = v_res_2129_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___boxed(lean_object* v_e_2130_, lean_object* v_p_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_){
_start:
{
lean_object* v_res_2143_; 
v_res_2143_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_e_2130_, v_p_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
lean_dec(v_a_2141_);
lean_dec_ref(v_a_2140_);
lean_dec(v_a_2139_);
lean_dec_ref(v_a_2138_);
lean_dec(v_a_2137_);
lean_dec_ref(v_a_2136_);
lean_dec(v_a_2135_);
lean_dec_ref(v_a_2134_);
lean_dec(v_a_2133_);
lean_dec(v_a_2132_);
return v_res_2143_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go(lean_object* v_e_2144_, lean_object* v_p_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_){
_start:
{
uint8_t v___x_2157_; lean_object* v___x_2158_; 
v___x_2157_ = 1;
lean_inc_ref(v_e_2144_);
v___x_2158_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_2144_, v___x_2157_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_);
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_object* v_a_2159_; 
v_a_2159_ = lean_ctor_get(v___x_2158_, 0);
lean_inc(v_a_2159_);
lean_dec_ref_known(v___x_2158_, 1);
if (lean_obj_tag(v_a_2159_) == 1)
{
lean_object* v_val_2160_; lean_object* v_fst_2161_; lean_object* v_snd_2162_; lean_object* v___x_2163_; 
lean_dec_ref(v_e_2144_);
v_val_2160_ = lean_ctor_get(v_a_2159_, 0);
lean_inc(v_val_2160_);
lean_dec_ref_known(v_a_2159_, 1);
v_fst_2161_ = lean_ctor_get(v_val_2160_, 0);
lean_inc(v_fst_2161_);
v_snd_2162_ = lean_ctor_get(v_val_2160_, 1);
lean_inc(v_snd_2162_);
lean_dec(v_val_2160_);
v___x_2163_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_snd_2162_, v_p_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
lean_inc(v_a_2164_);
lean_dec_ref_known(v___x_2163_, 1);
v_e_2144_ = v_fst_2161_;
v_p_2145_ = v_a_2164_;
goto _start;
}
else
{
lean_dec(v_fst_2161_);
return v___x_2163_;
}
}
else
{
lean_object* v___x_2166_; 
lean_dec(v_a_2159_);
v___x_2166_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_e_2144_, v_p_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_);
return v___x_2166_;
}
}
else
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2174_; 
lean_dec_ref(v_p_2145_);
lean_dec_ref(v_e_2144_);
v_a_2167_ = lean_ctor_get(v___x_2158_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2169_ = v___x_2158_;
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2158_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2172_; 
if (v_isShared_2170_ == 0)
{
v___x_2172_ = v___x_2169_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_a_2167_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2144_ = stack[0].m_obj;
lean_object* v_p_2145_ = stack[1].m_obj;
lean_object* v_a_2146_ = stack[2].m_obj;
lean_object* v_a_2147_ = stack[3].m_obj;
lean_object* v_a_2148_ = stack[4].m_obj;
lean_object* v_a_2149_ = stack[5].m_obj;
lean_object* v_a_2150_ = stack[6].m_obj;
lean_object* v_a_2151_ = stack[7].m_obj;
lean_object* v_a_2152_ = stack[8].m_obj;
lean_object* v_a_2153_ = stack[9].m_obj;
lean_object* v_a_2154_ = stack[10].m_obj;
lean_object* v_a_2155_ = stack[11].m_obj;
lean_object* v_res_2175_;
v_res_2175_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go(v_e_2144_, v_p_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_);
stack->m_obj
 = v_res_2175_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go___boxed(lean_object* v_e_2176_, lean_object* v_p_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go(v_e_2176_, v_p_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_);
lean_dec(v_a_2187_);
lean_dec_ref(v_a_2186_);
lean_dec(v_a_2185_);
lean_dec_ref(v_a_2184_);
lean_dec(v_a_2183_);
lean_dec_ref(v_a_2182_);
lean_dec(v_a_2181_);
lean_dec_ref(v_a_2180_);
lean_dec(v_a_2179_);
lean_dec(v_a_2178_);
return v_res_2189_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0(void){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2190_ = lean_unsigned_to_nat(0u);
v___x_2191_ = lean_nat_to_int(v___x_2190_);
return v___x_2191_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1(void){
_start:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2192_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0);
v___x_2193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2192_);
return v___x_2193_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly(lean_object* v_e_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_){
_start:
{
uint8_t v___x_2206_; lean_object* v___x_2207_; 
v___x_2206_ = 1;
lean_inc_ref(v_e_2194_);
v___x_2207_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_2194_, v___x_2206_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_object* v_a_2208_; 
v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
lean_inc(v_a_2208_);
lean_dec_ref_known(v___x_2207_, 1);
if (lean_obj_tag(v_a_2208_) == 1)
{
lean_object* v_val_2209_; lean_object* v_fst_2210_; lean_object* v_snd_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
lean_dec_ref(v_e_2194_);
v_val_2209_ = lean_ctor_get(v_a_2208_, 0);
lean_inc(v_val_2209_);
lean_dec_ref_known(v_a_2208_, 1);
v_fst_2210_ = lean_ctor_get(v_val_2209_, 0);
lean_inc(v_fst_2210_);
v_snd_2211_ = lean_ctor_get(v_val_2209_, 1);
lean_inc(v_snd_2211_);
lean_dec(v_val_2209_);
v___x_2212_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1);
v___x_2213_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_snd_2211_, v___x_2212_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_);
if (lean_obj_tag(v___x_2213_) == 0)
{
lean_object* v_a_2214_; lean_object* v___x_2215_; 
v_a_2214_ = lean_ctor_get(v___x_2213_, 0);
lean_inc(v_a_2214_);
lean_dec_ref_known(v___x_2213_, 1);
v___x_2215_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go(v_fst_2210_, v_a_2214_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_);
return v___x_2215_;
}
else
{
lean_dec(v_fst_2210_);
return v___x_2213_;
}
}
else
{
lean_object* v___x_2216_; lean_object* v___x_2217_; 
lean_dec(v_a_2208_);
v___x_2216_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1);
v___x_2217_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_e_2194_, v___x_2216_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_);
return v___x_2217_;
}
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_dec_ref(v_e_2194_);
v_a_2218_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2207_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2207_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_toPoly_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2194_ = stack[0].m_obj;
lean_object* v_a_2195_ = stack[1].m_obj;
lean_object* v_a_2196_ = stack[2].m_obj;
lean_object* v_a_2197_ = stack[3].m_obj;
lean_object* v_a_2198_ = stack[4].m_obj;
lean_object* v_a_2199_ = stack[5].m_obj;
lean_object* v_a_2200_ = stack[6].m_obj;
lean_object* v_a_2201_ = stack[7].m_obj;
lean_object* v_a_2202_ = stack[8].m_obj;
lean_object* v_a_2203_ = stack[9].m_obj;
lean_object* v_a_2204_ = stack[10].m_obj;
lean_object* v_res_2226_;
v_res_2226_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_e_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_);
stack->m_obj
 = v_res_2226_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly___boxed(lean_object* v_e_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_e_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_);
lean_dec(v_a_2237_);
lean_dec_ref(v_a_2236_);
lean_dec(v_a_2235_);
lean_dec_ref(v_a_2234_);
lean_dec(v_a_2233_);
lean_dec_ref(v_a_2232_);
lean_dec(v_a_2231_);
lean_dec_ref(v_a_2230_);
lean_dec(v_a_2229_);
lean_dec(v_a_2228_);
return v_res_2239_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_IntInstTesters(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_IntInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(uint8_t builtin);
lean_object* initialize_Lean_Meta_IntInstTesters(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_IntInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(builtin);
}
#ifdef __cplusplus
}
#endif
