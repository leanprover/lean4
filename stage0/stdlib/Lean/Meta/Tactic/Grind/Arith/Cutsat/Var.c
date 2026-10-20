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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNonlinearTerm___boxed(lean_object* v_y_14_, lean_object* v_x_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_00___x40___internal___hyg_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = lean_cutsat_propagate_nonlinear(v_y_14_, v_x_15_, v_a_16_, v_a_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm(lean_object* v_e_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_48_, v_a_50_);
if (lean_obj_tag(v___x_58_) == 0)
{
lean_object* v_a_59_; lean_object* v___x_60_; uint8_t v___x_61_; 
v_a_59_ = lean_ctor_get(v___x_58_, 0);
lean_inc(v_a_59_);
lean_dec_ref_known(v___x_58_, 1);
v___x_60_ = l_Lean_Expr_cleanupAnnotations(v_a_59_);
v___x_61_ = l_Lean_Expr_isApp(v___x_60_);
if (v___x_61_ == 0)
{
lean_dec_ref(v___x_60_);
goto v___jp_54_;
}
else
{
lean_object* v_arg_62_; lean_object* v___x_63_; uint8_t v___x_64_; 
v_arg_62_ = lean_ctor_get(v___x_60_, 1);
lean_inc_ref(v_arg_62_);
v___x_63_ = l_Lean_Expr_appFnCleanup___redArg(v___x_60_);
v___x_64_ = l_Lean_Expr_isApp(v___x_63_);
if (v___x_64_ == 0)
{
lean_dec_ref(v___x_63_);
lean_dec_ref(v_arg_62_);
goto v___jp_54_;
}
else
{
lean_object* v_arg_65_; lean_object* v___x_66_; uint8_t v___x_67_; 
v_arg_65_ = lean_ctor_get(v___x_63_, 1);
lean_inc_ref(v_arg_65_);
v___x_66_ = l_Lean_Expr_appFnCleanup___redArg(v___x_63_);
v___x_67_ = l_Lean_Expr_isApp(v___x_66_);
if (v___x_67_ == 0)
{
lean_dec_ref(v___x_66_);
lean_dec_ref(v_arg_65_);
lean_dec_ref(v_arg_62_);
goto v___jp_54_;
}
else
{
lean_object* v_arg_68_; lean_object* v___x_69_; uint8_t v___x_70_; 
v_arg_68_ = lean_ctor_get(v___x_66_, 1);
lean_inc_ref(v_arg_68_);
v___x_69_ = l_Lean_Expr_appFnCleanup___redArg(v___x_66_);
v___x_70_ = l_Lean_Expr_isApp(v___x_69_);
if (v___x_70_ == 0)
{
lean_dec_ref(v___x_69_);
lean_dec_ref(v_arg_68_);
lean_dec_ref(v_arg_65_);
lean_dec_ref(v_arg_62_);
goto v___jp_54_;
}
else
{
lean_object* v___x_71_; uint8_t v___x_72_; 
v___x_71_ = l_Lean_Expr_appFnCleanup___redArg(v___x_69_);
v___x_72_ = l_Lean_Expr_isApp(v___x_71_);
if (v___x_72_ == 0)
{
lean_dec_ref(v___x_71_);
lean_dec_ref(v_arg_68_);
lean_dec_ref(v_arg_65_);
lean_dec_ref(v_arg_62_);
goto v___jp_54_;
}
else
{
lean_object* v___x_73_; uint8_t v___x_74_; 
v___x_73_ = l_Lean_Expr_appFnCleanup___redArg(v___x_71_);
v___x_74_ = l_Lean_Expr_isApp(v___x_73_);
if (v___x_74_ == 0)
{
lean_dec_ref(v___x_73_);
lean_dec_ref(v_arg_68_);
lean_dec_ref(v_arg_65_);
lean_dec_ref(v_arg_62_);
goto v___jp_54_;
}
else
{
lean_object* v___x_75_; lean_object* v___x_76_; uint8_t v___x_77_; 
v___x_75_ = l_Lean_Expr_appFnCleanup___redArg(v___x_73_);
v___x_76_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__2));
v___x_77_ = l_Lean_Expr_isConstOf(v___x_75_, v___x_76_);
if (v___x_77_ == 0)
{
lean_object* v___x_78_; uint8_t v___x_79_; 
lean_dec_ref(v_arg_65_);
v___x_78_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__5));
v___x_79_ = l_Lean_Expr_isConstOf(v___x_75_, v___x_78_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; uint8_t v___x_81_; 
v___x_80_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__8));
v___x_81_ = l_Lean_Expr_isConstOf(v___x_75_, v___x_80_);
if (v___x_81_ == 0)
{
lean_object* v___x_82_; uint8_t v___x_83_; 
lean_dec_ref(v_arg_62_);
v___x_82_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11));
v___x_83_ = l_Lean_Expr_isConstOf(v___x_75_, v___x_82_);
lean_dec_ref(v___x_75_);
if (v___x_83_ == 0)
{
lean_dec_ref(v_arg_68_);
goto v___jp_54_;
}
else
{
lean_object* v___x_84_; 
v___x_84_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_68_, v_a_50_);
return v___x_84_;
}
}
else
{
lean_object* v___x_85_; 
lean_dec_ref(v___x_75_);
v___x_85_ = l_Lean_Meta_getIntValue_x3f(v_arg_62_, v_a_49_, v_a_50_, v_a_51_, v_a_52_);
if (lean_obj_tag(v___x_85_) == 0)
{
lean_object* v_a_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_95_; 
v_a_86_ = lean_ctor_get(v___x_85_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_95_ == 0)
{
v___x_88_ = v___x_85_;
v_isShared_89_ = v_isSharedCheck_95_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_a_86_);
lean_dec(v___x_85_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_95_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
if (lean_obj_tag(v_a_86_) == 0)
{
lean_object* v___x_90_; 
lean_del_object(v___x_88_);
v___x_90_ = l_Lean_Meta_Structural_isInstHDivInt___redArg(v_arg_68_, v_a_50_);
return v___x_90_;
}
else
{
lean_object* v___x_91_; lean_object* v___x_93_; 
lean_dec_ref_known(v_a_86_, 1);
lean_dec_ref(v_arg_68_);
v___x_91_ = lean_box(v___x_79_);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 0, v___x_91_);
v___x_93_ = v___x_88_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v___x_91_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
}
else
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_103_; 
lean_dec_ref(v_arg_68_);
v_a_96_ = lean_ctor_get(v___x_85_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_103_ == 0)
{
v___x_98_ = v___x_85_;
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___x_85_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_101_; 
if (v_isShared_99_ == 0)
{
v___x_101_ = v___x_98_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_a_96_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
}
}
else
{
lean_object* v___x_104_; 
lean_dec_ref(v___x_75_);
v___x_104_ = l_Lean_Meta_getIntValue_x3f(v_arg_62_, v_a_49_, v_a_50_, v_a_51_, v_a_52_);
if (lean_obj_tag(v___x_104_) == 0)
{
lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_114_; 
v_a_105_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_114_ == 0)
{
v___x_107_ = v___x_104_;
v_isShared_108_ = v_isSharedCheck_114_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_dec(v___x_104_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_114_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
if (lean_obj_tag(v_a_105_) == 0)
{
lean_object* v___x_109_; 
lean_del_object(v___x_107_);
v___x_109_ = l_Lean_Meta_Structural_isInstHModInt___redArg(v_arg_68_, v_a_50_);
return v___x_109_;
}
else
{
lean_object* v___x_110_; lean_object* v___x_112_; 
lean_dec_ref_known(v_a_105_, 1);
lean_dec_ref(v_arg_68_);
v___x_110_ = lean_box(v___x_77_);
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 0, v___x_110_);
v___x_112_ = v___x_107_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_110_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
}
else
{
lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_122_; 
lean_dec_ref(v_arg_68_);
v_a_115_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_122_ == 0)
{
v___x_117_ = v___x_104_;
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_dec(v___x_104_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_120_; 
if (v_isShared_118_ == 0)
{
v___x_120_ = v___x_117_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_a_115_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
}
}
else
{
lean_object* v___x_123_; 
lean_dec_ref(v___x_75_);
v___x_123_ = l_Lean_Meta_Structural_isInstHPowInt___redArg(v_arg_68_, v_a_50_);
if (lean_obj_tag(v___x_123_) == 0)
{
lean_object* v_a_124_; uint8_t v___x_125_; 
v_a_124_ = lean_ctor_get(v___x_123_, 0);
v___x_125_ = lean_unbox(v_a_124_);
if (v___x_125_ == 0)
{
lean_dec_ref(v_arg_65_);
lean_dec_ref(v_arg_62_);
return v___x_123_;
}
else
{
lean_object* v___x_126_; 
lean_inc(v_a_124_);
lean_dec_ref_known(v___x_123_, 1);
v___x_126_ = l_Lean_Meta_getIntValue_x3f(v_arg_65_, v_a_49_, v_a_50_, v_a_51_, v_a_52_);
if (lean_obj_tag(v___x_126_) == 0)
{
lean_object* v_a_127_; lean_object* v___x_128_; 
v_a_127_ = lean_ctor_get(v___x_126_, 0);
lean_inc(v_a_127_);
lean_dec_ref_known(v___x_126_, 1);
v___x_128_ = l_Lean_Meta_getIntValue_x3f(v_arg_62_, v_a_49_, v_a_50_, v_a_51_, v_a_52_);
if (lean_obj_tag(v___x_128_) == 0)
{
if (lean_obj_tag(v_a_127_) == 0)
{
lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_136_; 
lean_dec(v_a_124_);
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_136_ == 0)
{
lean_object* v_unused_137_; 
v_unused_137_ = lean_ctor_get(v___x_128_, 0);
lean_dec(v_unused_137_);
v___x_130_ = v___x_128_;
v_isShared_131_ = v_isSharedCheck_136_;
goto v_resetjp_129_;
}
else
{
lean_dec(v___x_128_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_136_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_132_; lean_object* v___x_134_; 
v___x_132_ = lean_box(v___x_77_);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 0, v___x_132_);
v___x_134_ = v___x_130_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_132_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
else
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_150_; 
lean_dec_ref_known(v_a_127_, 1);
v_a_138_ = lean_ctor_get(v___x_128_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_150_ == 0)
{
v___x_140_ = v___x_128_;
v_isShared_141_ = v_isSharedCheck_150_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_128_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_150_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
if (lean_obj_tag(v_a_138_) == 0)
{
lean_object* v___x_143_; 
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 0, v_a_124_);
v___x_143_ = v___x_140_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_a_124_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
else
{
uint8_t v___x_145_; lean_object* v___x_146_; lean_object* v___x_148_; 
lean_dec_ref_known(v_a_138_, 1);
lean_dec(v_a_124_);
v___x_145_ = 0;
v___x_146_ = lean_box(v___x_145_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 0, v___x_146_);
v___x_148_ = v___x_140_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v___x_146_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
}
}
else
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_158_; 
lean_dec(v_a_127_);
lean_dec(v_a_124_);
v_a_151_ = lean_ctor_get(v___x_128_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_158_ == 0)
{
v___x_153_ = v___x_128_;
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v___x_128_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_156_; 
if (v_isShared_154_ == 0)
{
v___x_156_ = v___x_153_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_a_151_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
}
else
{
lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_166_; 
lean_dec(v_a_124_);
lean_dec_ref(v_arg_62_);
v_a_159_ = lean_ctor_get(v___x_126_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_166_ == 0)
{
v___x_161_ = v___x_126_;
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_dec(v___x_126_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_164_; 
if (v_isShared_162_ == 0)
{
v___x_164_ = v___x_161_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_a_159_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
}
else
{
lean_dec_ref(v_arg_65_);
lean_dec_ref(v_arg_62_);
return v___x_123_;
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
lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_174_; 
v_a_167_ = lean_ctor_get(v___x_58_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_58_);
if (v_isSharedCheck_174_ == 0)
{
v___x_169_ = v___x_58_;
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v___x_58_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_172_; 
if (v_isShared_170_ == 0)
{
v___x_172_ = v___x_169_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_a_167_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
v___jp_54_:
{
uint8_t v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_55_ = 0;
v___x_56_ = lean_box(v___x_55_);
v___x_57_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
return v___x_57_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___boxed(lean_object* v_e_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm(v_e_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_);
lean_dec(v_a_179_);
lean_dec_ref(v_a_178_);
lean_dec(v_a_177_);
lean_dec_ref(v_a_176_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_x_182_, lean_object* v_x_183_, lean_object* v_x_184_, lean_object* v_x_185_){
_start:
{
lean_object* v_ks_186_; lean_object* v_vs_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_211_; 
v_ks_186_ = lean_ctor_get(v_x_182_, 0);
v_vs_187_ = lean_ctor_get(v_x_182_, 1);
v_isSharedCheck_211_ = !lean_is_exclusive(v_x_182_);
if (v_isSharedCheck_211_ == 0)
{
v___x_189_ = v_x_182_;
v_isShared_190_ = v_isSharedCheck_211_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_vs_187_);
lean_inc(v_ks_186_);
lean_dec(v_x_182_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_211_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_191_ = lean_array_get_size(v_ks_186_);
v___x_192_ = lean_nat_dec_lt(v_x_183_, v___x_191_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_196_; 
lean_dec(v_x_183_);
v___x_193_ = lean_array_push(v_ks_186_, v_x_184_);
v___x_194_ = lean_array_push(v_vs_187_, v_x_185_);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 1, v___x_194_);
lean_ctor_set(v___x_189_, 0, v___x_193_);
v___x_196_ = v___x_189_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_193_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v___x_194_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
else
{
lean_object* v_k_x27_198_; uint8_t v___x_199_; 
v_k_x27_198_ = lean_array_fget_borrowed(v_ks_186_, v_x_183_);
v___x_199_ = lean_nat_dec_eq(v_x_184_, v_k_x27_198_);
if (v___x_199_ == 0)
{
lean_object* v___x_201_; 
if (v_isShared_190_ == 0)
{
v___x_201_ = v___x_189_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_ks_186_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v_vs_187_);
v___x_201_ = v_reuseFailAlloc_205_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = lean_unsigned_to_nat(1u);
v___x_203_ = lean_nat_add(v_x_183_, v___x_202_);
lean_dec(v_x_183_);
v_x_182_ = v___x_201_;
v_x_183_ = v___x_203_;
goto _start;
}
}
else
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_209_; 
v___x_206_ = lean_array_fset(v_ks_186_, v_x_183_, v_x_184_);
v___x_207_ = lean_array_fset(v_vs_187_, v_x_183_, v_x_185_);
lean_dec(v_x_183_);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 1, v___x_207_);
lean_ctor_set(v___x_189_, 0, v___x_206_);
v___x_209_ = v___x_189_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_206_);
lean_ctor_set(v_reuseFailAlloc_210_, 1, v___x_207_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1___redArg(lean_object* v_n_212_, lean_object* v_k_213_, lean_object* v_v_214_){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = lean_unsigned_to_nat(0u);
v___x_216_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__4___redArg(v_n_212_, v___x_215_, v_k_213_, v_v_214_);
return v___x_216_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(lean_object* v_x_218_, size_t v_x_219_, size_t v_x_220_, lean_object* v_x_221_, lean_object* v_x_222_){
_start:
{
if (lean_obj_tag(v_x_218_) == 0)
{
lean_object* v_es_223_; size_t v___x_224_; size_t v___x_225_; lean_object* v_j_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
v_es_223_ = lean_ctor_get(v_x_218_, 0);
v___x_224_ = ((size_t)31ULL);
v___x_225_ = lean_usize_land(v_x_219_, v___x_224_);
v_j_226_ = lean_usize_to_nat(v___x_225_);
v___x_227_ = lean_array_get_size(v_es_223_);
v___x_228_ = lean_nat_dec_lt(v_j_226_, v___x_227_);
if (v___x_228_ == 0)
{
lean_dec(v_j_226_);
lean_dec(v_x_222_);
lean_dec(v_x_221_);
return v_x_218_;
}
else
{
lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_267_; 
lean_inc_ref(v_es_223_);
v_isSharedCheck_267_ = !lean_is_exclusive(v_x_218_);
if (v_isSharedCheck_267_ == 0)
{
lean_object* v_unused_268_; 
v_unused_268_ = lean_ctor_get(v_x_218_, 0);
lean_dec(v_unused_268_);
v___x_230_ = v_x_218_;
v_isShared_231_ = v_isSharedCheck_267_;
goto v_resetjp_229_;
}
else
{
lean_dec(v_x_218_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_267_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v_v_232_; lean_object* v___x_233_; lean_object* v_xs_x27_234_; lean_object* v___y_236_; 
v_v_232_ = lean_array_fget(v_es_223_, v_j_226_);
v___x_233_ = lean_box(0);
v_xs_x27_234_ = lean_array_fset(v_es_223_, v_j_226_, v___x_233_);
switch(lean_obj_tag(v_v_232_))
{
case 0:
{
lean_object* v_key_241_; lean_object* v_val_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_252_; 
v_key_241_ = lean_ctor_get(v_v_232_, 0);
v_val_242_ = lean_ctor_get(v_v_232_, 1);
v_isSharedCheck_252_ = !lean_is_exclusive(v_v_232_);
if (v_isSharedCheck_252_ == 0)
{
v___x_244_ = v_v_232_;
v_isShared_245_ = v_isSharedCheck_252_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_val_242_);
lean_inc(v_key_241_);
lean_dec(v_v_232_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_252_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
uint8_t v___x_246_; 
v___x_246_ = lean_nat_dec_eq(v_x_221_, v_key_241_);
if (v___x_246_ == 0)
{
lean_object* v___x_247_; lean_object* v___x_248_; 
lean_del_object(v___x_244_);
v___x_247_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_241_, v_val_242_, v_x_221_, v_x_222_);
v___x_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
v___y_236_ = v___x_248_;
goto v___jp_235_;
}
else
{
lean_object* v___x_250_; 
lean_dec(v_val_242_);
lean_dec(v_key_241_);
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 1, v_x_222_);
lean_ctor_set(v___x_244_, 0, v_x_221_);
v___x_250_ = v___x_244_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_x_221_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v_x_222_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
v___y_236_ = v___x_250_;
goto v___jp_235_;
}
}
}
}
case 1:
{
lean_object* v_node_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_265_; 
v_node_253_ = lean_ctor_get(v_v_232_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v_v_232_);
if (v_isSharedCheck_265_ == 0)
{
v___x_255_ = v_v_232_;
v_isShared_256_ = v_isSharedCheck_265_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_node_253_);
lean_dec(v_v_232_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_265_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
size_t v___x_257_; size_t v___x_258_; size_t v___x_259_; size_t v___x_260_; lean_object* v___x_261_; lean_object* v___x_263_; 
v___x_257_ = ((size_t)5ULL);
v___x_258_ = lean_usize_shift_right(v_x_219_, v___x_257_);
v___x_259_ = ((size_t)1ULL);
v___x_260_ = lean_usize_add(v_x_220_, v___x_259_);
v___x_261_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_node_253_, v___x_258_, v___x_260_, v_x_221_, v_x_222_);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 0, v___x_261_);
v___x_263_ = v___x_255_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_261_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
v___y_236_ = v___x_263_;
goto v___jp_235_;
}
}
}
default: 
{
lean_object* v___x_266_; 
v___x_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_266_, 0, v_x_221_);
lean_ctor_set(v___x_266_, 1, v_x_222_);
v___y_236_ = v___x_266_;
goto v___jp_235_;
}
}
v___jp_235_:
{
lean_object* v___x_237_; lean_object* v___x_239_; 
v___x_237_ = lean_array_fset(v_xs_x27_234_, v_j_226_, v___y_236_);
lean_dec(v_j_226_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 0, v___x_237_);
v___x_239_ = v___x_230_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_237_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
}
else
{
lean_object* v_ks_269_; lean_object* v_vs_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_288_; 
v_ks_269_ = lean_ctor_get(v_x_218_, 0);
v_vs_270_ = lean_ctor_get(v_x_218_, 1);
v_isSharedCheck_288_ = !lean_is_exclusive(v_x_218_);
if (v_isSharedCheck_288_ == 0)
{
v___x_272_ = v_x_218_;
v_isShared_273_ = v_isSharedCheck_288_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_vs_270_);
lean_inc(v_ks_269_);
lean_dec(v_x_218_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_288_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_275_; 
if (v_isShared_273_ == 0)
{
v___x_275_ = v___x_272_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_ks_269_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v_vs_270_);
v___x_275_ = v_reuseFailAlloc_287_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
lean_object* v_newNode_276_; size_t v___x_277_; uint8_t v___x_278_; 
v_newNode_276_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1___redArg(v___x_275_, v_x_221_, v_x_222_);
v___x_277_ = ((size_t)7ULL);
v___x_278_ = lean_usize_dec_le(v___x_277_, v_x_220_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; lean_object* v___x_280_; uint8_t v___x_281_; 
v___x_279_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_276_);
v___x_280_ = lean_unsigned_to_nat(4u);
v___x_281_ = lean_nat_dec_lt(v___x_279_, v___x_280_);
lean_dec(v___x_279_);
if (v___x_281_ == 0)
{
lean_object* v_ks_282_; lean_object* v_vs_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v_ks_282_ = lean_ctor_get(v_newNode_276_, 0);
lean_inc_ref(v_ks_282_);
v_vs_283_ = lean_ctor_get(v_newNode_276_, 1);
lean_inc_ref(v_vs_283_);
lean_dec_ref(v_newNode_276_);
v___x_284_ = lean_unsigned_to_nat(0u);
v___x_285_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0);
v___x_286_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg(v_x_220_, v_ks_282_, v_vs_283_, v___x_284_, v___x_285_);
lean_dec_ref(v_vs_283_);
lean_dec_ref(v_ks_282_);
return v___x_286_;
}
else
{
return v_newNode_276_;
}
}
else
{
return v_newNode_276_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg(size_t v_depth_289_, lean_object* v_keys_290_, lean_object* v_vals_291_, lean_object* v_i_292_, lean_object* v_entries_293_){
_start:
{
lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_294_ = lean_array_get_size(v_keys_290_);
v___x_295_ = lean_nat_dec_lt(v_i_292_, v___x_294_);
if (v___x_295_ == 0)
{
lean_dec(v_i_292_);
return v_entries_293_;
}
else
{
lean_object* v_k_296_; lean_object* v_v_297_; uint64_t v___x_298_; size_t v_h_299_; size_t v___x_300_; lean_object* v___x_301_; size_t v___x_302_; size_t v___x_303_; size_t v___x_304_; size_t v_h_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v_k_296_ = lean_array_fget_borrowed(v_keys_290_, v_i_292_);
v_v_297_ = lean_array_fget_borrowed(v_vals_291_, v_i_292_);
v___x_298_ = lean_uint64_of_nat(v_k_296_);
v_h_299_ = lean_uint64_to_usize(v___x_298_);
v___x_300_ = ((size_t)5ULL);
v___x_301_ = lean_unsigned_to_nat(1u);
v___x_302_ = ((size_t)1ULL);
v___x_303_ = lean_usize_sub(v_depth_289_, v___x_302_);
v___x_304_ = lean_usize_mul(v___x_300_, v___x_303_);
v_h_305_ = lean_usize_shift_right(v_h_299_, v___x_304_);
v___x_306_ = lean_nat_add(v_i_292_, v___x_301_);
lean_dec(v_i_292_);
lean_inc(v_v_297_);
lean_inc(v_k_296_);
v___x_307_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_entries_293_, v_h_305_, v_depth_289_, v_k_296_, v_v_297_);
v_i_292_ = v___x_306_;
v_entries_293_ = v___x_307_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_309_, lean_object* v_keys_310_, lean_object* v_vals_311_, lean_object* v_i_312_, lean_object* v_entries_313_){
_start:
{
size_t v_depth_boxed_314_; lean_object* v_res_315_; 
v_depth_boxed_314_ = lean_unbox_usize(v_depth_309_);
lean_dec(v_depth_309_);
v_res_315_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg(v_depth_boxed_314_, v_keys_310_, v_vals_311_, v_i_312_, v_entries_313_);
lean_dec_ref(v_vals_311_);
lean_dec_ref(v_keys_310_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___boxed(lean_object* v_x_316_, lean_object* v_x_317_, lean_object* v_x_318_, lean_object* v_x_319_, lean_object* v_x_320_){
_start:
{
size_t v_x_7941__boxed_321_; size_t v_x_7942__boxed_322_; lean_object* v_res_323_; 
v_x_7941__boxed_321_ = lean_unbox_usize(v_x_317_);
lean_dec(v_x_317_);
v_x_7942__boxed_322_ = lean_unbox_usize(v_x_318_);
lean_dec(v_x_318_);
v_res_323_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_x_316_, v_x_7941__boxed_321_, v_x_7942__boxed_322_, v_x_319_, v_x_320_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0___redArg(lean_object* v_x_324_, lean_object* v_x_325_, lean_object* v_x_326_){
_start:
{
uint64_t v___x_327_; size_t v___x_328_; size_t v___x_329_; lean_object* v___x_330_; 
v___x_327_ = lean_uint64_of_nat(v_x_325_);
v___x_328_ = lean_uint64_to_usize(v___x_327_);
v___x_329_ = ((size_t)1ULL);
v___x_330_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_x_324_, v___x_328_, v___x_329_, v_x_325_, v_x_326_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___lam__0(lean_object* v_x_331_, lean_object* v___y_332_, lean_object* v_a_333_, lean_object* v_s_334_){
_start:
{
lean_object* v_vars_335_; lean_object* v_varMap_336_; lean_object* v_varsHistory_337_; lean_object* v_natToIntMap_338_; lean_object* v_natDef_339_; lean_object* v_dvds_340_; lean_object* v_lowers_341_; lean_object* v_uppers_342_; lean_object* v_diseqs_343_; lean_object* v_elimEqs_344_; lean_object* v_elimStack_345_; lean_object* v_occurs_346_; lean_object* v_assignment_347_; lean_object* v_nextCnstrId_348_; uint8_t v_caseSplits_349_; lean_object* v_steps_350_; lean_object* v_conflict_x3f_351_; lean_object* v_diseqSplits_352_; lean_object* v_divMod_353_; uint8_t v_usedCommRing_354_; lean_object* v_nonlinearOccs_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_364_; 
v_vars_335_ = lean_ctor_get(v_s_334_, 0);
v_varMap_336_ = lean_ctor_get(v_s_334_, 1);
v_varsHistory_337_ = lean_ctor_get(v_s_334_, 2);
v_natToIntMap_338_ = lean_ctor_get(v_s_334_, 3);
v_natDef_339_ = lean_ctor_get(v_s_334_, 4);
v_dvds_340_ = lean_ctor_get(v_s_334_, 5);
v_lowers_341_ = lean_ctor_get(v_s_334_, 6);
v_uppers_342_ = lean_ctor_get(v_s_334_, 7);
v_diseqs_343_ = lean_ctor_get(v_s_334_, 8);
v_elimEqs_344_ = lean_ctor_get(v_s_334_, 9);
v_elimStack_345_ = lean_ctor_get(v_s_334_, 10);
v_occurs_346_ = lean_ctor_get(v_s_334_, 11);
v_assignment_347_ = lean_ctor_get(v_s_334_, 12);
v_nextCnstrId_348_ = lean_ctor_get(v_s_334_, 13);
v_caseSplits_349_ = lean_ctor_get_uint8(v_s_334_, sizeof(void*)*19);
v_steps_350_ = lean_ctor_get(v_s_334_, 14);
v_conflict_x3f_351_ = lean_ctor_get(v_s_334_, 15);
v_diseqSplits_352_ = lean_ctor_get(v_s_334_, 16);
v_divMod_353_ = lean_ctor_get(v_s_334_, 17);
v_usedCommRing_354_ = lean_ctor_get_uint8(v_s_334_, sizeof(void*)*19 + 1);
v_nonlinearOccs_355_ = lean_ctor_get(v_s_334_, 18);
v_isSharedCheck_364_ = !lean_is_exclusive(v_s_334_);
if (v_isSharedCheck_364_ == 0)
{
v___x_357_ = v_s_334_;
v_isShared_358_ = v_isSharedCheck_364_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_nonlinearOccs_355_);
lean_inc(v_divMod_353_);
lean_inc(v_diseqSplits_352_);
lean_inc(v_conflict_x3f_351_);
lean_inc(v_steps_350_);
lean_inc(v_nextCnstrId_348_);
lean_inc(v_assignment_347_);
lean_inc(v_occurs_346_);
lean_inc(v_elimStack_345_);
lean_inc(v_elimEqs_344_);
lean_inc(v_diseqs_343_);
lean_inc(v_uppers_342_);
lean_inc(v_lowers_341_);
lean_inc(v_dvds_340_);
lean_inc(v_natDef_339_);
lean_inc(v_natToIntMap_338_);
lean_inc(v_varsHistory_337_);
lean_inc(v_varMap_336_);
lean_inc(v_vars_335_);
lean_dec(v_s_334_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_364_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_362_; 
v___x_359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_359_, 0, v_x_331_);
lean_ctor_set(v___x_359_, 1, v___y_332_);
v___x_360_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0___redArg(v_nonlinearOccs_355_, v_a_333_, v___x_359_);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 18, v___x_360_);
v___x_362_ = v___x_357_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_vars_335_);
lean_ctor_set(v_reuseFailAlloc_363_, 1, v_varMap_336_);
lean_ctor_set(v_reuseFailAlloc_363_, 2, v_varsHistory_337_);
lean_ctor_set(v_reuseFailAlloc_363_, 3, v_natToIntMap_338_);
lean_ctor_set(v_reuseFailAlloc_363_, 4, v_natDef_339_);
lean_ctor_set(v_reuseFailAlloc_363_, 5, v_dvds_340_);
lean_ctor_set(v_reuseFailAlloc_363_, 6, v_lowers_341_);
lean_ctor_set(v_reuseFailAlloc_363_, 7, v_uppers_342_);
lean_ctor_set(v_reuseFailAlloc_363_, 8, v_diseqs_343_);
lean_ctor_set(v_reuseFailAlloc_363_, 9, v_elimEqs_344_);
lean_ctor_set(v_reuseFailAlloc_363_, 10, v_elimStack_345_);
lean_ctor_set(v_reuseFailAlloc_363_, 11, v_occurs_346_);
lean_ctor_set(v_reuseFailAlloc_363_, 12, v_assignment_347_);
lean_ctor_set(v_reuseFailAlloc_363_, 13, v_nextCnstrId_348_);
lean_ctor_set(v_reuseFailAlloc_363_, 14, v_steps_350_);
lean_ctor_set(v_reuseFailAlloc_363_, 15, v_conflict_x3f_351_);
lean_ctor_set(v_reuseFailAlloc_363_, 16, v_diseqSplits_352_);
lean_ctor_set(v_reuseFailAlloc_363_, 17, v_divMod_353_);
lean_ctor_set(v_reuseFailAlloc_363_, 18, v___x_360_);
lean_ctor_set_uint8(v_reuseFailAlloc_363_, sizeof(void*)*19, v_caseSplits_349_);
lean_ctor_set_uint8(v_reuseFailAlloc_363_, sizeof(void*)*19 + 1, v_usedCommRing_354_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1(lean_object* v_a_365_, lean_object* v_x_366_){
_start:
{
if (lean_obj_tag(v_x_366_) == 0)
{
uint8_t v___x_367_; 
v___x_367_ = 0;
return v___x_367_;
}
else
{
lean_object* v_head_368_; lean_object* v_tail_369_; uint8_t v___x_370_; 
v_head_368_ = lean_ctor_get(v_x_366_, 0);
v_tail_369_ = lean_ctor_get(v_x_366_, 1);
v___x_370_ = lean_nat_dec_eq(v_a_365_, v_head_368_);
if (v___x_370_ == 0)
{
v_x_366_ = v_tail_369_;
goto _start;
}
else
{
return v___x_370_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___boxed(lean_object* v_a_372_, lean_object* v_x_373_){
_start:
{
uint8_t v_res_374_; lean_object* v_r_375_; 
v_res_374_ = l_List_elem___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1(v_a_372_, v_x_373_);
lean_dec(v_x_373_);
lean_dec(v_a_372_);
v_r_375_ = lean_box(v_res_374_);
return v_r_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6___redArg(lean_object* v_keys_376_, lean_object* v_vals_377_, lean_object* v_i_378_, lean_object* v_k_379_){
_start:
{
lean_object* v___x_380_; uint8_t v___x_381_; 
v___x_380_ = lean_array_get_size(v_keys_376_);
v___x_381_ = lean_nat_dec_lt(v_i_378_, v___x_380_);
if (v___x_381_ == 0)
{
lean_object* v___x_382_; 
lean_dec(v_i_378_);
v___x_382_ = lean_box(0);
return v___x_382_;
}
else
{
lean_object* v_k_x27_383_; uint8_t v___x_384_; 
v_k_x27_383_ = lean_array_fget_borrowed(v_keys_376_, v_i_378_);
v___x_384_ = lean_nat_dec_eq(v_k_379_, v_k_x27_383_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = lean_unsigned_to_nat(1u);
v___x_386_ = lean_nat_add(v_i_378_, v___x_385_);
lean_dec(v_i_378_);
v_i_378_ = v___x_386_;
goto _start;
}
else
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = lean_array_fget_borrowed(v_vals_377_, v_i_378_);
lean_dec(v_i_378_);
lean_inc(v___x_388_);
v___x_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
return v___x_389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_keys_390_, lean_object* v_vals_391_, lean_object* v_i_392_, lean_object* v_k_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6___redArg(v_keys_390_, v_vals_391_, v_i_392_, v_k_393_);
lean_dec(v_k_393_);
lean_dec_ref(v_vals_391_);
lean_dec_ref(v_keys_390_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___redArg(lean_object* v_x_395_, size_t v_x_396_, lean_object* v_x_397_){
_start:
{
if (lean_obj_tag(v_x_395_) == 0)
{
lean_object* v_es_398_; lean_object* v___x_399_; size_t v___x_400_; size_t v___x_401_; lean_object* v_j_402_; lean_object* v___x_403_; 
v_es_398_ = lean_ctor_get(v_x_395_, 0);
v___x_399_ = lean_box(2);
v___x_400_ = ((size_t)31ULL);
v___x_401_ = lean_usize_land(v_x_396_, v___x_400_);
v_j_402_ = lean_usize_to_nat(v___x_401_);
v___x_403_ = lean_array_get_borrowed(v___x_399_, v_es_398_, v_j_402_);
lean_dec(v_j_402_);
switch(lean_obj_tag(v___x_403_))
{
case 0:
{
lean_object* v_key_404_; lean_object* v_val_405_; uint8_t v___x_406_; 
v_key_404_ = lean_ctor_get(v___x_403_, 0);
v_val_405_ = lean_ctor_get(v___x_403_, 1);
v___x_406_ = lean_nat_dec_eq(v_x_397_, v_key_404_);
if (v___x_406_ == 0)
{
lean_object* v___x_407_; 
v___x_407_ = lean_box(0);
return v___x_407_;
}
else
{
lean_object* v___x_408_; 
lean_inc(v_val_405_);
v___x_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_408_, 0, v_val_405_);
return v___x_408_;
}
}
case 1:
{
lean_object* v_node_409_; size_t v___x_410_; size_t v___x_411_; 
v_node_409_ = lean_ctor_get(v___x_403_, 0);
v___x_410_ = ((size_t)5ULL);
v___x_411_ = lean_usize_shift_right(v_x_396_, v___x_410_);
v_x_395_ = v_node_409_;
v_x_396_ = v___x_411_;
goto _start;
}
default: 
{
lean_object* v___x_413_; 
v___x_413_ = lean_box(0);
return v___x_413_;
}
}
}
else
{
lean_object* v_ks_414_; lean_object* v_vs_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v_ks_414_ = lean_ctor_get(v_x_395_, 0);
v_vs_415_ = lean_ctor_get(v_x_395_, 1);
v___x_416_ = lean_unsigned_to_nat(0u);
v___x_417_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6___redArg(v_ks_414_, v_vs_415_, v___x_416_, v_x_397_);
return v___x_417_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___redArg___boxed(lean_object* v_x_418_, lean_object* v_x_419_, lean_object* v_x_420_){
_start:
{
size_t v_x_8160__boxed_421_; lean_object* v_res_422_; 
v_x_8160__boxed_421_ = lean_unbox_usize(v_x_419_);
lean_dec(v_x_419_);
v_res_422_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___redArg(v_x_418_, v_x_8160__boxed_421_, v_x_420_);
lean_dec(v_x_420_);
lean_dec_ref(v_x_418_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2___redArg(lean_object* v_x_423_, lean_object* v_x_424_){
_start:
{
uint64_t v___x_425_; size_t v___x_426_; lean_object* v___x_427_; 
v___x_425_ = lean_uint64_of_nat(v_x_424_);
v___x_426_ = lean_uint64_to_usize(v___x_425_);
v___x_427_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___redArg(v_x_423_, v___x_426_, v_x_424_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2___redArg___boxed(lean_object* v_x_428_, lean_object* v_x_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2___redArg(v_x_428_, v_x_429_);
lean_dec(v_x_429_);
lean_dec_ref(v_x_428_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(lean_object* v_arg_431_, lean_object* v_x_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = lean_box(0);
lean_inc(v_a_442_);
lean_inc_ref(v_a_441_);
lean_inc(v_a_440_);
lean_inc_ref(v_a_439_);
lean_inc(v_a_438_);
lean_inc_ref(v_a_437_);
lean_inc(v_a_436_);
lean_inc_ref(v_a_435_);
lean_inc(v_a_434_);
lean_inc(v_a_433_);
v___x_445_ = lean_grind_cutsat_mk_var(v_arg_431_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_514_; 
v_a_446_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_514_ == 0)
{
v___x_448_ = v___x_445_;
v_isShared_449_ = v_isSharedCheck_514_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_445_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_514_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___y_451_; lean_object* v___y_452_; lean_object* v___y_462_; lean_object* v___y_463_; lean_object* v___x_478_; 
v___x_478_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_433_, v_a_441_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; lean_object* v___y_481_; lean_object* v_elimEqs_501_; lean_object* v_size_502_; uint8_t v___x_503_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_a_479_);
lean_dec_ref_known(v___x_478_, 1);
v_elimEqs_501_ = lean_ctor_get(v_a_479_, 9);
lean_inc_ref(v_elimEqs_501_);
lean_dec(v_a_479_);
v_size_502_ = lean_ctor_get(v_elimEqs_501_, 2);
v___x_503_ = lean_nat_dec_lt(v_a_446_, v_size_502_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; 
lean_dec_ref(v_elimEqs_501_);
v___x_504_ = l_outOfBounds___redArg(v___x_444_);
v___y_481_ = v___x_504_;
goto v___jp_480_;
}
else
{
lean_object* v___x_505_; 
v___x_505_ = l_Lean_PersistentArray_get_x21___redArg(v___x_444_, v_elimEqs_501_, v_a_446_);
lean_dec_ref(v_elimEqs_501_);
v___y_481_ = v___x_505_;
goto v___jp_480_;
}
v___jp_480_:
{
if (lean_obj_tag(v___y_481_) == 0)
{
v___y_462_ = v_a_433_;
v___y_463_ = v_a_441_;
goto v___jp_461_;
}
else
{
lean_object* v___x_482_; 
lean_dec_ref_known(v___y_481_, 1);
lean_inc(v_a_442_);
lean_inc_ref(v_a_441_);
lean_inc(v_a_440_);
lean_inc_ref(v_a_439_);
lean_inc(v_a_438_);
lean_inc_ref(v_a_437_);
lean_inc(v_a_436_);
lean_inc_ref(v_a_435_);
lean_inc(v_a_434_);
lean_inc(v_a_433_);
lean_inc(v_x_432_);
lean_inc(v_a_446_);
v___x_482_ = lean_cutsat_propagate_nonlinear(v_a_446_, v_x_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_492_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_492_ == 0)
{
v___x_485_ = v___x_482_;
v_isShared_486_ = v_isSharedCheck_492_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_482_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_492_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
uint8_t v___x_487_; 
v___x_487_ = lean_unbox(v_a_483_);
lean_dec(v_a_483_);
if (v___x_487_ == 0)
{
lean_del_object(v___x_485_);
v___y_462_ = v_a_433_;
v___y_463_ = v_a_441_;
goto v___jp_461_;
}
else
{
lean_object* v___x_488_; lean_object* v___x_490_; 
lean_del_object(v___x_448_);
lean_dec(v_a_446_);
lean_dec(v_x_432_);
v___x_488_ = lean_box(0);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 0, v___x_488_);
v___x_490_ = v___x_485_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_488_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
else
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_500_; 
lean_del_object(v___x_448_);
lean_dec(v_a_446_);
lean_dec(v_x_432_);
v_a_493_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_500_ == 0)
{
v___x_495_ = v___x_482_;
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_482_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_498_; 
if (v_isShared_496_ == 0)
{
v___x_498_ = v___x_495_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_a_493_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
}
}
else
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_513_; 
lean_del_object(v___x_448_);
lean_dec(v_a_446_);
lean_dec(v_x_432_);
v_a_506_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_513_ == 0)
{
v___x_508_ = v___x_478_;
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_478_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
if (v_isShared_509_ == 0)
{
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_a_506_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
v___jp_450_:
{
uint8_t v___x_453_; 
v___x_453_ = l_List_elem___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1(v_x_432_, v___y_452_);
if (v___x_453_ == 0)
{
lean_object* v___f_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
lean_del_object(v___x_448_);
v___f_454_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___lam__0), 4, 3);
lean_closure_set(v___f_454_, 0, v_x_432_);
lean_closure_set(v___f_454_, 1, v___y_452_);
lean_closure_set(v___f_454_, 2, v_a_446_);
v___x_455_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_456_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_455_, v___f_454_, v___y_451_);
return v___x_456_;
}
else
{
lean_object* v___x_457_; lean_object* v___x_459_; 
lean_dec(v___y_452_);
lean_dec(v_a_446_);
lean_dec(v_x_432_);
v___x_457_ = lean_box(0);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 0, v___x_457_);
v___x_459_ = v___x_448_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_457_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
v___jp_461_:
{
lean_object* v___x_464_; 
v___x_464_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v___y_462_, v___y_463_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; lean_object* v_nonlinearOccs_466_; lean_object* v___x_467_; 
v_a_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_a_465_);
lean_dec_ref_known(v___x_464_, 1);
v_nonlinearOccs_466_ = lean_ctor_get(v_a_465_, 18);
lean_inc_ref(v_nonlinearOccs_466_);
lean_dec(v_a_465_);
v___x_467_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2___redArg(v_nonlinearOccs_466_, v_a_446_);
lean_dec_ref(v_nonlinearOccs_466_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v___x_468_; 
v___x_468_ = lean_box(0);
v___y_451_ = v___y_462_;
v___y_452_ = v___x_468_;
goto v___jp_450_;
}
else
{
lean_object* v_val_469_; 
v_val_469_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_val_469_);
lean_dec_ref_known(v___x_467_, 1);
v___y_451_ = v___y_462_;
v___y_452_ = v_val_469_;
goto v___jp_450_;
}
}
else
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_477_; 
lean_del_object(v___x_448_);
lean_dec(v_a_446_);
lean_dec(v_x_432_);
v_a_470_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_477_ == 0)
{
v___x_472_ = v___x_464_;
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_464_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_475_; 
if (v_isShared_473_ == 0)
{
v___x_475_ = v___x_472_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_a_470_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
}
}
else
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_522_; 
lean_dec(v_x_432_);
v_a_515_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_522_ == 0)
{
v___x_517_ = v___x_445_;
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_445_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_520_; 
if (v_isShared_518_ == 0)
{
v___x_520_ = v___x_517_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_a_515_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___boxed(lean_object* v_arg_523_, lean_object* v_x_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_arg_523_, v_x_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_);
lean_dec(v_a_534_);
lean_dec_ref(v_a_533_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
lean_dec(v_a_530_);
lean_dec_ref(v_a_529_);
lean_dec(v_a_528_);
lean_dec_ref(v_a_527_);
lean_dec(v_a_526_);
lean_dec(v_a_525_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0(lean_object* v_00_u03b2_537_, lean_object* v_x_538_, lean_object* v_x_539_, lean_object* v_x_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0___redArg(v_x_538_, v_x_539_, v_x_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2(lean_object* v_00_u03b2_542_, lean_object* v_x_543_, lean_object* v_x_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2___redArg(v_x_543_, v_x_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2___boxed(lean_object* v_00_u03b2_546_, lean_object* v_x_547_, lean_object* v_x_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2(v_00_u03b2_546_, v_x_547_, v_x_548_);
lean_dec(v_x_548_);
lean_dec_ref(v_x_547_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0(lean_object* v_00_u03b2_550_, lean_object* v_x_551_, size_t v_x_552_, size_t v_x_553_, lean_object* v_x_554_, lean_object* v_x_555_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_x_551_, v_x_552_, v_x_553_, v_x_554_, v_x_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___boxed(lean_object* v_00_u03b2_557_, lean_object* v_x_558_, lean_object* v_x_559_, lean_object* v_x_560_, lean_object* v_x_561_, lean_object* v_x_562_){
_start:
{
size_t v_x_8391__boxed_563_; size_t v_x_8392__boxed_564_; lean_object* v_res_565_; 
v_x_8391__boxed_563_ = lean_unbox_usize(v_x_559_);
lean_dec(v_x_559_);
v_x_8392__boxed_564_ = lean_unbox_usize(v_x_560_);
lean_dec(v_x_560_);
v_res_565_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0(v_00_u03b2_557_, v_x_558_, v_x_8391__boxed_563_, v_x_8392__boxed_564_, v_x_561_, v_x_562_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3(lean_object* v_00_u03b2_566_, lean_object* v_x_567_, size_t v_x_568_, lean_object* v_x_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___redArg(v_x_567_, v_x_568_, v_x_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___boxed(lean_object* v_00_u03b2_571_, lean_object* v_x_572_, lean_object* v_x_573_, lean_object* v_x_574_){
_start:
{
size_t v_x_8408__boxed_575_; lean_object* v_res_576_; 
v_x_8408__boxed_575_ = lean_unbox_usize(v_x_573_);
lean_dec(v_x_573_);
v_res_576_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3(v_00_u03b2_571_, v_x_572_, v_x_8408__boxed_575_, v_x_574_);
lean_dec(v_x_574_);
lean_dec_ref(v_x_572_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_577_, lean_object* v_n_578_, lean_object* v_k_579_, lean_object* v_v_580_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1___redArg(v_n_578_, v_k_579_, v_v_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_582_, size_t v_depth_583_, lean_object* v_keys_584_, lean_object* v_vals_585_, lean_object* v_heq_586_, lean_object* v_i_587_, lean_object* v_entries_588_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg(v_depth_583_, v_keys_584_, v_vals_585_, v_i_587_, v_entries_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_590_, lean_object* v_depth_591_, lean_object* v_keys_592_, lean_object* v_vals_593_, lean_object* v_heq_594_, lean_object* v_i_595_, lean_object* v_entries_596_){
_start:
{
size_t v_depth_boxed_597_; lean_object* v_res_598_; 
v_depth_boxed_597_ = lean_unbox_usize(v_depth_591_);
lean_dec(v_depth_591_);
v_res_598_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2(v_00_u03b2_590_, v_depth_boxed_597_, v_keys_592_, v_vals_593_, v_heq_594_, v_i_595_, v_entries_596_);
lean_dec_ref(v_vals_593_);
lean_dec_ref(v_keys_592_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_599_, lean_object* v_keys_600_, lean_object* v_vals_601_, lean_object* v_heq_602_, lean_object* v_i_603_, lean_object* v_k_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6___redArg(v_keys_600_, v_vals_601_, v_i_603_, v_k_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_606_, lean_object* v_keys_607_, lean_object* v_vals_608_, lean_object* v_heq_609_, lean_object* v_i_610_, lean_object* v_k_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6(v_00_u03b2_606_, v_keys_607_, v_vals_608_, v_heq_609_, v_i_610_, v_k_611_);
lean_dec(v_k_611_);
lean_dec_ref(v_vals_608_);
lean_dec_ref(v_keys_607_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_613_, lean_object* v_x_614_, lean_object* v_x_615_, lean_object* v_x_616_, lean_object* v_x_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__4___redArg(v_x_614_, v_x_615_, v_x_616_, v_x_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(lean_object* v_x_619_, lean_object* v_e_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
lean_object* v___x_632_; 
lean_inc_ref(v_e_620_);
v___x_632_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_620_, v_a_628_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v___x_634_; uint8_t v___x_635_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_633_);
lean_dec_ref_known(v___x_632_, 1);
v___x_634_ = l_Lean_Expr_cleanupAnnotations(v_a_633_);
v___x_635_ = l_Lean_Expr_isApp(v___x_634_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; 
lean_dec_ref(v___x_634_);
v___x_636_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_620_, v_x_619_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
return v___x_636_;
}
else
{
lean_object* v_arg_637_; lean_object* v___x_638_; uint8_t v___x_639_; 
v_arg_637_ = lean_ctor_get(v___x_634_, 1);
lean_inc_ref(v_arg_637_);
v___x_638_ = l_Lean_Expr_appFnCleanup___redArg(v___x_634_);
v___x_639_ = l_Lean_Expr_isApp(v___x_638_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; 
lean_dec_ref(v___x_638_);
lean_dec_ref(v_arg_637_);
v___x_640_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_620_, v_x_619_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
return v___x_640_;
}
else
{
lean_object* v_arg_641_; lean_object* v___x_642_; uint8_t v___x_643_; 
v_arg_641_ = lean_ctor_get(v___x_638_, 1);
lean_inc_ref(v_arg_641_);
v___x_642_ = l_Lean_Expr_appFnCleanup___redArg(v___x_638_);
v___x_643_ = l_Lean_Expr_isApp(v___x_642_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; 
lean_dec_ref(v___x_642_);
lean_dec_ref(v_arg_641_);
lean_dec_ref(v_arg_637_);
v___x_644_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_620_, v_x_619_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
return v___x_644_;
}
else
{
lean_object* v_arg_645_; lean_object* v___x_646_; uint8_t v___x_647_; 
v_arg_645_ = lean_ctor_get(v___x_642_, 1);
lean_inc_ref(v_arg_645_);
v___x_646_ = l_Lean_Expr_appFnCleanup___redArg(v___x_642_);
v___x_647_ = l_Lean_Expr_isApp(v___x_646_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; 
lean_dec_ref(v___x_646_);
lean_dec_ref(v_arg_645_);
lean_dec_ref(v_arg_641_);
lean_dec_ref(v_arg_637_);
v___x_648_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_620_, v_x_619_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
return v___x_648_;
}
else
{
lean_object* v___x_649_; uint8_t v___x_650_; 
v___x_649_ = l_Lean_Expr_appFnCleanup___redArg(v___x_646_);
v___x_650_ = l_Lean_Expr_isApp(v___x_649_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; 
lean_dec_ref(v___x_649_);
lean_dec_ref(v_arg_645_);
lean_dec_ref(v_arg_641_);
lean_dec_ref(v_arg_637_);
v___x_651_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_620_, v_x_619_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
return v___x_651_;
}
else
{
lean_object* v___x_652_; uint8_t v___x_653_; 
v___x_652_ = l_Lean_Expr_appFnCleanup___redArg(v___x_649_);
v___x_653_ = l_Lean_Expr_isApp(v___x_652_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; 
lean_dec_ref(v___x_652_);
lean_dec_ref(v_arg_645_);
lean_dec_ref(v_arg_641_);
lean_dec_ref(v_arg_637_);
v___x_654_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_620_, v_x_619_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
return v___x_654_;
}
else
{
lean_object* v___x_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v___x_655_ = l_Lean_Expr_appFnCleanup___redArg(v___x_652_);
v___x_656_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11));
v___x_657_ = l_Lean_Expr_isConstOf(v___x_655_, v___x_656_);
lean_dec_ref(v___x_655_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; 
lean_dec_ref(v_arg_645_);
lean_dec_ref(v_arg_641_);
lean_dec_ref(v_arg_637_);
v___x_658_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_620_, v_x_619_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
return v___x_658_;
}
else
{
lean_object* v___x_659_; 
v___x_659_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_645_, v_a_628_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v_a_660_; uint8_t v___x_661_; 
v_a_660_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_a_660_);
lean_dec_ref_known(v___x_659_, 1);
v___x_661_ = lean_unbox(v_a_660_);
lean_dec(v_a_660_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; 
lean_dec_ref(v_arg_641_);
lean_dec_ref(v_arg_637_);
v___x_662_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_620_, v_x_619_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
return v___x_662_;
}
else
{
lean_object* v___x_663_; 
lean_dec_ref(v_e_620_);
lean_inc(v_x_619_);
v___x_663_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(v_x_619_, v_arg_641_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_dec_ref_known(v___x_663_, 1);
v_e_620_ = v_arg_637_;
goto _start;
}
else
{
lean_dec_ref(v_arg_637_);
lean_dec(v_x_619_);
return v___x_663_;
}
}
}
else
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
lean_dec_ref(v_arg_641_);
lean_dec_ref(v_arg_637_);
lean_dec_ref(v_e_620_);
lean_dec(v_x_619_);
v_a_665_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v___x_659_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_659_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_665_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
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
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_680_; 
lean_dec_ref(v_e_620_);
lean_dec(v_x_619_);
v_a_673_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_680_ == 0)
{
v___x_675_ = v___x_632_;
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_632_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_678_; 
if (v_isShared_676_ == 0)
{
v___x_678_ = v___x_675_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_a_673_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go___boxed(lean_object* v_x_681_, lean_object* v_e_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(v_x_681_, v_e_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_);
lean_dec(v_a_692_);
lean_dec_ref(v_a_691_);
lean_dec(v_a_690_);
lean_dec_ref(v_a_689_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
lean_dec(v_a_686_);
lean_dec_ref(v_a_685_);
lean_dec(v_a_684_);
lean_dec(v_a_683_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt(lean_object* v_e_695_, lean_object* v_x_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_695_, v_a_704_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_a_715_);
lean_dec_ref_known(v___x_714_, 1);
v___x_716_ = l_Lean_Expr_cleanupAnnotations(v_a_715_);
v___x_717_ = l_Lean_Expr_isApp(v___x_716_);
if (v___x_717_ == 0)
{
lean_dec_ref(v___x_716_);
lean_dec(v_x_696_);
goto v___jp_708_;
}
else
{
lean_object* v_arg_718_; lean_object* v___y_720_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v___y_724_; lean_object* v___y_725_; lean_object* v___y_726_; lean_object* v___y_727_; lean_object* v___y_728_; lean_object* v___y_729_; lean_object* v___x_774_; uint8_t v___x_775_; 
v_arg_718_ = lean_ctor_get(v___x_716_, 1);
lean_inc_ref(v_arg_718_);
v___x_774_ = l_Lean_Expr_appFnCleanup___redArg(v___x_716_);
v___x_775_ = l_Lean_Expr_isApp(v___x_774_);
if (v___x_775_ == 0)
{
lean_dec_ref(v___x_774_);
lean_dec_ref(v_arg_718_);
lean_dec(v_x_696_);
goto v___jp_708_;
}
else
{
lean_object* v_arg_776_; lean_object* v___x_777_; uint8_t v___x_778_; 
v_arg_776_ = lean_ctor_get(v___x_774_, 1);
lean_inc_ref(v_arg_776_);
v___x_777_ = l_Lean_Expr_appFnCleanup___redArg(v___x_774_);
v___x_778_ = l_Lean_Expr_isApp(v___x_777_);
if (v___x_778_ == 0)
{
lean_dec_ref(v___x_777_);
lean_dec_ref(v_arg_776_);
lean_dec_ref(v_arg_718_);
lean_dec(v_x_696_);
goto v___jp_708_;
}
else
{
lean_object* v___x_779_; uint8_t v___x_780_; 
v___x_779_ = l_Lean_Expr_appFnCleanup___redArg(v___x_777_);
v___x_780_ = l_Lean_Expr_isApp(v___x_779_);
if (v___x_780_ == 0)
{
lean_dec_ref(v___x_779_);
lean_dec_ref(v_arg_776_);
lean_dec_ref(v_arg_718_);
lean_dec(v_x_696_);
goto v___jp_708_;
}
else
{
lean_object* v___x_781_; uint8_t v___x_782_; 
v___x_781_ = l_Lean_Expr_appFnCleanup___redArg(v___x_779_);
v___x_782_ = l_Lean_Expr_isApp(v___x_781_);
if (v___x_782_ == 0)
{
lean_dec_ref(v___x_781_);
lean_dec_ref(v_arg_776_);
lean_dec_ref(v_arg_718_);
lean_dec(v_x_696_);
goto v___jp_708_;
}
else
{
lean_object* v___x_783_; uint8_t v___x_784_; 
v___x_783_ = l_Lean_Expr_appFnCleanup___redArg(v___x_781_);
v___x_784_ = l_Lean_Expr_isApp(v___x_783_);
if (v___x_784_ == 0)
{
lean_dec_ref(v___x_783_);
lean_dec_ref(v_arg_776_);
lean_dec_ref(v_arg_718_);
lean_dec(v_x_696_);
goto v___jp_708_;
}
else
{
lean_object* v___x_785_; lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_785_ = l_Lean_Expr_appFnCleanup___redArg(v___x_783_);
v___x_786_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__2));
v___x_787_ = l_Lean_Expr_isConstOf(v___x_785_, v___x_786_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; uint8_t v___x_789_; 
v___x_788_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__5));
v___x_789_ = l_Lean_Expr_isConstOf(v___x_785_, v___x_788_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; uint8_t v___x_791_; 
v___x_790_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__8));
v___x_791_ = l_Lean_Expr_isConstOf(v___x_785_, v___x_790_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; uint8_t v___x_793_; 
v___x_792_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11));
v___x_793_ = l_Lean_Expr_isConstOf(v___x_785_, v___x_792_);
lean_dec_ref(v___x_785_);
if (v___x_793_ == 0)
{
lean_dec_ref(v_arg_776_);
lean_dec_ref(v_arg_718_);
lean_dec(v_x_696_);
goto v___jp_708_;
}
else
{
lean_object* v___x_794_; 
lean_inc(v_x_696_);
v___x_794_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(v_x_696_, v_arg_776_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v___x_795_; 
lean_dec_ref_known(v___x_794_, 1);
v___x_795_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(v_x_696_, v_arg_718_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_);
return v___x_795_;
}
else
{
lean_dec_ref(v_arg_718_);
lean_dec(v_x_696_);
return v___x_794_;
}
}
}
else
{
lean_object* v___x_796_; 
lean_dec_ref(v___x_785_);
lean_dec_ref(v_arg_776_);
v___x_796_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_arg_718_, v_x_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_);
return v___x_796_;
}
}
else
{
lean_object* v___x_797_; 
lean_dec_ref(v___x_785_);
lean_dec_ref(v_arg_776_);
v___x_797_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_arg_718_, v_x_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_);
return v___x_797_;
}
}
else
{
lean_object* v___x_798_; 
lean_dec_ref(v___x_785_);
lean_inc_ref(v_arg_776_);
v___x_798_ = l_Lean_Meta_getIntValue_x3f(v_arg_776_, v_a_703_, v_a_704_, v_a_705_, v_a_706_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_a_799_);
lean_dec_ref_known(v___x_798_, 1);
if (lean_obj_tag(v_a_799_) == 0)
{
lean_object* v___x_800_; 
lean_inc(v_x_696_);
v___x_800_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_arg_776_, v_x_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_dec_ref_known(v___x_800_, 1);
v___y_720_ = v_a_697_;
v___y_721_ = v_a_698_;
v___y_722_ = v_a_699_;
v___y_723_ = v_a_700_;
v___y_724_ = v_a_701_;
v___y_725_ = v_a_702_;
v___y_726_ = v_a_703_;
v___y_727_ = v_a_704_;
v___y_728_ = v_a_705_;
v___y_729_ = v_a_706_;
goto v___jp_719_;
}
else
{
lean_dec_ref(v_arg_718_);
lean_dec(v_x_696_);
return v___x_800_;
}
}
else
{
lean_dec_ref_known(v_a_799_, 1);
lean_dec_ref(v_arg_776_);
v___y_720_ = v_a_697_;
v___y_721_ = v_a_698_;
v___y_722_ = v_a_699_;
v___y_723_ = v_a_700_;
v___y_724_ = v_a_701_;
v___y_725_ = v_a_702_;
v___y_726_ = v_a_703_;
v___y_727_ = v_a_704_;
v___y_728_ = v_a_705_;
v___y_729_ = v_a_706_;
goto v___jp_719_;
}
}
else
{
lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_808_; 
lean_dec_ref(v_arg_776_);
lean_dec_ref(v_arg_718_);
lean_dec(v_x_696_);
v_a_801_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_808_ == 0)
{
v___x_803_ = v___x_798_;
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_a_801_);
lean_dec(v___x_798_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_806_; 
if (v_isShared_804_ == 0)
{
v___x_806_ = v___x_803_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_a_801_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
}
}
}
}
}
}
v___jp_719_:
{
lean_object* v___x_730_; 
lean_inc_ref(v_arg_718_);
v___x_730_ = l_Lean_Meta_getIntValue_x3f(v_arg_718_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v_a_731_; lean_object* v___x_732_; 
v_a_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_a_731_);
lean_dec_ref_known(v___x_730_, 1);
v___x_732_ = l_Lean_Meta_getNatValue_x3f(v_arg_718_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
if (lean_obj_tag(v___x_732_) == 0)
{
if (lean_obj_tag(v_a_731_) == 0)
{
lean_object* v_a_733_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
lean_inc(v_a_733_);
lean_dec_ref_known(v___x_732_, 1);
if (lean_obj_tag(v_a_733_) == 0)
{
lean_object* v___x_734_; 
lean_inc_ref(v_arg_718_);
v___x_734_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_arg_718_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; lean_object* v_fst_736_; lean_object* v___x_737_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_a_735_);
lean_dec_ref_known(v___x_734_, 1);
v_fst_736_ = lean_ctor_get(v_a_735_, 0);
lean_inc(v_fst_736_);
lean_dec(v_a_735_);
v___x_737_ = l_Lean_Meta_Grind_getGeneration___redArg(v_arg_718_, v___y_720_);
lean_dec_ref(v_arg_718_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_a_738_);
lean_dec_ref_known(v___x_737_, 1);
v___x_739_ = lean_box(0);
lean_inc(v___y_729_);
lean_inc_ref(v___y_728_);
lean_inc(v___y_727_);
lean_inc_ref(v___y_726_);
lean_inc(v___y_725_);
lean_inc_ref(v___y_724_);
lean_inc(v___y_723_);
lean_inc_ref(v___y_722_);
lean_inc(v___y_721_);
lean_inc(v___y_720_);
lean_inc(v_fst_736_);
v___x_740_ = lean_grind_internalize(v_fst_736_, v_a_738_, v___x_739_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v___x_741_; 
lean_dec_ref_known(v___x_740_, 1);
v___x_741_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_fst_736_, v_x_696_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
return v___x_741_;
}
else
{
lean_dec(v_fst_736_);
lean_dec(v_x_696_);
return v___x_740_;
}
}
else
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_749_; 
lean_dec(v_fst_736_);
lean_dec(v_x_696_);
v_a_742_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_749_ == 0)
{
v___x_744_ = v___x_737_;
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_737_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_747_; 
if (v_isShared_745_ == 0)
{
v___x_747_ = v___x_744_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_a_742_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
else
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
lean_dec_ref(v_arg_718_);
lean_dec(v_x_696_);
v_a_750_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_757_ == 0)
{
v___x_752_ = v___x_734_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_734_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_750_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_733_, 1);
lean_dec_ref(v_arg_718_);
lean_dec(v_x_696_);
goto v___jp_711_;
}
}
else
{
lean_dec_ref_known(v_a_731_, 1);
lean_dec_ref_known(v___x_732_, 1);
lean_dec_ref(v_arg_718_);
lean_dec(v_x_696_);
goto v___jp_711_;
}
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
lean_dec(v_a_731_);
lean_dec_ref(v_arg_718_);
lean_dec(v_x_696_);
v_a_758_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_732_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_732_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_dec_ref(v_arg_718_);
lean_dec(v_x_696_);
v_a_766_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_730_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_730_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
}
}
else
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_dec(v_x_696_);
v_a_809_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_714_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_714_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_809_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
v___jp_708_:
{
lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_709_ = lean_box(0);
v___x_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
return v___x_710_;
}
v___jp_711_:
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = lean_box(0);
v___x_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
return v___x_713_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt___boxed(lean_object* v_e_817_, lean_object* v_x_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt(v_e_817_, v_x_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
lean_dec(v_a_828_);
lean_dec_ref(v_a_827_);
lean_dec(v_a_826_);
lean_dec_ref(v_a_825_);
lean_dec(v_a_824_);
lean_dec_ref(v_a_823_);
lean_dec(v_a_822_);
lean_dec_ref(v_a_821_);
lean_dec(v_a_820_);
lean_dec(v_a_819_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_x_831_, lean_object* v_x_832_, lean_object* v_x_833_, lean_object* v_x_834_){
_start:
{
lean_object* v_ks_835_; lean_object* v_vs_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_862_; 
v_ks_835_ = lean_ctor_get(v_x_831_, 0);
v_vs_836_ = lean_ctor_get(v_x_831_, 1);
v_isSharedCheck_862_ = !lean_is_exclusive(v_x_831_);
if (v_isSharedCheck_862_ == 0)
{
v___x_838_ = v_x_831_;
v_isShared_839_ = v_isSharedCheck_862_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_vs_836_);
lean_inc(v_ks_835_);
lean_dec(v_x_831_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_862_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_840_; uint8_t v___x_841_; 
v___x_840_ = lean_array_get_size(v_ks_835_);
v___x_841_ = lean_nat_dec_lt(v_x_832_, v___x_840_);
if (v___x_841_ == 0)
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_845_; 
lean_dec(v_x_832_);
v___x_842_ = lean_array_push(v_ks_835_, v_x_833_);
v___x_843_ = lean_array_push(v_vs_836_, v_x_834_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 1, v___x_843_);
lean_ctor_set(v___x_838_, 0, v___x_842_);
v___x_845_ = v___x_838_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_842_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v___x_843_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
else
{
lean_object* v_k_x27_847_; size_t v___x_848_; size_t v___x_849_; uint8_t v___x_850_; 
v_k_x27_847_ = lean_array_fget_borrowed(v_ks_835_, v_x_832_);
v___x_848_ = lean_ptr_addr(v_x_833_);
v___x_849_ = lean_ptr_addr(v_k_x27_847_);
v___x_850_ = lean_usize_dec_eq(v___x_848_, v___x_849_);
if (v___x_850_ == 0)
{
lean_object* v___x_852_; 
if (v_isShared_839_ == 0)
{
v___x_852_ = v___x_838_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_ks_835_);
lean_ctor_set(v_reuseFailAlloc_856_, 1, v_vs_836_);
v___x_852_ = v_reuseFailAlloc_856_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_853_ = lean_unsigned_to_nat(1u);
v___x_854_ = lean_nat_add(v_x_832_, v___x_853_);
lean_dec(v_x_832_);
v_x_831_ = v___x_852_;
v_x_832_ = v___x_854_;
goto _start;
}
}
else
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_860_; 
v___x_857_ = lean_array_fset(v_ks_835_, v_x_832_, v_x_833_);
v___x_858_ = lean_array_fset(v_vs_836_, v_x_832_, v_x_834_);
lean_dec(v_x_832_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 1, v___x_858_);
lean_ctor_set(v___x_838_, 0, v___x_857_);
v___x_860_ = v___x_838_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_857_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v___x_858_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4___redArg(lean_object* v_n_863_, lean_object* v_k_864_, lean_object* v_v_865_){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_866_ = lean_unsigned_to_nat(0u);
v___x_867_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7___redArg(v_n_863_, v___x_866_, v_k_864_, v_v_865_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(lean_object* v_x_868_, size_t v_x_869_, size_t v_x_870_, lean_object* v_x_871_, lean_object* v_x_872_){
_start:
{
if (lean_obj_tag(v_x_868_) == 0)
{
lean_object* v_es_873_; size_t v___x_874_; size_t v___x_875_; lean_object* v_j_876_; lean_object* v___x_877_; uint8_t v___x_878_; 
v_es_873_ = lean_ctor_get(v_x_868_, 0);
v___x_874_ = ((size_t)31ULL);
v___x_875_ = lean_usize_land(v_x_869_, v___x_874_);
v_j_876_ = lean_usize_to_nat(v___x_875_);
v___x_877_ = lean_array_get_size(v_es_873_);
v___x_878_ = lean_nat_dec_lt(v_j_876_, v___x_877_);
if (v___x_878_ == 0)
{
lean_dec(v_j_876_);
lean_dec(v_x_872_);
lean_dec_ref(v_x_871_);
return v_x_868_;
}
else
{
lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_919_; 
lean_inc_ref(v_es_873_);
v_isSharedCheck_919_ = !lean_is_exclusive(v_x_868_);
if (v_isSharedCheck_919_ == 0)
{
lean_object* v_unused_920_; 
v_unused_920_ = lean_ctor_get(v_x_868_, 0);
lean_dec(v_unused_920_);
v___x_880_ = v_x_868_;
v_isShared_881_ = v_isSharedCheck_919_;
goto v_resetjp_879_;
}
else
{
lean_dec(v_x_868_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_919_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v_v_882_; lean_object* v___x_883_; lean_object* v_xs_x27_884_; lean_object* v___y_886_; 
v_v_882_ = lean_array_fget(v_es_873_, v_j_876_);
v___x_883_ = lean_box(0);
v_xs_x27_884_ = lean_array_fset(v_es_873_, v_j_876_, v___x_883_);
switch(lean_obj_tag(v_v_882_))
{
case 0:
{
lean_object* v_key_891_; lean_object* v_val_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_904_; 
v_key_891_ = lean_ctor_get(v_v_882_, 0);
v_val_892_ = lean_ctor_get(v_v_882_, 1);
v_isSharedCheck_904_ = !lean_is_exclusive(v_v_882_);
if (v_isSharedCheck_904_ == 0)
{
v___x_894_ = v_v_882_;
v_isShared_895_ = v_isSharedCheck_904_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_val_892_);
lean_inc(v_key_891_);
lean_dec(v_v_882_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_904_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
size_t v___x_896_; size_t v___x_897_; uint8_t v___x_898_; 
v___x_896_ = lean_ptr_addr(v_x_871_);
v___x_897_ = lean_ptr_addr(v_key_891_);
v___x_898_ = lean_usize_dec_eq(v___x_896_, v___x_897_);
if (v___x_898_ == 0)
{
lean_object* v___x_899_; lean_object* v___x_900_; 
lean_del_object(v___x_894_);
v___x_899_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_891_, v_val_892_, v_x_871_, v_x_872_);
v___x_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
v___y_886_ = v___x_900_;
goto v___jp_885_;
}
else
{
lean_object* v___x_902_; 
lean_dec(v_val_892_);
lean_dec(v_key_891_);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 1, v_x_872_);
lean_ctor_set(v___x_894_, 0, v_x_871_);
v___x_902_ = v___x_894_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_x_871_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v_x_872_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
v___y_886_ = v___x_902_;
goto v___jp_885_;
}
}
}
}
case 1:
{
lean_object* v_node_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_917_; 
v_node_905_ = lean_ctor_get(v_v_882_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v_v_882_);
if (v_isSharedCheck_917_ == 0)
{
v___x_907_ = v_v_882_;
v_isShared_908_ = v_isSharedCheck_917_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_node_905_);
lean_dec(v_v_882_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_917_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
size_t v___x_909_; size_t v___x_910_; size_t v___x_911_; size_t v___x_912_; lean_object* v___x_913_; lean_object* v___x_915_; 
v___x_909_ = ((size_t)5ULL);
v___x_910_ = lean_usize_shift_right(v_x_869_, v___x_909_);
v___x_911_ = ((size_t)1ULL);
v___x_912_ = lean_usize_add(v_x_870_, v___x_911_);
v___x_913_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_node_905_, v___x_910_, v___x_912_, v_x_871_, v_x_872_);
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 0, v___x_913_);
v___x_915_ = v___x_907_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v___x_913_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
v___y_886_ = v___x_915_;
goto v___jp_885_;
}
}
}
default: 
{
lean_object* v___x_918_; 
v___x_918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_918_, 0, v_x_871_);
lean_ctor_set(v___x_918_, 1, v_x_872_);
v___y_886_ = v___x_918_;
goto v___jp_885_;
}
}
v___jp_885_:
{
lean_object* v___x_887_; lean_object* v___x_889_; 
v___x_887_ = lean_array_fset(v_xs_x27_884_, v_j_876_, v___y_886_);
lean_dec(v_j_876_);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 0, v___x_887_);
v___x_889_ = v___x_880_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_887_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
}
else
{
lean_object* v_ks_921_; lean_object* v_vs_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_940_; 
v_ks_921_ = lean_ctor_get(v_x_868_, 0);
v_vs_922_ = lean_ctor_get(v_x_868_, 1);
v_isSharedCheck_940_ = !lean_is_exclusive(v_x_868_);
if (v_isSharedCheck_940_ == 0)
{
v___x_924_ = v_x_868_;
v_isShared_925_ = v_isSharedCheck_940_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_vs_922_);
lean_inc(v_ks_921_);
lean_dec(v_x_868_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_940_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_ks_921_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v_vs_922_);
v___x_927_ = v_reuseFailAlloc_939_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
lean_object* v_newNode_928_; size_t v___x_929_; uint8_t v___x_930_; 
v_newNode_928_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4___redArg(v___x_927_, v_x_871_, v_x_872_);
v___x_929_ = ((size_t)7ULL);
v___x_930_ = lean_usize_dec_le(v___x_929_, v_x_870_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; lean_object* v___x_932_; uint8_t v___x_933_; 
v___x_931_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_928_);
v___x_932_ = lean_unsigned_to_nat(4u);
v___x_933_ = lean_nat_dec_lt(v___x_931_, v___x_932_);
lean_dec(v___x_931_);
if (v___x_933_ == 0)
{
lean_object* v_ks_934_; lean_object* v_vs_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v_ks_934_ = lean_ctor_get(v_newNode_928_, 0);
lean_inc_ref(v_ks_934_);
v_vs_935_ = lean_ctor_get(v_newNode_928_, 1);
lean_inc_ref(v_vs_935_);
lean_dec_ref(v_newNode_928_);
v___x_936_ = lean_unsigned_to_nat(0u);
v___x_937_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0);
v___x_938_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(v_x_870_, v_ks_934_, v_vs_935_, v___x_936_, v___x_937_);
lean_dec_ref(v_vs_935_);
lean_dec_ref(v_ks_934_);
return v___x_938_;
}
else
{
return v_newNode_928_;
}
}
else
{
return v_newNode_928_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(size_t v_depth_941_, lean_object* v_keys_942_, lean_object* v_vals_943_, lean_object* v_i_944_, lean_object* v_entries_945_){
_start:
{
lean_object* v___x_946_; uint8_t v___x_947_; 
v___x_946_ = lean_array_get_size(v_keys_942_);
v___x_947_ = lean_nat_dec_lt(v_i_944_, v___x_946_);
if (v___x_947_ == 0)
{
lean_dec(v_i_944_);
return v_entries_945_;
}
else
{
lean_object* v_k_948_; lean_object* v_v_949_; size_t v___x_950_; size_t v___x_951_; size_t v___x_952_; uint64_t v___x_953_; size_t v_h_954_; size_t v___x_955_; lean_object* v___x_956_; size_t v___x_957_; size_t v___x_958_; size_t v___x_959_; size_t v_h_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v_k_948_ = lean_array_fget_borrowed(v_keys_942_, v_i_944_);
v_v_949_ = lean_array_fget_borrowed(v_vals_943_, v_i_944_);
v___x_950_ = lean_ptr_addr(v_k_948_);
v___x_951_ = ((size_t)3ULL);
v___x_952_ = lean_usize_shift_right(v___x_950_, v___x_951_);
v___x_953_ = lean_usize_to_uint64(v___x_952_);
v_h_954_ = lean_uint64_to_usize(v___x_953_);
v___x_955_ = ((size_t)5ULL);
v___x_956_ = lean_unsigned_to_nat(1u);
v___x_957_ = ((size_t)1ULL);
v___x_958_ = lean_usize_sub(v_depth_941_, v___x_957_);
v___x_959_ = lean_usize_mul(v___x_955_, v___x_958_);
v_h_960_ = lean_usize_shift_right(v_h_954_, v___x_959_);
v___x_961_ = lean_nat_add(v_i_944_, v___x_956_);
lean_dec(v_i_944_);
lean_inc(v_v_949_);
lean_inc(v_k_948_);
v___x_962_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_entries_945_, v_h_960_, v_depth_941_, v_k_948_, v_v_949_);
v_i_944_ = v___x_961_;
v_entries_945_ = v___x_962_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_964_, lean_object* v_keys_965_, lean_object* v_vals_966_, lean_object* v_i_967_, lean_object* v_entries_968_){
_start:
{
size_t v_depth_boxed_969_; lean_object* v_res_970_; 
v_depth_boxed_969_ = lean_unbox_usize(v_depth_964_);
lean_dec(v_depth_964_);
v_res_970_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(v_depth_boxed_969_, v_keys_965_, v_vals_966_, v_i_967_, v_entries_968_);
lean_dec_ref(v_vals_966_);
lean_dec_ref(v_keys_965_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg___boxed(lean_object* v_x_971_, lean_object* v_x_972_, lean_object* v_x_973_, lean_object* v_x_974_, lean_object* v_x_975_){
_start:
{
size_t v_x_27465__boxed_976_; size_t v_x_27466__boxed_977_; lean_object* v_res_978_; 
v_x_27465__boxed_976_ = lean_unbox_usize(v_x_972_);
lean_dec(v_x_972_);
v_x_27466__boxed_977_ = lean_unbox_usize(v_x_973_);
lean_dec(v_x_973_);
v_res_978_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_x_971_, v_x_27465__boxed_976_, v_x_27466__boxed_977_, v_x_974_, v_x_975_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg(lean_object* v_x_979_, lean_object* v_x_980_, lean_object* v_x_981_){
_start:
{
size_t v___x_982_; size_t v___x_983_; size_t v___x_984_; uint64_t v___x_985_; size_t v___x_986_; size_t v___x_987_; lean_object* v___x_988_; 
v___x_982_ = lean_ptr_addr(v_x_980_);
v___x_983_ = ((size_t)3ULL);
v___x_984_ = lean_usize_shift_right(v___x_982_, v___x_983_);
v___x_985_ = lean_usize_to_uint64(v___x_984_);
v___x_986_ = lean_uint64_to_usize(v___x_985_);
v___x_987_ = ((size_t)1ULL);
v___x_988_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_x_979_, v___x_986_, v___x_987_, v_x_980_, v_x_981_);
return v___x_988_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0(void){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_989_ = lean_unsigned_to_nat(32u);
v___x_990_ = lean_mk_empty_array_with_capacity(v___x_989_);
v___x_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
return v___x_991_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1(void){
_start:
{
size_t v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_992_ = ((size_t)5ULL);
v___x_993_ = lean_unsigned_to_nat(0u);
v___x_994_ = lean_unsigned_to_nat(32u);
v___x_995_ = lean_mk_empty_array_with_capacity(v___x_994_);
v___x_996_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0);
v___x_997_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_997_, 0, v___x_996_);
lean_ctor_set(v___x_997_, 1, v___x_995_);
lean_ctor_set(v___x_997_, 2, v___x_993_);
lean_ctor_set(v___x_997_, 3, v___x_993_);
lean_ctor_set_usize(v___x_997_, 4, v___x_992_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0(lean_object* v_expr_998_, lean_object* v_size_999_, lean_object* v_s_1000_){
_start:
{
lean_object* v_vars_1001_; lean_object* v_varMap_1002_; lean_object* v_varsHistory_1003_; lean_object* v_natToIntMap_1004_; lean_object* v_natDef_1005_; lean_object* v_dvds_1006_; lean_object* v_lowers_1007_; lean_object* v_uppers_1008_; lean_object* v_diseqs_1009_; lean_object* v_elimEqs_1010_; lean_object* v_elimStack_1011_; lean_object* v_occurs_1012_; lean_object* v_assignment_1013_; lean_object* v_nextCnstrId_1014_; uint8_t v_caseSplits_1015_; lean_object* v_steps_1016_; lean_object* v_conflict_x3f_1017_; lean_object* v_diseqSplits_1018_; lean_object* v_divMod_1019_; uint8_t v_usedCommRing_1020_; lean_object* v_nonlinearOccs_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1039_; 
v_vars_1001_ = lean_ctor_get(v_s_1000_, 0);
v_varMap_1002_ = lean_ctor_get(v_s_1000_, 1);
v_varsHistory_1003_ = lean_ctor_get(v_s_1000_, 2);
v_natToIntMap_1004_ = lean_ctor_get(v_s_1000_, 3);
v_natDef_1005_ = lean_ctor_get(v_s_1000_, 4);
v_dvds_1006_ = lean_ctor_get(v_s_1000_, 5);
v_lowers_1007_ = lean_ctor_get(v_s_1000_, 6);
v_uppers_1008_ = lean_ctor_get(v_s_1000_, 7);
v_diseqs_1009_ = lean_ctor_get(v_s_1000_, 8);
v_elimEqs_1010_ = lean_ctor_get(v_s_1000_, 9);
v_elimStack_1011_ = lean_ctor_get(v_s_1000_, 10);
v_occurs_1012_ = lean_ctor_get(v_s_1000_, 11);
v_assignment_1013_ = lean_ctor_get(v_s_1000_, 12);
v_nextCnstrId_1014_ = lean_ctor_get(v_s_1000_, 13);
v_caseSplits_1015_ = lean_ctor_get_uint8(v_s_1000_, sizeof(void*)*19);
v_steps_1016_ = lean_ctor_get(v_s_1000_, 14);
v_conflict_x3f_1017_ = lean_ctor_get(v_s_1000_, 15);
v_diseqSplits_1018_ = lean_ctor_get(v_s_1000_, 16);
v_divMod_1019_ = lean_ctor_get(v_s_1000_, 17);
v_usedCommRing_1020_ = lean_ctor_get_uint8(v_s_1000_, sizeof(void*)*19 + 1);
v_nonlinearOccs_1021_ = lean_ctor_get(v_s_1000_, 18);
v_isSharedCheck_1039_ = !lean_is_exclusive(v_s_1000_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1023_ = v_s_1000_;
v_isShared_1024_ = v_isSharedCheck_1039_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_nonlinearOccs_1021_);
lean_inc(v_divMod_1019_);
lean_inc(v_diseqSplits_1018_);
lean_inc(v_conflict_x3f_1017_);
lean_inc(v_steps_1016_);
lean_inc(v_nextCnstrId_1014_);
lean_inc(v_assignment_1013_);
lean_inc(v_occurs_1012_);
lean_inc(v_elimStack_1011_);
lean_inc(v_elimEqs_1010_);
lean_inc(v_diseqs_1009_);
lean_inc(v_uppers_1008_);
lean_inc(v_lowers_1007_);
lean_inc(v_dvds_1006_);
lean_inc(v_natDef_1005_);
lean_inc(v_natToIntMap_1004_);
lean_inc(v_varsHistory_1003_);
lean_inc(v_varMap_1002_);
lean_inc(v_vars_1001_);
lean_dec(v_s_1000_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1039_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1037_; 
lean_inc_ref(v_expr_998_);
v___x_1025_ = l_Lean_PersistentArray_push___redArg(v_vars_1001_, v_expr_998_);
v___x_1026_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg(v_varMap_1002_, v_expr_998_, v_size_999_);
v___x_1027_ = lean_box(0);
v___x_1028_ = l_Lean_PersistentArray_push___redArg(v_dvds_1006_, v___x_1027_);
v___x_1029_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1);
v___x_1030_ = l_Lean_PersistentArray_push___redArg(v_lowers_1007_, v___x_1029_);
v___x_1031_ = l_Lean_PersistentArray_push___redArg(v_uppers_1008_, v___x_1029_);
v___x_1032_ = l_Lean_PersistentArray_push___redArg(v_diseqs_1009_, v___x_1029_);
v___x_1033_ = l_Lean_PersistentArray_push___redArg(v_elimEqs_1010_, v___x_1027_);
v___x_1034_ = lean_box(1);
v___x_1035_ = l_Lean_PersistentArray_push___redArg(v_occurs_1012_, v___x_1034_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 11, v___x_1035_);
lean_ctor_set(v___x_1023_, 9, v___x_1033_);
lean_ctor_set(v___x_1023_, 8, v___x_1032_);
lean_ctor_set(v___x_1023_, 7, v___x_1031_);
lean_ctor_set(v___x_1023_, 6, v___x_1030_);
lean_ctor_set(v___x_1023_, 5, v___x_1028_);
lean_ctor_set(v___x_1023_, 1, v___x_1026_);
lean_ctor_set(v___x_1023_, 0, v___x_1025_);
v___x_1037_ = v___x_1023_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1025_);
lean_ctor_set(v_reuseFailAlloc_1038_, 1, v___x_1026_);
lean_ctor_set(v_reuseFailAlloc_1038_, 2, v_varsHistory_1003_);
lean_ctor_set(v_reuseFailAlloc_1038_, 3, v_natToIntMap_1004_);
lean_ctor_set(v_reuseFailAlloc_1038_, 4, v_natDef_1005_);
lean_ctor_set(v_reuseFailAlloc_1038_, 5, v___x_1028_);
lean_ctor_set(v_reuseFailAlloc_1038_, 6, v___x_1030_);
lean_ctor_set(v_reuseFailAlloc_1038_, 7, v___x_1031_);
lean_ctor_set(v_reuseFailAlloc_1038_, 8, v___x_1032_);
lean_ctor_set(v_reuseFailAlloc_1038_, 9, v___x_1033_);
lean_ctor_set(v_reuseFailAlloc_1038_, 10, v_elimStack_1011_);
lean_ctor_set(v_reuseFailAlloc_1038_, 11, v___x_1035_);
lean_ctor_set(v_reuseFailAlloc_1038_, 12, v_assignment_1013_);
lean_ctor_set(v_reuseFailAlloc_1038_, 13, v_nextCnstrId_1014_);
lean_ctor_set(v_reuseFailAlloc_1038_, 14, v_steps_1016_);
lean_ctor_set(v_reuseFailAlloc_1038_, 15, v_conflict_x3f_1017_);
lean_ctor_set(v_reuseFailAlloc_1038_, 16, v_diseqSplits_1018_);
lean_ctor_set(v_reuseFailAlloc_1038_, 17, v_divMod_1019_);
lean_ctor_set(v_reuseFailAlloc_1038_, 18, v_nonlinearOccs_1021_);
lean_ctor_set_uint8(v_reuseFailAlloc_1038_, sizeof(void*)*19, v_caseSplits_1015_);
lean_ctor_set_uint8(v_reuseFailAlloc_1038_, sizeof(void*)*19 + 1, v_usedCommRing_1020_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1040_, lean_object* v_vals_1041_, lean_object* v_i_1042_, lean_object* v_k_1043_){
_start:
{
lean_object* v___x_1044_; uint8_t v___x_1045_; 
v___x_1044_ = lean_array_get_size(v_keys_1040_);
v___x_1045_ = lean_nat_dec_lt(v_i_1042_, v___x_1044_);
if (v___x_1045_ == 0)
{
lean_object* v___x_1046_; 
lean_dec(v_i_1042_);
v___x_1046_ = lean_box(0);
return v___x_1046_;
}
else
{
lean_object* v_k_x27_1047_; size_t v___x_1048_; size_t v___x_1049_; uint8_t v___x_1050_; 
v_k_x27_1047_ = lean_array_fget_borrowed(v_keys_1040_, v_i_1042_);
v___x_1048_ = lean_ptr_addr(v_k_1043_);
v___x_1049_ = lean_ptr_addr(v_k_x27_1047_);
v___x_1050_ = lean_usize_dec_eq(v___x_1048_, v___x_1049_);
if (v___x_1050_ == 0)
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = lean_unsigned_to_nat(1u);
v___x_1052_ = lean_nat_add(v_i_1042_, v___x_1051_);
lean_dec(v_i_1042_);
v_i_1042_ = v___x_1052_;
goto _start;
}
else
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1054_ = lean_array_fget_borrowed(v_vals_1041_, v_i_1042_);
lean_dec(v_i_1042_);
lean_inc(v___x_1054_);
v___x_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
return v___x_1055_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1056_, lean_object* v_vals_1057_, lean_object* v_i_1058_, lean_object* v_k_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(v_keys_1056_, v_vals_1057_, v_i_1058_, v_k_1059_);
lean_dec_ref(v_k_1059_);
lean_dec_ref(v_vals_1057_);
lean_dec_ref(v_keys_1056_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(lean_object* v_x_1061_, size_t v_x_1062_, lean_object* v_x_1063_){
_start:
{
if (lean_obj_tag(v_x_1061_) == 0)
{
lean_object* v_es_1064_; lean_object* v___x_1065_; size_t v___x_1066_; size_t v___x_1067_; lean_object* v_j_1068_; lean_object* v___x_1069_; 
v_es_1064_ = lean_ctor_get(v_x_1061_, 0);
v___x_1065_ = lean_box(2);
v___x_1066_ = ((size_t)31ULL);
v___x_1067_ = lean_usize_land(v_x_1062_, v___x_1066_);
v_j_1068_ = lean_usize_to_nat(v___x_1067_);
v___x_1069_ = lean_array_get_borrowed(v___x_1065_, v_es_1064_, v_j_1068_);
lean_dec(v_j_1068_);
switch(lean_obj_tag(v___x_1069_))
{
case 0:
{
lean_object* v_key_1070_; lean_object* v_val_1071_; size_t v___x_1072_; size_t v___x_1073_; uint8_t v___x_1074_; 
v_key_1070_ = lean_ctor_get(v___x_1069_, 0);
v_val_1071_ = lean_ctor_get(v___x_1069_, 1);
v___x_1072_ = lean_ptr_addr(v_x_1063_);
v___x_1073_ = lean_ptr_addr(v_key_1070_);
v___x_1074_ = lean_usize_dec_eq(v___x_1072_, v___x_1073_);
if (v___x_1074_ == 0)
{
lean_object* v___x_1075_; 
v___x_1075_ = lean_box(0);
return v___x_1075_;
}
else
{
lean_object* v___x_1076_; 
lean_inc(v_val_1071_);
v___x_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1076_, 0, v_val_1071_);
return v___x_1076_;
}
}
case 1:
{
lean_object* v_node_1077_; size_t v___x_1078_; size_t v___x_1079_; 
v_node_1077_ = lean_ctor_get(v___x_1069_, 0);
v___x_1078_ = ((size_t)5ULL);
v___x_1079_ = lean_usize_shift_right(v_x_1062_, v___x_1078_);
v_x_1061_ = v_node_1077_;
v_x_1062_ = v___x_1079_;
goto _start;
}
default: 
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_box(0);
return v___x_1081_;
}
}
}
else
{
lean_object* v_ks_1082_; lean_object* v_vs_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v_ks_1082_ = lean_ctor_get(v_x_1061_, 0);
v_vs_1083_ = lean_ctor_get(v_x_1061_, 1);
v___x_1084_ = lean_unsigned_to_nat(0u);
v___x_1085_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(v_ks_1082_, v_vs_1083_, v___x_1084_, v_x_1063_);
return v___x_1085_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg___boxed(lean_object* v_x_1086_, lean_object* v_x_1087_, lean_object* v_x_1088_){
_start:
{
size_t v_x_27730__boxed_1089_; lean_object* v_res_1090_; 
v_x_27730__boxed_1089_ = lean_unbox_usize(v_x_1087_);
lean_dec(v_x_1087_);
v_res_1090_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(v_x_1086_, v_x_27730__boxed_1089_, v_x_1088_);
lean_dec_ref(v_x_1088_);
lean_dec_ref(v_x_1086_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(lean_object* v_x_1091_, lean_object* v_x_1092_){
_start:
{
size_t v___x_1093_; size_t v___x_1094_; size_t v___x_1095_; uint64_t v___x_1096_; size_t v___x_1097_; lean_object* v___x_1098_; 
v___x_1093_ = lean_ptr_addr(v_x_1092_);
v___x_1094_ = ((size_t)3ULL);
v___x_1095_ = lean_usize_shift_right(v___x_1093_, v___x_1094_);
v___x_1096_ = lean_usize_to_uint64(v___x_1095_);
v___x_1097_ = lean_uint64_to_usize(v___x_1096_);
v___x_1098_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(v_x_1091_, v___x_1097_, v_x_1092_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg___boxed(lean_object* v_x_1099_, lean_object* v_x_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(v_x_1099_, v_x_1100_);
lean_dec_ref(v_x_1100_);
lean_dec_ref(v_x_1099_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4(lean_object* v_msgData_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v___x_1108_; lean_object* v_env_1109_; uint8_t v___x_1110_; lean_object* v_env_1111_; lean_object* v___x_1112_; lean_object* v_toCold_1113_; lean_object* v_mctx_1114_; lean_object* v_lctx_1115_; lean_object* v_options_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1108_ = lean_st_ref_get(v___y_1106_);
v_env_1109_ = lean_ctor_get(v___x_1108_, 0);
lean_inc_ref(v_env_1109_);
lean_dec(v___x_1108_);
v___x_1110_ = 0;
v_env_1111_ = l_Lean_Environment_setRecordingDeps(v_env_1109_, v___x_1110_);
v___x_1112_ = lean_st_ref_get(v___y_1104_);
v_toCold_1113_ = lean_ctor_get(v___y_1105_, 0);
v_mctx_1114_ = lean_ctor_get(v___x_1112_, 0);
lean_inc_ref(v_mctx_1114_);
lean_dec(v___x_1112_);
v_lctx_1115_ = lean_ctor_get(v___y_1103_, 2);
v_options_1116_ = lean_ctor_get(v_toCold_1113_, 2);
lean_inc_ref(v_options_1116_);
lean_inc_ref(v_lctx_1115_);
v___x_1117_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1117_, 0, v_env_1111_);
lean_ctor_set(v___x_1117_, 1, v_mctx_1114_);
lean_ctor_set(v___x_1117_, 2, v_lctx_1115_);
lean_ctor_set(v___x_1117_, 3, v_options_1116_);
v___x_1118_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
lean_ctor_set(v___x_1118_, 1, v_msgData_1102_);
v___x_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4___boxed(lean_object* v_msgData_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4(v_msgData_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
return v_res_1126_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1127_; double v___x_1128_; 
v___x_1127_ = lean_unsigned_to_nat(0u);
v___x_1128_ = lean_float_of_nat(v___x_1127_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(lean_object* v_cls_1132_, lean_object* v_msg_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v_ref_1139_; lean_object* v___x_1140_; lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1186_; 
v_ref_1139_ = lean_ctor_get(v___y_1136_, 2);
v___x_1140_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4(v_msg_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1143_ = v___x_1140_;
v_isShared_1144_ = v_isSharedCheck_1186_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1140_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1186_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1145_; lean_object* v_traceState_1146_; lean_object* v_env_1147_; lean_object* v_nextMacroScope_1148_; lean_object* v_ngen_1149_; lean_object* v_auxDeclNGen_1150_; lean_object* v_cache_1151_; lean_object* v_recordedDeps_1152_; lean_object* v_messages_1153_; lean_object* v_infoState_1154_; lean_object* v_snapshotTasks_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1185_; 
v___x_1145_ = lean_st_ref_take(v___y_1137_);
v_traceState_1146_ = lean_ctor_get(v___x_1145_, 4);
v_env_1147_ = lean_ctor_get(v___x_1145_, 0);
v_nextMacroScope_1148_ = lean_ctor_get(v___x_1145_, 1);
v_ngen_1149_ = lean_ctor_get(v___x_1145_, 2);
v_auxDeclNGen_1150_ = lean_ctor_get(v___x_1145_, 3);
v_cache_1151_ = lean_ctor_get(v___x_1145_, 5);
v_recordedDeps_1152_ = lean_ctor_get(v___x_1145_, 6);
v_messages_1153_ = lean_ctor_get(v___x_1145_, 7);
v_infoState_1154_ = lean_ctor_get(v___x_1145_, 8);
v_snapshotTasks_1155_ = lean_ctor_get(v___x_1145_, 9);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1157_ = v___x_1145_;
v_isShared_1158_ = v_isSharedCheck_1185_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_snapshotTasks_1155_);
lean_inc(v_infoState_1154_);
lean_inc(v_messages_1153_);
lean_inc(v_recordedDeps_1152_);
lean_inc(v_cache_1151_);
lean_inc(v_traceState_1146_);
lean_inc(v_auxDeclNGen_1150_);
lean_inc(v_ngen_1149_);
lean_inc(v_nextMacroScope_1148_);
lean_inc(v_env_1147_);
lean_dec(v___x_1145_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1185_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
uint64_t v_tid_1159_; lean_object* v_traces_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1184_; 
v_tid_1159_ = lean_ctor_get_uint64(v_traceState_1146_, sizeof(void*)*1);
v_traces_1160_ = lean_ctor_get(v_traceState_1146_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v_traceState_1146_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1162_ = v_traceState_1146_;
v_isShared_1163_ = v_isSharedCheck_1184_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_traces_1160_);
lean_dec(v_traceState_1146_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1184_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; double v___x_1166_; uint8_t v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1175_; 
v___x_1164_ = lean_box(0);
v___x_1165_ = lean_box(0);
v___x_1166_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0);
v___x_1167_ = 0;
v___x_1168_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__1));
v___x_1169_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1169_, 0, v_cls_1132_);
lean_ctor_set(v___x_1169_, 1, v___x_1165_);
lean_ctor_set(v___x_1169_, 2, v___x_1168_);
lean_ctor_set_float(v___x_1169_, sizeof(void*)*3, v___x_1166_);
lean_ctor_set_float(v___x_1169_, sizeof(void*)*3 + 8, v___x_1166_);
lean_ctor_set_uint8(v___x_1169_, sizeof(void*)*3 + 16, v___x_1167_);
v___x_1170_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__2));
v___x_1171_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1169_);
lean_ctor_set(v___x_1171_, 1, v_a_1141_);
lean_ctor_set(v___x_1171_, 2, v___x_1170_);
lean_inc(v_ref_1139_);
v___x_1172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1172_, 0, v_ref_1139_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
v___x_1173_ = l_Lean_PersistentArray_push___redArg(v_traces_1160_, v___x_1172_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 0, v___x_1173_);
v___x_1175_ = v___x_1162_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v___x_1173_);
lean_ctor_set_uint64(v_reuseFailAlloc_1183_, sizeof(void*)*1, v_tid_1159_);
v___x_1175_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
lean_object* v___x_1177_; 
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 4, v___x_1175_);
v___x_1177_ = v___x_1157_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_env_1147_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v_nextMacroScope_1148_);
lean_ctor_set(v_reuseFailAlloc_1182_, 2, v_ngen_1149_);
lean_ctor_set(v_reuseFailAlloc_1182_, 3, v_auxDeclNGen_1150_);
lean_ctor_set(v_reuseFailAlloc_1182_, 4, v___x_1175_);
lean_ctor_set(v_reuseFailAlloc_1182_, 5, v_cache_1151_);
lean_ctor_set(v_reuseFailAlloc_1182_, 6, v_recordedDeps_1152_);
lean_ctor_set(v_reuseFailAlloc_1182_, 7, v_messages_1153_);
lean_ctor_set(v_reuseFailAlloc_1182_, 8, v_infoState_1154_);
lean_ctor_set(v_reuseFailAlloc_1182_, 9, v_snapshotTasks_1155_);
v___x_1177_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
lean_object* v___x_1178_; lean_object* v___x_1180_; 
v___x_1178_ = lean_st_ref_put(v___y_1137_, v___x_1177_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 0, v___x_1164_);
v___x_1180_ = v___x_1143_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1164_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___boxed(lean_object* v_cls_1187_, lean_object* v_msg_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(v_cls_1187_, v_msg_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
return v_res_1194_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7(void){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1207_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4));
v___x_1208_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__6));
v___x_1209_ = l_Lean_Name_append(v___x_1208_, v___x_1207_);
return v___x_1209_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9(void){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__8));
v___x_1212_ = l_Lean_stringToMessageData(v___x_1211_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* lean_grind_cutsat_mk_var(lean_object* v_expr_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_){
_start:
{
lean_object* v___x_1225_; 
v___x_1225_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1214_, v_a_1222_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1355_; 
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1355_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1228_ = v___x_1225_;
v_isShared_1229_ = v_isSharedCheck_1355_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1225_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1355_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v_varMap_1230_; lean_object* v___x_1231_; 
v_varMap_1230_ = lean_ctor_get(v_a_1226_, 1);
lean_inc_ref(v_varMap_1230_);
lean_dec(v_a_1226_);
v___x_1231_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(v_varMap_1230_, v_expr_1213_);
lean_dec_ref(v_varMap_1230_);
if (lean_obj_tag(v___x_1231_) == 1)
{
lean_object* v_val_1232_; lean_object* v___x_1234_; 
lean_dec(v_a_1223_);
lean_dec_ref(v_a_1222_);
lean_dec(v_a_1221_);
lean_dec_ref(v_a_1220_);
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec_ref(v_a_1216_);
lean_dec(v_a_1215_);
lean_dec(v_a_1214_);
lean_dec_ref(v_expr_1213_);
v_val_1232_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_val_1232_);
lean_dec_ref_known(v___x_1231_, 1);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 0, v_val_1232_);
v___x_1234_ = v___x_1228_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_val_1232_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
else
{
lean_object* v___x_1236_; 
lean_dec(v___x_1231_);
lean_del_object(v___x_1228_);
v___x_1236_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1214_, v_a_1222_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_a_1237_; lean_object* v_vars_1238_; lean_object* v_toCold_1239_; lean_object* v_options_1240_; lean_object* v_size_1241_; lean_object* v_inheritedTraceOptions_1242_; uint8_t v_hasTrace_1243_; lean_object* v___f_1244_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; 
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_a_1237_);
lean_dec_ref_known(v___x_1236_, 1);
v_vars_1238_ = lean_ctor_get(v_a_1237_, 0);
lean_inc_ref(v_vars_1238_);
lean_dec(v_a_1237_);
v_toCold_1239_ = lean_ctor_get(v_a_1222_, 0);
v_options_1240_ = lean_ctor_get(v_toCold_1239_, 2);
v_size_1241_ = lean_ctor_get(v_vars_1238_, 2);
lean_inc_n(v_size_1241_, 2);
lean_dec_ref(v_vars_1238_);
v_inheritedTraceOptions_1242_ = lean_ctor_get(v_toCold_1239_, 11);
v_hasTrace_1243_ = lean_ctor_get_uint8(v_options_1240_, sizeof(void*)*1);
lean_inc_ref(v_expr_1213_);
v___f_1244_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0), 3, 2);
lean_closure_set(v___f_1244_, 0, v_expr_1213_);
lean_closure_set(v___f_1244_, 1, v_size_1241_);
if (v_hasTrace_1243_ == 0)
{
v___y_1246_ = v_a_1214_;
v___y_1247_ = v_a_1215_;
v___y_1248_ = v_a_1216_;
v___y_1249_ = v_a_1217_;
v___y_1250_ = v_a_1218_;
v___y_1251_ = v_a_1219_;
v___y_1252_ = v_a_1220_;
v___y_1253_ = v_a_1221_;
v___y_1254_ = v_a_1222_;
v___y_1255_ = v_a_1223_;
goto v___jp_1245_;
}
else
{
lean_object* v___x_1328_; lean_object* v___x_1329_; uint8_t v___x_1330_; 
v___x_1328_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4));
v___x_1329_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7);
v___x_1330_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1242_, v_options_1240_, v___x_1329_);
if (v___x_1330_ == 0)
{
v___y_1246_ = v_a_1214_;
v___y_1247_ = v_a_1215_;
v___y_1248_ = v_a_1216_;
v___y_1249_ = v_a_1217_;
v___y_1250_ = v_a_1218_;
v___y_1251_ = v_a_1219_;
v___y_1252_ = v_a_1220_;
v___y_1253_ = v_a_1221_;
v___y_1254_ = v_a_1222_;
v___y_1255_ = v_a_1223_;
goto v___jp_1245_;
}
else
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
lean_inc_ref(v_expr_1213_);
v___x_1331_ = l_Lean_MessageData_ofExpr(v_expr_1213_);
v___x_1332_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9);
v___x_1333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1331_);
lean_ctor_set(v___x_1333_, 1, v___x_1332_);
lean_inc(v_size_1241_);
v___x_1334_ = l_Nat_reprFast(v_size_1241_);
v___x_1335_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
v___x_1336_ = l_Lean_MessageData_ofFormat(v___x_1335_);
v___x_1337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1333_);
lean_ctor_set(v___x_1337_, 1, v___x_1336_);
v___x_1338_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(v___x_1328_, v___x_1337_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_dec_ref_known(v___x_1338_, 1);
v___y_1246_ = v_a_1214_;
v___y_1247_ = v_a_1215_;
v___y_1248_ = v_a_1216_;
v___y_1249_ = v_a_1217_;
v___y_1250_ = v_a_1218_;
v___y_1251_ = v_a_1219_;
v___y_1252_ = v_a_1220_;
v___y_1253_ = v_a_1221_;
v___y_1254_ = v_a_1222_;
v___y_1255_ = v_a_1223_;
goto v___jp_1245_;
}
else
{
lean_object* v_a_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1346_; 
lean_dec_ref(v___f_1244_);
lean_dec(v_size_1241_);
lean_dec(v_a_1223_);
lean_dec_ref(v_a_1222_);
lean_dec(v_a_1221_);
lean_dec_ref(v_a_1220_);
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec_ref(v_a_1216_);
lean_dec(v_a_1215_);
lean_dec(v_a_1214_);
lean_dec_ref(v_expr_1213_);
v_a_1339_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1341_ = v___x_1338_;
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_a_1339_);
lean_dec(v___x_1338_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1344_; 
if (v_isShared_1342_ == 0)
{
v___x_1344_ = v___x_1341_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_a_1339_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
}
v___jp_1245_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1256_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_1257_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1256_, v___f_1244_, v___y_1246_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v___x_1258_; 
lean_dec_ref_known(v___x_1257_, 1);
lean_inc_ref(v_expr_1213_);
v___x_1258_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_1256_, v_expr_1213_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v___x_1259_; 
lean_dec_ref_known(v___x_1258_, 1);
lean_inc(v_size_1241_);
lean_inc_ref(v_expr_1213_);
v___x_1259_ = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(v_expr_1213_, v_size_1241_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v___x_1260_; 
lean_dec_ref_known(v___x_1259_, 1);
lean_inc(v_size_1241_);
lean_inc_ref(v_expr_1213_);
v___x_1260_ = l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg(v_expr_1213_, v_size_1241_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v___x_1261_; 
lean_dec_ref_known(v___x_1260_, 1);
lean_inc_ref(v_expr_1213_);
v___x_1261_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm(v_expr_1213_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1287_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1264_ = v___x_1261_;
v_isShared_1265_ = v_isSharedCheck_1287_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1261_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1287_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
uint8_t v___x_1266_; 
v___x_1266_ = lean_unbox(v_a_1262_);
lean_dec(v_a_1262_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1268_; 
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v_expr_1213_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 0, v_size_1241_);
v___x_1268_ = v___x_1264_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_size_1241_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
else
{
lean_object* v___x_1270_; 
lean_del_object(v___x_1264_);
lean_inc(v_size_1241_);
v___x_1270_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt(v_expr_1213_, v_size_1241_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec(v___y_1246_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1277_; 
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1277_ == 0)
{
lean_object* v_unused_1278_; 
v_unused_1278_ = lean_ctor_get(v___x_1270_, 0);
lean_dec(v_unused_1278_);
v___x_1272_ = v___x_1270_;
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
else
{
lean_dec(v___x_1270_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 0, v_size_1241_);
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_size_1241_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
else
{
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1286_; 
lean_dec(v_size_1241_);
v_a_1279_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1281_ = v___x_1270_;
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1270_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1284_; 
if (v_isShared_1282_ == 0)
{
v___x_1284_ = v___x_1281_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_a_1279_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
}
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec(v_size_1241_);
lean_dec_ref(v_expr_1213_);
v_a_1288_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1261_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1261_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec(v_size_1241_);
lean_dec_ref(v_expr_1213_);
v_a_1296_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1260_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1260_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec(v_size_1241_);
lean_dec_ref(v_expr_1213_);
v_a_1304_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1259_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1259_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
else
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1319_; 
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec(v_size_1241_);
lean_dec_ref(v_expr_1213_);
v_a_1312_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1314_ = v___x_1258_;
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1258_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1317_; 
if (v_isShared_1315_ == 0)
{
v___x_1317_ = v___x_1314_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_a_1312_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1327_; 
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec(v_size_1241_);
lean_dec_ref(v_expr_1213_);
v_a_1320_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1322_ = v___x_1257_;
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1257_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1325_; 
if (v_isShared_1323_ == 0)
{
v___x_1325_ = v___x_1322_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1320_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
}
else
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1354_; 
lean_dec(v_a_1223_);
lean_dec_ref(v_a_1222_);
lean_dec(v_a_1221_);
lean_dec_ref(v_a_1220_);
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec_ref(v_a_1216_);
lean_dec(v_a_1215_);
lean_dec(v_a_1214_);
lean_dec_ref(v_expr_1213_);
v_a_1347_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1349_ = v___x_1236_;
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1236_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1352_; 
if (v_isShared_1350_ == 0)
{
v___x_1352_ = v___x_1349_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1347_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
}
}
}
else
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1363_; 
lean_dec(v_a_1223_);
lean_dec_ref(v_a_1222_);
lean_dec(v_a_1221_);
lean_dec_ref(v_a_1220_);
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec_ref(v_a_1216_);
lean_dec(v_a_1215_);
lean_dec(v_a_1214_);
lean_dec_ref(v_expr_1213_);
v_a_1356_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1358_ = v___x_1225_;
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1225_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___boxed(lean_object* v_expr_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = lean_grind_cutsat_mk_var(v_expr_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0(lean_object* v_00_u03b2_1377_, lean_object* v_x_1378_, lean_object* v_x_1379_){
_start:
{
lean_object* v___x_1380_; 
v___x_1380_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(v_x_1378_, v_x_1379_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___boxed(lean_object* v_00_u03b2_1381_, lean_object* v_x_1382_, lean_object* v_x_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0(v_00_u03b2_1381_, v_x_1382_, v_x_1383_);
lean_dec_ref(v_x_1383_);
lean_dec_ref(v_x_1382_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1(lean_object* v_00_u03b2_1385_, lean_object* v_x_1386_, lean_object* v_x_1387_, lean_object* v_x_1388_){
_start:
{
lean_object* v___x_1389_; 
v___x_1389_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg(v_x_1386_, v_x_1387_, v_x_1388_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2(lean_object* v_cls_1390_, lean_object* v_msg_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v___x_1403_; 
v___x_1403_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(v_cls_1390_, v_msg_1391_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___boxed(lean_object* v_cls_1404_, lean_object* v_msg_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2(v_cls_1404_, v_msg_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec(v___y_1407_);
lean_dec(v___y_1406_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0(lean_object* v_00_u03b2_1418_, lean_object* v_x_1419_, size_t v_x_1420_, lean_object* v_x_1421_){
_start:
{
lean_object* v___x_1422_; 
v___x_1422_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(v_x_1419_, v_x_1420_, v_x_1421_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1423_, lean_object* v_x_1424_, lean_object* v_x_1425_, lean_object* v_x_1426_){
_start:
{
size_t v_x_28305__boxed_1427_; lean_object* v_res_1428_; 
v_x_28305__boxed_1427_ = lean_unbox_usize(v_x_1425_);
lean_dec(v_x_1425_);
v_res_1428_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0(v_00_u03b2_1423_, v_x_1424_, v_x_28305__boxed_1427_, v_x_1426_);
lean_dec_ref(v_x_1426_);
lean_dec_ref(v_x_1424_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2(lean_object* v_00_u03b2_1429_, lean_object* v_x_1430_, size_t v_x_1431_, size_t v_x_1432_, lean_object* v_x_1433_, lean_object* v_x_1434_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_x_1430_, v_x_1431_, v_x_1432_, v_x_1433_, v_x_1434_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1436_, lean_object* v_x_1437_, lean_object* v_x_1438_, lean_object* v_x_1439_, lean_object* v_x_1440_, lean_object* v_x_1441_){
_start:
{
size_t v_x_28316__boxed_1442_; size_t v_x_28317__boxed_1443_; lean_object* v_res_1444_; 
v_x_28316__boxed_1442_ = lean_unbox_usize(v_x_1438_);
lean_dec(v_x_1438_);
v_x_28317__boxed_1443_ = lean_unbox_usize(v_x_1439_);
lean_dec(v_x_1439_);
v_res_1444_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2(v_00_u03b2_1436_, v_x_1437_, v_x_28316__boxed_1442_, v_x_28317__boxed_1443_, v_x_1440_, v_x_1441_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1445_, lean_object* v_keys_1446_, lean_object* v_vals_1447_, lean_object* v_heq_1448_, lean_object* v_i_1449_, lean_object* v_k_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(v_keys_1446_, v_vals_1447_, v_i_1449_, v_k_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1452_, lean_object* v_keys_1453_, lean_object* v_vals_1454_, lean_object* v_heq_1455_, lean_object* v_i_1456_, lean_object* v_k_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1(v_00_u03b2_1452_, v_keys_1453_, v_vals_1454_, v_heq_1455_, v_i_1456_, v_k_1457_);
lean_dec_ref(v_k_1457_);
lean_dec_ref(v_vals_1454_);
lean_dec_ref(v_keys_1453_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1459_, lean_object* v_n_1460_, lean_object* v_k_1461_, lean_object* v_v_1462_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4___redArg(v_n_1460_, v_k_1461_, v_v_1462_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1464_, size_t v_depth_1465_, lean_object* v_keys_1466_, lean_object* v_vals_1467_, lean_object* v_heq_1468_, lean_object* v_i_1469_, lean_object* v_entries_1470_){
_start:
{
lean_object* v___x_1471_; 
v___x_1471_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(v_depth_1465_, v_keys_1466_, v_vals_1467_, v_i_1469_, v_entries_1470_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1472_, lean_object* v_depth_1473_, lean_object* v_keys_1474_, lean_object* v_vals_1475_, lean_object* v_heq_1476_, lean_object* v_i_1477_, lean_object* v_entries_1478_){
_start:
{
size_t v_depth_boxed_1479_; lean_object* v_res_1480_; 
v_depth_boxed_1479_ = lean_unbox_usize(v_depth_1473_);
lean_dec(v_depth_1473_);
v_res_1480_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5(v_00_u03b2_1472_, v_depth_boxed_1479_, v_keys_1474_, v_vals_1475_, v_heq_1476_, v_i_1477_, v_entries_1478_);
lean_dec_ref(v_vals_1475_);
lean_dec_ref(v_keys_1474_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_1481_, lean_object* v_x_1482_, lean_object* v_x_1483_, lean_object* v_x_1484_, lean_object* v_x_1485_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7___redArg(v_x_1482_, v_x_1483_, v_x_1484_, v_x_1485_);
return v___x_1486_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2(void){
_start:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1490_ = lean_box(0);
v___x_1491_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__1));
v___x_1492_ = l_Lean_mkConst(v___x_1491_, v___x_1490_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(lean_object* v_e_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_){
_start:
{
lean_object* v___x_1499_; 
lean_inc(v_a_1497_);
lean_inc_ref(v_a_1496_);
lean_inc(v_a_1495_);
lean_inc_ref(v_a_1494_);
v___x_1499_ = lean_infer_type(v_e_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v_a_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_a_1500_);
lean_dec_ref_known(v___x_1499_, 1);
v___x_1501_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2);
v___x_1502_ = l_Lean_Meta_isExprDefEq(v_a_1500_, v___x_1501_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_);
return v___x_1502_;
}
else
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1510_; 
v_a_1503_ = lean_ctor_get(v___x_1499_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1505_ = v___x_1499_;
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1499_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1508_; 
if (v_isShared_1506_ == 0)
{
v___x_1508_ = v___x_1505_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_a_1503_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___boxed(lean_object* v_e_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(v_e_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_);
lean_dec(v_a_1515_);
lean_dec_ref(v_a_1514_);
lean_dec(v_a_1513_);
lean_dec_ref(v_a_1512_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt(lean_object* v_e_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(v_e_1518_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___boxed(lean_object* v_e_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l_Lean_Meta_Grind_Arith_Cutsat_isInt(v_e_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_);
lean_dec(v_a_1541_);
lean_dec_ref(v_a_1540_);
lean_dec(v_a_1539_);
lean_dec_ref(v_a_1538_);
lean_dec(v_a_1537_);
lean_dec_ref(v_a_1536_);
lean_dec(v_a_1535_);
lean_dec_ref(v_a_1534_);
lean_dec(v_a_1533_);
lean_dec(v_a_1532_);
return v_res_1543_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4(void){
_start:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1550_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__3));
v___x_1551_ = l_Lean_stringToMessageData(v___x_1550_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(lean_object* v_e_1552_, uint8_t v_report_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_){
_start:
{
lean_object* v___x_1567_; 
lean_inc_ref(v_e_1552_);
v___x_1567_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1552_, v_a_1557_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v___x_1569_; uint8_t v___x_1570_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_a_1568_);
lean_dec_ref_known(v___x_1567_, 1);
v___x_1569_ = l_Lean_Expr_cleanupAnnotations(v_a_1568_);
v___x_1570_ = l_Lean_Expr_isApp(v___x_1569_);
if (v___x_1570_ == 0)
{
lean_dec_ref(v___x_1569_);
lean_dec_ref(v_e_1552_);
goto v___jp_1561_;
}
else
{
lean_object* v_arg_1571_; lean_object* v___x_1572_; uint8_t v___x_1573_; 
v_arg_1571_ = lean_ctor_get(v___x_1569_, 1);
lean_inc_ref(v_arg_1571_);
v___x_1572_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1569_);
v___x_1573_ = l_Lean_Expr_isApp(v___x_1572_);
if (v___x_1573_ == 0)
{
lean_dec_ref(v___x_1572_);
lean_dec_ref(v_arg_1571_);
lean_dec_ref(v_e_1552_);
goto v___jp_1561_;
}
else
{
lean_object* v_arg_1574_; lean_object* v___x_1575_; uint8_t v___x_1576_; 
v_arg_1574_ = lean_ctor_get(v___x_1572_, 1);
lean_inc_ref(v_arg_1574_);
v___x_1575_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1572_);
v___x_1576_ = l_Lean_Expr_isApp(v___x_1575_);
if (v___x_1576_ == 0)
{
lean_dec_ref(v___x_1575_);
lean_dec_ref(v_arg_1574_);
lean_dec_ref(v_arg_1571_);
lean_dec_ref(v_e_1552_);
goto v___jp_1561_;
}
else
{
lean_object* v_arg_1577_; lean_object* v___x_1578_; uint8_t v___x_1579_; 
v_arg_1577_ = lean_ctor_get(v___x_1575_, 1);
lean_inc_ref(v_arg_1577_);
v___x_1578_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1575_);
v___x_1579_ = l_Lean_Expr_isApp(v___x_1578_);
if (v___x_1579_ == 0)
{
lean_dec_ref(v___x_1578_);
lean_dec_ref(v_arg_1577_);
lean_dec_ref(v_arg_1574_);
lean_dec_ref(v_arg_1571_);
lean_dec_ref(v_e_1552_);
goto v___jp_1561_;
}
else
{
lean_object* v___x_1580_; uint8_t v___x_1581_; 
v___x_1580_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1578_);
v___x_1581_ = l_Lean_Expr_isApp(v___x_1580_);
if (v___x_1581_ == 0)
{
lean_dec_ref(v___x_1580_);
lean_dec_ref(v_arg_1577_);
lean_dec_ref(v_arg_1574_);
lean_dec_ref(v_arg_1571_);
lean_dec_ref(v_e_1552_);
goto v___jp_1561_;
}
else
{
lean_object* v___x_1582_; uint8_t v___x_1583_; 
v___x_1582_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1580_);
v___x_1583_ = l_Lean_Expr_isApp(v___x_1582_);
if (v___x_1583_ == 0)
{
lean_dec_ref(v___x_1582_);
lean_dec_ref(v_arg_1577_);
lean_dec_ref(v_arg_1574_);
lean_dec_ref(v_arg_1571_);
lean_dec_ref(v_e_1552_);
goto v___jp_1561_;
}
else
{
lean_object* v___x_1584_; lean_object* v___x_1585_; uint8_t v___x_1586_; 
v___x_1584_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1582_);
v___x_1585_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__2));
v___x_1586_ = l_Lean_Expr_isConstOf(v___x_1584_, v___x_1585_);
lean_dec_ref(v___x_1584_);
if (v___x_1586_ == 0)
{
lean_dec_ref(v_arg_1577_);
lean_dec_ref(v_arg_1574_);
lean_dec_ref(v_arg_1571_);
lean_dec_ref(v_e_1552_);
goto v___jp_1561_;
}
else
{
lean_object* v___x_1587_; 
v___x_1587_ = l_Lean_Meta_Structural_isInstHAddInt___redArg(v_arg_1577_, v_a_1557_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1621_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1590_ = v___x_1587_;
v_isShared_1591_ = v_isSharedCheck_1621_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1587_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1621_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
uint8_t v___x_1592_; 
v___x_1592_ = lean_unbox(v_a_1588_);
lean_dec(v_a_1588_);
if (v___x_1592_ == 0)
{
lean_del_object(v___x_1590_);
lean_dec_ref(v_arg_1574_);
lean_dec_ref(v_arg_1571_);
if (v_report_1553_ == 0)
{
lean_dec_ref(v_e_1552_);
goto v___jp_1564_;
}
else
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1593_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4);
v___x_1594_ = l_Lean_indentExpr(v_e_1552_);
v___x_1595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1593_);
lean_ctor_set(v___x_1595_, 1, v___x_1594_);
v___x_1596_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1554_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_object* v_a_1597_; uint8_t v_verbose_1598_; 
v_a_1597_ = lean_ctor_get(v___x_1596_, 0);
lean_inc(v_a_1597_);
lean_dec_ref_known(v___x_1596_, 1);
v_verbose_1598_ = lean_ctor_get_uint8(v_a_1597_, 0);
lean_dec(v_a_1597_);
if (v_verbose_1598_ == 0)
{
lean_dec_ref_known(v___x_1595_, 2);
goto v___jp_1564_;
}
else
{
lean_object* v___x_1599_; 
v___x_1599_ = l_Lean_Meta_Sym_reportIssue(v___x_1595_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_dec_ref_known(v___x_1599_, 1);
goto v___jp_1564_;
}
else
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1607_; 
v_a_1600_ = lean_ctor_get(v___x_1599_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1602_ = v___x_1599_;
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1599_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1607_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1605_; 
if (v_isShared_1603_ == 0)
{
v___x_1605_ = v___x_1602_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1600_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
}
else
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1615_; 
lean_dec_ref_known(v___x_1595_, 2);
v_a_1608_ = lean_ctor_get(v___x_1596_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1610_ = v___x_1596_;
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1596_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1613_; 
if (v_isShared_1611_ == 0)
{
v___x_1613_ = v___x_1610_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_a_1608_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
}
else
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1619_; 
lean_dec_ref(v_e_1552_);
v___x_1616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1616_, 0, v_arg_1574_);
lean_ctor_set(v___x_1616_, 1, v_arg_1571_);
v___x_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1616_);
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 0, v___x_1617_);
v___x_1619_ = v___x_1590_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1617_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
lean_dec_ref(v_arg_1574_);
lean_dec_ref(v_arg_1571_);
lean_dec_ref(v_e_1552_);
v_a_1622_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1587_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1587_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
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
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1637_; 
lean_dec_ref(v_e_1552_);
v_a_1630_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1632_ = v___x_1567_;
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1567_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1637_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1635_; 
if (v_isShared_1633_ == 0)
{
v___x_1635_ = v___x_1632_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
v___jp_1561_:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1562_ = lean_box(0);
v___x_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
return v___x_1563_;
}
v___jp_1564_:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1565_ = lean_box(0);
v___x_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
return v___x_1566_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___boxed(lean_object* v_e_1638_, lean_object* v_report_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_){
_start:
{
uint8_t v_report_boxed_1647_; lean_object* v_res_1648_; 
v_report_boxed_1647_ = lean_unbox(v_report_1639_);
v_res_1648_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_1638_, v_report_boxed_1647_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_);
lean_dec(v_a_1645_);
lean_dec_ref(v_a_1644_);
lean_dec(v_a_1643_);
lean_dec_ref(v_a_1642_);
lean_dec(v_a_1641_);
lean_dec_ref(v_a_1640_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f(lean_object* v_e_1649_, uint8_t v_report_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_1649_, v_report_1650_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___boxed(lean_object* v_e_1663_, lean_object* v_report_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_){
_start:
{
uint8_t v_report_boxed_1676_; lean_object* v_res_1677_; 
v_report_boxed_1676_ = lean_unbox(v_report_1664_);
v_res_1677_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f(v_e_1663_, v_report_boxed_1676_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_);
lean_dec(v_a_1674_);
lean_dec_ref(v_a_1673_);
lean_dec(v_a_1672_);
lean_dec_ref(v_a_1671_);
lean_dec(v_a_1670_);
lean_dec_ref(v_a_1669_);
lean_dec(v_a_1668_);
lean_dec_ref(v_a_1667_);
lean_dec(v_a_1666_);
lean_dec(v_a_1665_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(lean_object* v_e_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_){
_start:
{
uint8_t v___x_1686_; lean_object* v___x_1687_; 
v___x_1686_ = 0;
v___x_1687_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_1678_, v___x_1686_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1701_; 
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1690_ = v___x_1687_;
v_isShared_1691_ = v_isSharedCheck_1701_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1687_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1701_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
if (lean_obj_tag(v_a_1688_) == 0)
{
lean_object* v___x_1692_; lean_object* v___x_1694_; 
v___x_1692_ = lean_box(v___x_1686_);
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 0, v___x_1692_);
v___x_1694_ = v___x_1690_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v___x_1692_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
else
{
uint8_t v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1699_; 
lean_dec_ref_known(v_a_1688_, 1);
v___x_1696_ = 1;
v___x_1697_ = lean_box(v___x_1696_);
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 0, v___x_1697_);
v___x_1699_ = v___x_1690_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v___x_1697_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
v_a_1702_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1687_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1687_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1702_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg___boxed(lean_object* v_e_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(v_e_1710_, v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_, v_a_1716_);
lean_dec(v_a_1716_);
lean_dec_ref(v_a_1715_);
lean_dec(v_a_1714_);
lean_dec_ref(v_a_1713_);
lean_dec(v_a_1712_);
lean_dec_ref(v_a_1711_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd(lean_object* v_e_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(v_e_1719_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___boxed(lean_object* v_e_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd(v_e_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_);
lean_dec(v_a_1742_);
lean_dec_ref(v_a_1741_);
lean_dec(v_a_1740_);
lean_dec_ref(v_a_1739_);
lean_dec(v_a_1738_);
lean_dec_ref(v_a_1737_);
lean_dec(v_a_1736_);
lean_dec_ref(v_a_1735_);
lean_dec(v_a_1734_);
lean_dec(v_a_1733_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(lean_object* v_e_1745_, uint8_t v_report_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_){
_start:
{
lean_object* v___x_1760_; 
lean_inc_ref(v_e_1745_);
v___x_1760_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1745_, v_a_1750_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v_a_1761_; lean_object* v___x_1762_; uint8_t v___x_1763_; 
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
lean_inc(v_a_1761_);
lean_dec_ref_known(v___x_1760_, 1);
v___x_1762_ = l_Lean_Expr_cleanupAnnotations(v_a_1761_);
v___x_1763_ = l_Lean_Expr_isApp(v___x_1762_);
if (v___x_1763_ == 0)
{
lean_dec_ref(v___x_1762_);
lean_dec_ref(v_e_1745_);
goto v___jp_1754_;
}
else
{
lean_object* v_arg_1764_; lean_object* v___x_1765_; uint8_t v___x_1766_; 
v_arg_1764_ = lean_ctor_get(v___x_1762_, 1);
lean_inc_ref(v_arg_1764_);
v___x_1765_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1762_);
v___x_1766_ = l_Lean_Expr_isApp(v___x_1765_);
if (v___x_1766_ == 0)
{
lean_dec_ref(v___x_1765_);
lean_dec_ref(v_arg_1764_);
lean_dec_ref(v_e_1745_);
goto v___jp_1754_;
}
else
{
lean_object* v_arg_1767_; lean_object* v___x_1768_; uint8_t v___x_1769_; 
v_arg_1767_ = lean_ctor_get(v___x_1765_, 1);
lean_inc_ref(v_arg_1767_);
v___x_1768_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1765_);
v___x_1769_ = l_Lean_Expr_isApp(v___x_1768_);
if (v___x_1769_ == 0)
{
lean_dec_ref(v___x_1768_);
lean_dec_ref(v_arg_1767_);
lean_dec_ref(v_arg_1764_);
lean_dec_ref(v_e_1745_);
goto v___jp_1754_;
}
else
{
lean_object* v_arg_1770_; lean_object* v___x_1771_; uint8_t v___x_1772_; 
v_arg_1770_ = lean_ctor_get(v___x_1768_, 1);
lean_inc_ref(v_arg_1770_);
v___x_1771_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1768_);
v___x_1772_ = l_Lean_Expr_isApp(v___x_1771_);
if (v___x_1772_ == 0)
{
lean_dec_ref(v___x_1771_);
lean_dec_ref(v_arg_1770_);
lean_dec_ref(v_arg_1767_);
lean_dec_ref(v_arg_1764_);
lean_dec_ref(v_e_1745_);
goto v___jp_1754_;
}
else
{
lean_object* v___x_1773_; uint8_t v___x_1774_; 
v___x_1773_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1771_);
v___x_1774_ = l_Lean_Expr_isApp(v___x_1773_);
if (v___x_1774_ == 0)
{
lean_dec_ref(v___x_1773_);
lean_dec_ref(v_arg_1770_);
lean_dec_ref(v_arg_1767_);
lean_dec_ref(v_arg_1764_);
lean_dec_ref(v_e_1745_);
goto v___jp_1754_;
}
else
{
lean_object* v___x_1775_; uint8_t v___x_1776_; 
v___x_1775_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1773_);
v___x_1776_ = l_Lean_Expr_isApp(v___x_1775_);
if (v___x_1776_ == 0)
{
lean_dec_ref(v___x_1775_);
lean_dec_ref(v_arg_1770_);
lean_dec_ref(v_arg_1767_);
lean_dec_ref(v_arg_1764_);
lean_dec_ref(v_e_1745_);
goto v___jp_1754_;
}
else
{
lean_object* v___x_1777_; lean_object* v___x_1778_; uint8_t v___x_1779_; 
v___x_1777_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1775_);
v___x_1778_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11));
v___x_1779_ = l_Lean_Expr_isConstOf(v___x_1777_, v___x_1778_);
lean_dec_ref(v___x_1777_);
if (v___x_1779_ == 0)
{
lean_dec_ref(v_arg_1770_);
lean_dec_ref(v_arg_1767_);
lean_dec_ref(v_arg_1764_);
lean_dec_ref(v_e_1745_);
goto v___jp_1754_;
}
else
{
lean_object* v___x_1780_; 
v___x_1780_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_1770_, v_a_1750_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_object* v_a_1781_; uint8_t v___x_1782_; 
v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
lean_inc(v_a_1781_);
lean_dec_ref_known(v___x_1780_, 1);
v___x_1782_ = lean_unbox(v_a_1781_);
lean_dec(v_a_1781_);
if (v___x_1782_ == 0)
{
lean_dec_ref(v_arg_1767_);
lean_dec_ref(v_arg_1764_);
if (v_report_1746_ == 0)
{
lean_dec_ref(v_e_1745_);
goto v___jp_1757_;
}
else
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1783_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4);
v___x_1784_ = l_Lean_indentExpr(v_e_1745_);
v___x_1785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1783_);
lean_ctor_set(v___x_1785_, 1, v___x_1784_);
v___x_1786_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1747_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v_a_1787_; uint8_t v_verbose_1788_; 
v_a_1787_ = lean_ctor_get(v___x_1786_, 0);
lean_inc(v_a_1787_);
lean_dec_ref_known(v___x_1786_, 1);
v_verbose_1788_ = lean_ctor_get_uint8(v_a_1787_, 0);
lean_dec(v_a_1787_);
if (v_verbose_1788_ == 0)
{
lean_dec_ref_known(v___x_1785_, 2);
goto v___jp_1757_;
}
else
{
lean_object* v___x_1789_; 
v___x_1789_ = l_Lean_Meta_Sym_reportIssue(v___x_1785_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_dec_ref_known(v___x_1789_, 1);
goto v___jp_1757_;
}
else
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1797_; 
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1792_ = v___x_1789_;
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1789_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1795_; 
if (v_isShared_1793_ == 0)
{
v___x_1795_ = v___x_1792_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_a_1790_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
}
}
else
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1805_; 
lean_dec_ref_known(v___x_1785_, 2);
v_a_1798_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1800_ = v___x_1786_;
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1786_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1803_; 
if (v_isShared_1801_ == 0)
{
v___x_1803_ = v___x_1800_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1798_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
}
}
else
{
lean_object* v___x_1806_; 
lean_dec_ref(v_e_1745_);
v___x_1806_ = l_Lean_Meta_getIntValue_x3f(v_arg_1767_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1827_; 
v_a_1807_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1809_ = v___x_1806_;
v_isShared_1810_ = v_isSharedCheck_1827_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1806_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1827_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
if (lean_obj_tag(v_a_1807_) == 1)
{
lean_object* v_val_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1822_; 
v_val_1811_ = lean_ctor_get(v_a_1807_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v_a_1807_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1813_ = v_a_1807_;
v_isShared_1814_ = v_isSharedCheck_1822_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_val_1811_);
lean_dec(v_a_1807_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1822_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1815_; lean_object* v___x_1817_; 
v___x_1815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1815_, 0, v_val_1811_);
lean_ctor_set(v___x_1815_, 1, v_arg_1764_);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 0, v___x_1815_);
v___x_1817_ = v___x_1813_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v___x_1815_);
v___x_1817_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
lean_object* v___x_1819_; 
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 0, v___x_1817_);
v___x_1819_ = v___x_1809_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1817_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
}
else
{
lean_object* v___x_1823_; lean_object* v___x_1825_; 
lean_dec(v_a_1807_);
lean_dec_ref(v_arg_1764_);
v___x_1823_ = lean_box(0);
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 0, v___x_1823_);
v___x_1825_ = v___x_1809_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1823_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
else
{
lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1835_; 
lean_dec_ref(v_arg_1764_);
v_a_1828_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1830_ = v___x_1806_;
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v___x_1806_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1833_; 
if (v_isShared_1831_ == 0)
{
v___x_1833_ = v___x_1830_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_a_1828_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
}
}
else
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1843_; 
lean_dec_ref(v_arg_1767_);
lean_dec_ref(v_arg_1764_);
lean_dec_ref(v_e_1745_);
v_a_1836_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1838_ = v___x_1780_;
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1780_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1839_ == 0)
{
v___x_1841_ = v___x_1838_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_a_1836_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
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
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1851_; 
lean_dec_ref(v_e_1745_);
v_a_1844_ = lean_ctor_get(v___x_1760_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1846_ = v___x_1760_;
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1760_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1849_; 
if (v_isShared_1847_ == 0)
{
v___x_1849_ = v___x_1846_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_a_1844_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
v___jp_1754_:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1755_ = lean_box(0);
v___x_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
return v___x_1756_;
}
v___jp_1757_:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1758_ = lean_box(0);
v___x_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
return v___x_1759_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg___boxed(lean_object* v_e_1852_, lean_object* v_report_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_){
_start:
{
uint8_t v_report_boxed_1861_; lean_object* v_res_1862_; 
v_report_boxed_1861_ = lean_unbox(v_report_1853_);
v_res_1862_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1852_, v_report_boxed_1861_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_);
lean_dec(v_a_1859_);
lean_dec_ref(v_a_1858_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec(v_a_1855_);
lean_dec_ref(v_a_1854_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f(lean_object* v_e_1863_, uint8_t v_report_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1863_, v_report_1864_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___boxed(lean_object* v_e_1877_, lean_object* v_report_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_){
_start:
{
uint8_t v_report_boxed_1890_; lean_object* v_res_1891_; 
v_report_boxed_1890_ = lean_unbox(v_report_1878_);
v_res_1891_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f(v_e_1877_, v_report_boxed_1890_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_);
lean_dec(v_a_1888_);
lean_dec_ref(v_a_1887_);
lean_dec(v_a_1886_);
lean_dec_ref(v_a_1885_);
lean_dec(v_a_1884_);
lean_dec_ref(v_a_1883_);
lean_dec(v_a_1882_);
lean_dec_ref(v_a_1881_);
lean_dec(v_a_1880_);
lean_dec(v_a_1879_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(lean_object* v_e_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_){
_start:
{
uint8_t v___x_1900_; lean_object* v___x_1901_; 
v___x_1900_ = 0;
v___x_1901_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1892_, v___x_1900_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1915_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1904_ = v___x_1901_;
v_isShared_1905_ = v_isSharedCheck_1915_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1901_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1915_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
if (lean_obj_tag(v_a_1902_) == 0)
{
lean_object* v___x_1906_; lean_object* v___x_1908_; 
v___x_1906_ = lean_box(v___x_1900_);
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 0, v___x_1906_);
v___x_1908_ = v___x_1904_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v___x_1906_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
else
{
uint8_t v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1913_; 
lean_dec_ref_known(v_a_1902_, 1);
v___x_1910_ = 1;
v___x_1911_ = lean_box(v___x_1910_);
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 0, v___x_1911_);
v___x_1913_ = v___x_1904_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1911_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
else
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1923_; 
v_a_1916_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1918_ = v___x_1901_;
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1901_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1919_ == 0)
{
v___x_1921_ = v___x_1918_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1916_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg___boxed(lean_object* v_e_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(v_e_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_);
lean_dec(v_a_1930_);
lean_dec_ref(v_a_1929_);
lean_dec(v_a_1928_);
lean_dec_ref(v_a_1927_);
lean_dec(v_a_1926_);
lean_dec_ref(v_a_1925_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul(lean_object* v_e_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(v_e_1933_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___boxed(lean_object* v_e_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul(v_e_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_);
lean_dec(v_a_1956_);
lean_dec_ref(v_a_1955_);
lean_dec(v_a_1954_);
lean_dec_ref(v_a_1953_);
lean_dec(v_a_1952_);
lean_dec_ref(v_a_1951_);
lean_dec(v_a_1950_);
lean_dec_ref(v_a_1949_);
lean_dec(v_a_1948_);
lean_dec(v_a_1947_);
return v_res_1958_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0(void){
_start:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1959_ = lean_unsigned_to_nat(1u);
v___x_1960_ = lean_nat_to_int(v___x_1959_);
return v___x_1960_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2(void){
_start:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1962_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__1));
v___x_1963_ = l_Lean_stringToMessageData(v___x_1962_);
return v___x_1963_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4(void){
_start:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1965_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__3));
v___x_1966_ = l_Lean_stringToMessageData(v___x_1965_);
return v___x_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(lean_object* v_e_1967_, lean_object* v_p_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_){
_start:
{
lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; uint8_t v___x_2010_; lean_object* v___x_2011_; 
v___x_2010_ = 1;
lean_inc_ref(v_e_1967_);
v___x_2011_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1967_, v___x_2010_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_object* v_a_2012_; 
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_a_2012_);
lean_dec_ref_known(v___x_2011_, 1);
if (lean_obj_tag(v_a_2012_) == 1)
{
lean_object* v_val_2013_; lean_object* v_fst_2014_; lean_object* v_snd_2015_; lean_object* v___x_2016_; 
lean_dec_ref(v_e_1967_);
v_val_2013_ = lean_ctor_get(v_a_2012_, 0);
lean_inc(v_val_2013_);
lean_dec_ref_known(v_a_2012_, 1);
v_fst_2014_ = lean_ctor_get(v_val_2013_, 0);
lean_inc(v_fst_2014_);
v_snd_2015_ = lean_ctor_get(v_val_2013_, 1);
lean_inc(v_snd_2015_);
lean_dec(v_val_2013_);
lean_inc(v_a_1978_);
lean_inc_ref(v_a_1977_);
lean_inc(v_a_1976_);
lean_inc_ref(v_a_1975_);
lean_inc(v_a_1974_);
lean_inc_ref(v_a_1973_);
lean_inc(v_a_1972_);
lean_inc_ref(v_a_1971_);
lean_inc(v_a_1970_);
lean_inc(v_a_1969_);
v___x_2016_ = lean_grind_cutsat_mk_var(v_snd_2015_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2025_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2019_ = v___x_2016_;
v_isShared_2020_ = v_isSharedCheck_2025_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2016_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2025_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2021_; lean_object* v___x_2023_; 
v___x_2021_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2021_, 0, v_fst_2014_);
lean_ctor_set(v___x_2021_, 1, v_a_2017_);
lean_ctor_set(v___x_2021_, 2, v_p_1968_);
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 0, v___x_2021_);
v___x_2023_ = v___x_2019_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_2021_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
else
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
lean_dec(v_fst_2014_);
lean_dec_ref(v_p_1968_);
v_a_2026_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2028_ = v___x_2016_;
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_2016_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2029_ == 0)
{
v___x_2031_ = v___x_2028_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2026_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
}
else
{
lean_object* v___x_2034_; 
lean_dec(v_a_2012_);
lean_inc_ref(v_e_1967_);
v___x_2034_ = l_Lean_Meta_getIntValue_x3f(v_e_1967_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2076_; 
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2037_ = v___x_2034_;
v_isShared_2038_ = v_isSharedCheck_2076_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_2034_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2076_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
if (lean_obj_tag(v_a_2035_) == 1)
{
lean_object* v_val_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2075_; 
v_val_2039_ = lean_ctor_get(v_a_2035_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v_a_2035_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2041_ = v_a_2035_;
v_isShared_2042_ = v_isSharedCheck_2075_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_val_2039_);
lean_dec(v_a_2035_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2075_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
uint8_t v___x_2043_; 
v___x_2043_ = l_Int_Internal_Linear_Poly_isZero(v_p_1968_);
if (v___x_2043_ == 0)
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
lean_del_object(v___x_2041_);
lean_dec(v_val_2039_);
lean_del_object(v___x_2037_);
v___x_2044_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2);
lean_inc_ref(v_e_1967_);
v___x_2045_ = l_Lean_indentExpr(v_e_1967_);
v___x_2046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2044_);
lean_ctor_set(v___x_2046_, 1, v___x_2045_);
v___x_2047_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4);
v___x_2048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2046_);
lean_ctor_set(v___x_2048_, 1, v___x_2047_);
v___x_2049_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1973_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; uint8_t v_verbose_2051_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2050_);
lean_dec_ref_known(v___x_2049_, 1);
v_verbose_2051_ = lean_ctor_get_uint8(v_a_2050_, 0);
lean_dec(v_a_2050_);
if (v_verbose_2051_ == 0)
{
lean_dec_ref_known(v___x_2048_, 2);
v___y_1981_ = v_a_1969_;
v___y_1982_ = v_a_1970_;
v___y_1983_ = v_a_1971_;
v___y_1984_ = v_a_1972_;
v___y_1985_ = v_a_1973_;
v___y_1986_ = v_a_1974_;
v___y_1987_ = v_a_1975_;
v___y_1988_ = v_a_1976_;
v___y_1989_ = v_a_1977_;
v___y_1990_ = v_a_1978_;
goto v___jp_1980_;
}
else
{
lean_object* v___x_2052_; 
v___x_2052_ = l_Lean_Meta_Sym_reportIssue(v___x_2048_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_dec_ref_known(v___x_2052_, 1);
v___y_1981_ = v_a_1969_;
v___y_1982_ = v_a_1970_;
v___y_1983_ = v_a_1971_;
v___y_1984_ = v_a_1972_;
v___y_1985_ = v_a_1973_;
v___y_1986_ = v_a_1974_;
v___y_1987_ = v_a_1975_;
v___y_1988_ = v_a_1976_;
v___y_1989_ = v_a_1977_;
v___y_1990_ = v_a_1978_;
goto v___jp_1980_;
}
else
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
lean_dec_ref(v_p_1968_);
lean_dec_ref(v_e_1967_);
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___x_2052_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_2052_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
}
else
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
lean_dec_ref_known(v___x_2048_, 2);
lean_dec_ref(v_p_1968_);
lean_dec_ref(v_e_1967_);
v_a_2061_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_2049_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2049_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_a_2061_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
else
{
lean_object* v___x_2070_; 
lean_dec_ref(v_p_1968_);
lean_dec_ref(v_e_1967_);
if (v_isShared_2042_ == 0)
{
lean_ctor_set_tag(v___x_2041_, 0);
v___x_2070_ = v___x_2041_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_val_2039_);
v___x_2070_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
lean_object* v___x_2072_; 
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 0, v___x_2070_);
v___x_2072_ = v___x_2037_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2070_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
}
else
{
lean_del_object(v___x_2037_);
lean_dec(v_a_2035_);
v___y_1981_ = v_a_1969_;
v___y_1982_ = v_a_1970_;
v___y_1983_ = v_a_1971_;
v___y_1984_ = v_a_1972_;
v___y_1985_ = v_a_1973_;
v___y_1986_ = v_a_1974_;
v___y_1987_ = v_a_1975_;
v___y_1988_ = v_a_1976_;
v___y_1989_ = v_a_1977_;
v___y_1990_ = v_a_1978_;
goto v___jp_1980_;
}
}
}
else
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2084_; 
lean_dec_ref(v_p_1968_);
lean_dec_ref(v_e_1967_);
v_a_2077_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2079_ = v___x_2034_;
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_2034_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2082_; 
if (v_isShared_2080_ == 0)
{
v___x_2082_ = v___x_2079_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_a_2077_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
}
}
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
lean_dec_ref(v_p_1968_);
lean_dec_ref(v_e_1967_);
v_a_2085_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___x_2011_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2011_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2090_; 
if (v_isShared_2088_ == 0)
{
v___x_2090_ = v___x_2087_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_a_2085_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
v___jp_1980_:
{
lean_object* v___x_1991_; 
lean_inc(v___y_1990_);
lean_inc_ref(v___y_1989_);
lean_inc(v___y_1988_);
lean_inc_ref(v___y_1987_);
lean_inc(v___y_1986_);
lean_inc_ref(v___y_1985_);
lean_inc(v___y_1984_);
lean_inc_ref(v___y_1983_);
lean_inc(v___y_1982_);
lean_inc(v___y_1981_);
v___x_1991_ = lean_grind_cutsat_mk_var(v_e_1967_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2001_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1994_ = v___x_1991_;
v_isShared_1995_ = v_isSharedCheck_2001_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1991_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2001_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1999_; 
v___x_1996_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0);
v___x_1997_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1996_);
lean_ctor_set(v___x_1997_, 1, v_a_1992_);
lean_ctor_set(v___x_1997_, 2, v_p_1968_);
if (v_isShared_1995_ == 0)
{
lean_ctor_set(v___x_1994_, 0, v___x_1997_);
v___x_1999_ = v___x_1994_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v___x_1997_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
else
{
lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2009_; 
lean_dec_ref(v_p_1968_);
v_a_2002_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2004_ = v___x_1991_;
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_dec(v___x_1991_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2007_; 
if (v_isShared_2005_ == 0)
{
v___x_2007_ = v___x_2004_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2002_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___boxed(lean_object* v_e_2093_, lean_object* v_p_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_e_2093_, v_p_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_);
lean_dec(v_a_2104_);
lean_dec_ref(v_a_2103_);
lean_dec(v_a_2102_);
lean_dec_ref(v_a_2101_);
lean_dec(v_a_2100_);
lean_dec_ref(v_a_2099_);
lean_dec(v_a_2098_);
lean_dec_ref(v_a_2097_);
lean_dec(v_a_2096_);
lean_dec(v_a_2095_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go(lean_object* v_e_2107_, lean_object* v_p_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_){
_start:
{
uint8_t v___x_2120_; lean_object* v___x_2121_; 
v___x_2120_ = 1;
lean_inc_ref(v_e_2107_);
v___x_2121_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_2107_, v___x_2120_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_a_2122_);
lean_dec_ref_known(v___x_2121_, 1);
if (lean_obj_tag(v_a_2122_) == 1)
{
lean_object* v_val_2123_; lean_object* v_fst_2124_; lean_object* v_snd_2125_; lean_object* v___x_2126_; 
lean_dec_ref(v_e_2107_);
v_val_2123_ = lean_ctor_get(v_a_2122_, 0);
lean_inc(v_val_2123_);
lean_dec_ref_known(v_a_2122_, 1);
v_fst_2124_ = lean_ctor_get(v_val_2123_, 0);
lean_inc(v_fst_2124_);
v_snd_2125_ = lean_ctor_get(v_val_2123_, 1);
lean_inc(v_snd_2125_);
lean_dec(v_val_2123_);
v___x_2126_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_snd_2125_, v_p_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2127_);
lean_dec_ref_known(v___x_2126_, 1);
v_e_2107_ = v_fst_2124_;
v_p_2108_ = v_a_2127_;
goto _start;
}
else
{
lean_dec(v_fst_2124_);
return v___x_2126_;
}
}
else
{
lean_object* v___x_2129_; 
lean_dec(v_a_2122_);
v___x_2129_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_e_2107_, v_p_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_);
return v___x_2129_;
}
}
else
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
lean_dec_ref(v_p_2108_);
lean_dec_ref(v_e_2107_);
v_a_2130_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2132_ = v___x_2121_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2121_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2133_ == 0)
{
v___x_2135_ = v___x_2132_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2130_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go___boxed(lean_object* v_e_2138_, lean_object* v_p_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_){
_start:
{
lean_object* v_res_2151_; 
v_res_2151_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go(v_e_2138_, v_p_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_);
lean_dec(v_a_2149_);
lean_dec_ref(v_a_2148_);
lean_dec(v_a_2147_);
lean_dec_ref(v_a_2146_);
lean_dec(v_a_2145_);
lean_dec_ref(v_a_2144_);
lean_dec(v_a_2143_);
lean_dec_ref(v_a_2142_);
lean_dec(v_a_2141_);
lean_dec(v_a_2140_);
return v_res_2151_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0(void){
_start:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2152_ = lean_unsigned_to_nat(0u);
v___x_2153_ = lean_nat_to_int(v___x_2152_);
return v___x_2153_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1(void){
_start:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2154_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0);
v___x_2155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2154_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly(lean_object* v_e_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_){
_start:
{
uint8_t v___x_2168_; lean_object* v___x_2169_; 
v___x_2168_ = 1;
lean_inc_ref(v_e_2156_);
v___x_2169_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_2156_, v___x_2168_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; 
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
lean_inc(v_a_2170_);
lean_dec_ref_known(v___x_2169_, 1);
if (lean_obj_tag(v_a_2170_) == 1)
{
lean_object* v_val_2171_; lean_object* v_fst_2172_; lean_object* v_snd_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
lean_dec_ref(v_e_2156_);
v_val_2171_ = lean_ctor_get(v_a_2170_, 0);
lean_inc(v_val_2171_);
lean_dec_ref_known(v_a_2170_, 1);
v_fst_2172_ = lean_ctor_get(v_val_2171_, 0);
lean_inc(v_fst_2172_);
v_snd_2173_ = lean_ctor_get(v_val_2171_, 1);
lean_inc(v_snd_2173_);
lean_dec(v_val_2171_);
v___x_2174_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1);
v___x_2175_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_snd_2173_, v___x_2174_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; lean_object* v___x_2177_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_a_2176_);
lean_dec_ref_known(v___x_2175_, 1);
v___x_2177_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go(v_fst_2172_, v_a_2176_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_);
return v___x_2177_;
}
else
{
lean_dec(v_fst_2172_);
return v___x_2175_;
}
}
else
{
lean_object* v___x_2178_; lean_object* v___x_2179_; 
lean_dec(v_a_2170_);
v___x_2178_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1);
v___x_2179_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_e_2156_, v___x_2178_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_);
return v___x_2179_;
}
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
lean_dec_ref(v_e_2156_);
v_a_2180_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2169_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2169_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly___boxed(lean_object* v_e_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_e_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
lean_dec(v_a_2198_);
lean_dec_ref(v_a_2197_);
lean_dec(v_a_2196_);
lean_dec_ref(v_a_2195_);
lean_dec(v_a_2194_);
lean_dec_ref(v_a_2193_);
lean_dec(v_a_2192_);
lean_dec_ref(v_a_2191_);
lean_dec(v_a_2190_);
lean_dec(v_a_2189_);
return v_res_2200_;
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
