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
lean_object* v_a_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_97_; 
v_a_86_ = lean_ctor_get(v___x_85_, 0);
v_isSharedCheck_97_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_97_ == 0)
{
v___x_88_ = v___x_85_;
v_isShared_89_ = v_isSharedCheck_97_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_a_86_);
lean_dec(v___x_85_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_97_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
uint8_t v___y_91_; 
if (lean_obj_tag(v_a_86_) == 0)
{
v___y_91_ = v___x_81_;
goto v___jp_90_;
}
else
{
lean_dec_ref_known(v_a_86_, 1);
v___y_91_ = v___x_79_;
goto v___jp_90_;
}
v___jp_90_:
{
if (v___y_91_ == 0)
{
lean_object* v___x_92_; lean_object* v___x_94_; 
lean_dec_ref(v_arg_68_);
v___x_92_ = lean_box(v___y_91_);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 0, v___x_92_);
v___x_94_ = v___x_88_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v___x_92_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
else
{
lean_object* v___x_96_; 
lean_del_object(v___x_88_);
v___x_96_ = l_Lean_Meta_Structural_isInstHDivInt___redArg(v_arg_68_, v_a_50_);
return v___x_96_;
}
}
}
}
else
{
lean_object* v_a_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_105_; 
lean_dec_ref(v_arg_68_);
v_a_98_ = lean_ctor_get(v___x_85_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_105_ == 0)
{
v___x_100_ = v___x_85_;
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_a_98_);
lean_dec(v___x_85_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_103_; 
if (v_isShared_101_ == 0)
{
v___x_103_ = v___x_100_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_a_98_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
}
}
}
else
{
lean_object* v___x_106_; 
lean_dec_ref(v___x_75_);
v___x_106_ = l_Lean_Meta_getIntValue_x3f(v_arg_62_, v_a_49_, v_a_50_, v_a_51_, v_a_52_);
if (lean_obj_tag(v___x_106_) == 0)
{
lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_118_; 
v_a_107_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_118_ == 0)
{
v___x_109_ = v___x_106_;
v_isShared_110_ = v_isSharedCheck_118_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_dec(v___x_106_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_118_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
uint8_t v___y_112_; 
if (lean_obj_tag(v_a_107_) == 0)
{
v___y_112_ = v___x_79_;
goto v___jp_111_;
}
else
{
lean_dec_ref_known(v_a_107_, 1);
v___y_112_ = v___x_77_;
goto v___jp_111_;
}
v___jp_111_:
{
if (v___y_112_ == 0)
{
lean_object* v___x_113_; lean_object* v___x_115_; 
lean_dec_ref(v_arg_68_);
v___x_113_ = lean_box(v___y_112_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 0, v___x_113_);
v___x_115_ = v___x_109_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v___x_113_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
else
{
lean_object* v___x_117_; 
lean_del_object(v___x_109_);
v___x_117_ = l_Lean_Meta_Structural_isInstHModInt___redArg(v_arg_68_, v_a_50_);
return v___x_117_;
}
}
}
}
else
{
lean_object* v_a_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_126_; 
lean_dec_ref(v_arg_68_);
v_a_119_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_126_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_126_ == 0)
{
v___x_121_ = v___x_106_;
v_isShared_122_ = v_isSharedCheck_126_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_a_119_);
lean_dec(v___x_106_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_126_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_124_; 
if (v_isShared_122_ == 0)
{
v___x_124_ = v___x_121_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_a_119_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
}
}
else
{
lean_object* v___x_127_; 
lean_dec_ref(v___x_75_);
v___x_127_ = l_Lean_Meta_Structural_isInstHPowInt___redArg(v_arg_68_, v_a_50_);
if (lean_obj_tag(v___x_127_) == 0)
{
lean_object* v_a_128_; uint8_t v___x_129_; 
v_a_128_ = lean_ctor_get(v___x_127_, 0);
v___x_129_ = lean_unbox(v_a_128_);
if (v___x_129_ == 0)
{
lean_dec_ref(v_arg_65_);
lean_dec_ref(v_arg_62_);
return v___x_127_;
}
else
{
lean_object* v___x_130_; 
lean_inc(v_a_128_);
lean_dec_ref_known(v___x_127_, 1);
v___x_130_ = l_Lean_Meta_getIntValue_x3f(v_arg_65_, v_a_49_, v_a_50_, v_a_51_, v_a_52_);
if (lean_obj_tag(v___x_130_) == 0)
{
lean_object* v_a_131_; lean_object* v___x_132_; 
v_a_131_ = lean_ctor_get(v___x_130_, 0);
lean_inc(v_a_131_);
lean_dec_ref_known(v___x_130_, 1);
v___x_132_ = l_Lean_Meta_getIntValue_x3f(v_arg_62_, v_a_49_, v_a_50_, v_a_51_, v_a_52_);
if (lean_obj_tag(v___x_132_) == 0)
{
if (lean_obj_tag(v_a_131_) == 0)
{
lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_140_; 
lean_dec(v_a_128_);
v_isSharedCheck_140_ = !lean_is_exclusive(v___x_132_);
if (v_isSharedCheck_140_ == 0)
{
lean_object* v_unused_141_; 
v_unused_141_ = lean_ctor_get(v___x_132_, 0);
lean_dec(v_unused_141_);
v___x_134_ = v___x_132_;
v_isShared_135_ = v_isSharedCheck_140_;
goto v_resetjp_133_;
}
else
{
lean_dec(v___x_132_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_140_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_136_; lean_object* v___x_138_; 
v___x_136_ = lean_box(v___x_77_);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 0, v___x_136_);
v___x_138_ = v___x_134_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v___x_136_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
else
{
lean_object* v_a_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_154_; 
lean_dec_ref_known(v_a_131_, 1);
v_a_142_ = lean_ctor_get(v___x_132_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_132_);
if (v_isSharedCheck_154_ == 0)
{
v___x_144_ = v___x_132_;
v_isShared_145_ = v_isSharedCheck_154_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_a_142_);
lean_dec(v___x_132_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_154_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
if (lean_obj_tag(v_a_142_) == 0)
{
lean_object* v___x_147_; 
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 0, v_a_128_);
v___x_147_ = v___x_144_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_a_128_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
else
{
uint8_t v___x_149_; lean_object* v___x_150_; lean_object* v___x_152_; 
lean_dec_ref_known(v_a_142_, 1);
lean_dec(v_a_128_);
v___x_149_ = 0;
v___x_150_ = lean_box(v___x_149_);
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 0, v___x_150_);
v___x_152_ = v___x_144_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_150_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
}
else
{
lean_object* v_a_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_162_; 
lean_dec(v_a_131_);
lean_dec(v_a_128_);
v_a_155_ = lean_ctor_get(v___x_132_, 0);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_132_);
if (v_isSharedCheck_162_ == 0)
{
v___x_157_ = v___x_132_;
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_a_155_);
lean_dec(v___x_132_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_160_; 
if (v_isShared_158_ == 0)
{
v___x_160_ = v___x_157_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_a_155_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
}
else
{
lean_object* v_a_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_170_; 
lean_dec(v_a_128_);
lean_dec_ref(v_arg_62_);
v_a_163_ = lean_ctor_get(v___x_130_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_170_ == 0)
{
v___x_165_ = v___x_130_;
v_isShared_166_ = v_isSharedCheck_170_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_a_163_);
lean_dec(v___x_130_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_170_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_168_; 
if (v_isShared_166_ == 0)
{
v___x_168_ = v___x_165_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v_a_163_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
}
}
}
else
{
lean_dec_ref(v_arg_65_);
lean_dec_ref(v_arg_62_);
return v___x_127_;
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
lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_178_; 
v_a_171_ = lean_ctor_get(v___x_58_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_58_);
if (v_isSharedCheck_178_ == 0)
{
v___x_173_ = v___x_58_;
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v___x_58_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_176_; 
if (v_isShared_174_ == 0)
{
v___x_176_ = v___x_173_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_a_171_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___boxed(lean_object* v_e_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm(v_e_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_);
lean_dec(v_a_183_);
lean_dec_ref(v_a_182_);
lean_dec(v_a_181_);
lean_dec_ref(v_a_180_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_x_186_, lean_object* v_x_187_, lean_object* v_x_188_, lean_object* v_x_189_){
_start:
{
lean_object* v_ks_190_; lean_object* v_vs_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_215_; 
v_ks_190_ = lean_ctor_get(v_x_186_, 0);
v_vs_191_ = lean_ctor_get(v_x_186_, 1);
v_isSharedCheck_215_ = !lean_is_exclusive(v_x_186_);
if (v_isSharedCheck_215_ == 0)
{
v___x_193_ = v_x_186_;
v_isShared_194_ = v_isSharedCheck_215_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_vs_191_);
lean_inc(v_ks_190_);
lean_dec(v_x_186_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_215_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_195_ = lean_array_get_size(v_ks_190_);
v___x_196_ = lean_nat_dec_lt(v_x_187_, v___x_195_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_200_; 
lean_dec(v_x_187_);
v___x_197_ = lean_array_push(v_ks_190_, v_x_188_);
v___x_198_ = lean_array_push(v_vs_191_, v_x_189_);
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 1, v___x_198_);
lean_ctor_set(v___x_193_, 0, v___x_197_);
v___x_200_ = v___x_193_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_197_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v___x_198_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
else
{
lean_object* v_k_x27_202_; uint8_t v___x_203_; 
v_k_x27_202_ = lean_array_fget_borrowed(v_ks_190_, v_x_187_);
v___x_203_ = lean_nat_dec_eq(v_x_188_, v_k_x27_202_);
if (v___x_203_ == 0)
{
lean_object* v___x_205_; 
if (v_isShared_194_ == 0)
{
v___x_205_ = v___x_193_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_ks_190_);
lean_ctor_set(v_reuseFailAlloc_209_, 1, v_vs_191_);
v___x_205_ = v_reuseFailAlloc_209_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = lean_unsigned_to_nat(1u);
v___x_207_ = lean_nat_add(v_x_187_, v___x_206_);
lean_dec(v_x_187_);
v_x_186_ = v___x_205_;
v_x_187_ = v___x_207_;
goto _start;
}
}
else
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_213_; 
v___x_210_ = lean_array_fset(v_ks_190_, v_x_187_, v_x_188_);
v___x_211_ = lean_array_fset(v_vs_191_, v_x_187_, v_x_189_);
lean_dec(v_x_187_);
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 1, v___x_211_);
lean_ctor_set(v___x_193_, 0, v___x_210_);
v___x_213_ = v___x_193_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_210_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v___x_211_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1___redArg(lean_object* v_n_216_, lean_object* v_k_217_, lean_object* v_v_218_){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = lean_unsigned_to_nat(0u);
v___x_220_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__4___redArg(v_n_216_, v___x_219_, v_k_217_, v_v_218_);
return v___x_220_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(lean_object* v_x_222_, size_t v_x_223_, size_t v_x_224_, lean_object* v_x_225_, lean_object* v_x_226_){
_start:
{
if (lean_obj_tag(v_x_222_) == 0)
{
lean_object* v_es_227_; size_t v___x_228_; size_t v___x_229_; lean_object* v_j_230_; lean_object* v___x_231_; uint8_t v___x_232_; 
v_es_227_ = lean_ctor_get(v_x_222_, 0);
v___x_228_ = ((size_t)31ULL);
v___x_229_ = lean_usize_land(v_x_223_, v___x_228_);
v_j_230_ = lean_usize_to_nat(v___x_229_);
v___x_231_ = lean_array_get_size(v_es_227_);
v___x_232_ = lean_nat_dec_lt(v_j_230_, v___x_231_);
if (v___x_232_ == 0)
{
lean_dec(v_j_230_);
lean_dec(v_x_226_);
lean_dec(v_x_225_);
return v_x_222_;
}
else
{
lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_271_; 
lean_inc_ref(v_es_227_);
v_isSharedCheck_271_ = !lean_is_exclusive(v_x_222_);
if (v_isSharedCheck_271_ == 0)
{
lean_object* v_unused_272_; 
v_unused_272_ = lean_ctor_get(v_x_222_, 0);
lean_dec(v_unused_272_);
v___x_234_ = v_x_222_;
v_isShared_235_ = v_isSharedCheck_271_;
goto v_resetjp_233_;
}
else
{
lean_dec(v_x_222_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_271_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v_v_236_; lean_object* v___x_237_; lean_object* v_xs_x27_238_; lean_object* v___y_240_; 
v_v_236_ = lean_array_fget(v_es_227_, v_j_230_);
v___x_237_ = lean_box(0);
v_xs_x27_238_ = lean_array_fset(v_es_227_, v_j_230_, v___x_237_);
switch(lean_obj_tag(v_v_236_))
{
case 0:
{
lean_object* v_key_245_; lean_object* v_val_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_256_; 
v_key_245_ = lean_ctor_get(v_v_236_, 0);
v_val_246_ = lean_ctor_get(v_v_236_, 1);
v_isSharedCheck_256_ = !lean_is_exclusive(v_v_236_);
if (v_isSharedCheck_256_ == 0)
{
v___x_248_ = v_v_236_;
v_isShared_249_ = v_isSharedCheck_256_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_val_246_);
lean_inc(v_key_245_);
lean_dec(v_v_236_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_256_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
uint8_t v___x_250_; 
v___x_250_ = lean_nat_dec_eq(v_x_225_, v_key_245_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; lean_object* v___x_252_; 
lean_del_object(v___x_248_);
v___x_251_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_245_, v_val_246_, v_x_225_, v_x_226_);
v___x_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
v___y_240_ = v___x_252_;
goto v___jp_239_;
}
else
{
lean_object* v___x_254_; 
lean_dec(v_val_246_);
lean_dec(v_key_245_);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 1, v_x_226_);
lean_ctor_set(v___x_248_, 0, v_x_225_);
v___x_254_ = v___x_248_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_x_225_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v_x_226_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
v___y_240_ = v___x_254_;
goto v___jp_239_;
}
}
}
}
case 1:
{
lean_object* v_node_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_269_; 
v_node_257_ = lean_ctor_get(v_v_236_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v_v_236_);
if (v_isSharedCheck_269_ == 0)
{
v___x_259_ = v_v_236_;
v_isShared_260_ = v_isSharedCheck_269_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_node_257_);
lean_dec(v_v_236_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_269_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
size_t v___x_261_; size_t v___x_262_; size_t v___x_263_; size_t v___x_264_; lean_object* v___x_265_; lean_object* v___x_267_; 
v___x_261_ = ((size_t)5ULL);
v___x_262_ = lean_usize_shift_right(v_x_223_, v___x_261_);
v___x_263_ = ((size_t)1ULL);
v___x_264_ = lean_usize_add(v_x_224_, v___x_263_);
v___x_265_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_node_257_, v___x_262_, v___x_264_, v_x_225_, v_x_226_);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 0, v___x_265_);
v___x_267_ = v___x_259_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_265_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
v___y_240_ = v___x_267_;
goto v___jp_239_;
}
}
}
default: 
{
lean_object* v___x_270_; 
v___x_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_270_, 0, v_x_225_);
lean_ctor_set(v___x_270_, 1, v_x_226_);
v___y_240_ = v___x_270_;
goto v___jp_239_;
}
}
v___jp_239_:
{
lean_object* v___x_241_; lean_object* v___x_243_; 
v___x_241_ = lean_array_fset(v_xs_x27_238_, v_j_230_, v___y_240_);
lean_dec(v_j_230_);
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 0, v___x_241_);
v___x_243_ = v___x_234_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_241_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
}
else
{
lean_object* v_ks_273_; lean_object* v_vs_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_292_; 
v_ks_273_ = lean_ctor_get(v_x_222_, 0);
v_vs_274_ = lean_ctor_get(v_x_222_, 1);
v_isSharedCheck_292_ = !lean_is_exclusive(v_x_222_);
if (v_isSharedCheck_292_ == 0)
{
v___x_276_ = v_x_222_;
v_isShared_277_ = v_isSharedCheck_292_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_vs_274_);
lean_inc(v_ks_273_);
lean_dec(v_x_222_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_292_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
if (v_isShared_277_ == 0)
{
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_ks_273_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v_vs_274_);
v___x_279_ = v_reuseFailAlloc_291_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
lean_object* v_newNode_280_; size_t v___x_281_; uint8_t v___x_282_; 
v_newNode_280_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1___redArg(v___x_279_, v_x_225_, v_x_226_);
v___x_281_ = ((size_t)7ULL);
v___x_282_ = lean_usize_dec_le(v___x_281_, v_x_224_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_283_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_280_);
v___x_284_ = lean_unsigned_to_nat(4u);
v___x_285_ = lean_nat_dec_lt(v___x_283_, v___x_284_);
lean_dec(v___x_283_);
if (v___x_285_ == 0)
{
lean_object* v_ks_286_; lean_object* v_vs_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v_ks_286_ = lean_ctor_get(v_newNode_280_, 0);
lean_inc_ref(v_ks_286_);
v_vs_287_ = lean_ctor_get(v_newNode_280_, 1);
lean_inc_ref(v_vs_287_);
lean_dec_ref(v_newNode_280_);
v___x_288_ = lean_unsigned_to_nat(0u);
v___x_289_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0);
v___x_290_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg(v_x_224_, v_ks_286_, v_vs_287_, v___x_288_, v___x_289_);
lean_dec_ref(v_vs_287_);
lean_dec_ref(v_ks_286_);
return v___x_290_;
}
else
{
return v_newNode_280_;
}
}
else
{
return v_newNode_280_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg(size_t v_depth_293_, lean_object* v_keys_294_, lean_object* v_vals_295_, lean_object* v_i_296_, lean_object* v_entries_297_){
_start:
{
lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_298_ = lean_array_get_size(v_keys_294_);
v___x_299_ = lean_nat_dec_lt(v_i_296_, v___x_298_);
if (v___x_299_ == 0)
{
lean_dec(v_i_296_);
return v_entries_297_;
}
else
{
lean_object* v_k_300_; lean_object* v_v_301_; uint64_t v___x_302_; size_t v_h_303_; size_t v___x_304_; lean_object* v___x_305_; size_t v___x_306_; size_t v___x_307_; size_t v___x_308_; size_t v_h_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v_k_300_ = lean_array_fget_borrowed(v_keys_294_, v_i_296_);
v_v_301_ = lean_array_fget_borrowed(v_vals_295_, v_i_296_);
v___x_302_ = lean_uint64_of_nat(v_k_300_);
v_h_303_ = lean_uint64_to_usize(v___x_302_);
v___x_304_ = ((size_t)5ULL);
v___x_305_ = lean_unsigned_to_nat(1u);
v___x_306_ = ((size_t)1ULL);
v___x_307_ = lean_usize_sub(v_depth_293_, v___x_306_);
v___x_308_ = lean_usize_mul(v___x_304_, v___x_307_);
v_h_309_ = lean_usize_shift_right(v_h_303_, v___x_308_);
v___x_310_ = lean_nat_add(v_i_296_, v___x_305_);
lean_dec(v_i_296_);
lean_inc(v_v_301_);
lean_inc(v_k_300_);
v___x_311_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_entries_297_, v_h_309_, v_depth_293_, v_k_300_, v_v_301_);
v_i_296_ = v___x_310_;
v_entries_297_ = v___x_311_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_313_, lean_object* v_keys_314_, lean_object* v_vals_315_, lean_object* v_i_316_, lean_object* v_entries_317_){
_start:
{
size_t v_depth_boxed_318_; lean_object* v_res_319_; 
v_depth_boxed_318_ = lean_unbox_usize(v_depth_313_);
lean_dec(v_depth_313_);
v_res_319_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg(v_depth_boxed_318_, v_keys_314_, v_vals_315_, v_i_316_, v_entries_317_);
lean_dec_ref(v_vals_315_);
lean_dec_ref(v_keys_314_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___boxed(lean_object* v_x_320_, lean_object* v_x_321_, lean_object* v_x_322_, lean_object* v_x_323_, lean_object* v_x_324_){
_start:
{
size_t v_x_7941__boxed_325_; size_t v_x_7942__boxed_326_; lean_object* v_res_327_; 
v_x_7941__boxed_325_ = lean_unbox_usize(v_x_321_);
lean_dec(v_x_321_);
v_x_7942__boxed_326_ = lean_unbox_usize(v_x_322_);
lean_dec(v_x_322_);
v_res_327_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_x_320_, v_x_7941__boxed_325_, v_x_7942__boxed_326_, v_x_323_, v_x_324_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0___redArg(lean_object* v_x_328_, lean_object* v_x_329_, lean_object* v_x_330_){
_start:
{
uint64_t v___x_331_; size_t v___x_332_; size_t v___x_333_; lean_object* v___x_334_; 
v___x_331_ = lean_uint64_of_nat(v_x_329_);
v___x_332_ = lean_uint64_to_usize(v___x_331_);
v___x_333_ = ((size_t)1ULL);
v___x_334_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_x_328_, v___x_332_, v___x_333_, v_x_329_, v_x_330_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___lam__0(lean_object* v_x_335_, lean_object* v___y_336_, lean_object* v_a_337_, lean_object* v_s_338_){
_start:
{
lean_object* v_vars_339_; lean_object* v_varMap_340_; lean_object* v_varsHistory_341_; lean_object* v_natToIntMap_342_; lean_object* v_natDef_343_; lean_object* v_dvds_344_; lean_object* v_lowers_345_; lean_object* v_uppers_346_; lean_object* v_diseqs_347_; lean_object* v_elimEqs_348_; lean_object* v_elimStack_349_; lean_object* v_occurs_350_; lean_object* v_assignment_351_; lean_object* v_nextCnstrId_352_; uint8_t v_caseSplits_353_; lean_object* v_steps_354_; lean_object* v_conflict_x3f_355_; lean_object* v_diseqSplits_356_; lean_object* v_divMod_357_; uint8_t v_usedCommRing_358_; lean_object* v_nonlinearOccs_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_368_; 
v_vars_339_ = lean_ctor_get(v_s_338_, 0);
v_varMap_340_ = lean_ctor_get(v_s_338_, 1);
v_varsHistory_341_ = lean_ctor_get(v_s_338_, 2);
v_natToIntMap_342_ = lean_ctor_get(v_s_338_, 3);
v_natDef_343_ = lean_ctor_get(v_s_338_, 4);
v_dvds_344_ = lean_ctor_get(v_s_338_, 5);
v_lowers_345_ = lean_ctor_get(v_s_338_, 6);
v_uppers_346_ = lean_ctor_get(v_s_338_, 7);
v_diseqs_347_ = lean_ctor_get(v_s_338_, 8);
v_elimEqs_348_ = lean_ctor_get(v_s_338_, 9);
v_elimStack_349_ = lean_ctor_get(v_s_338_, 10);
v_occurs_350_ = lean_ctor_get(v_s_338_, 11);
v_assignment_351_ = lean_ctor_get(v_s_338_, 12);
v_nextCnstrId_352_ = lean_ctor_get(v_s_338_, 13);
v_caseSplits_353_ = lean_ctor_get_uint8(v_s_338_, sizeof(void*)*19);
v_steps_354_ = lean_ctor_get(v_s_338_, 14);
v_conflict_x3f_355_ = lean_ctor_get(v_s_338_, 15);
v_diseqSplits_356_ = lean_ctor_get(v_s_338_, 16);
v_divMod_357_ = lean_ctor_get(v_s_338_, 17);
v_usedCommRing_358_ = lean_ctor_get_uint8(v_s_338_, sizeof(void*)*19 + 1);
v_nonlinearOccs_359_ = lean_ctor_get(v_s_338_, 18);
v_isSharedCheck_368_ = !lean_is_exclusive(v_s_338_);
if (v_isSharedCheck_368_ == 0)
{
v___x_361_ = v_s_338_;
v_isShared_362_ = v_isSharedCheck_368_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_nonlinearOccs_359_);
lean_inc(v_divMod_357_);
lean_inc(v_diseqSplits_356_);
lean_inc(v_conflict_x3f_355_);
lean_inc(v_steps_354_);
lean_inc(v_nextCnstrId_352_);
lean_inc(v_assignment_351_);
lean_inc(v_occurs_350_);
lean_inc(v_elimStack_349_);
lean_inc(v_elimEqs_348_);
lean_inc(v_diseqs_347_);
lean_inc(v_uppers_346_);
lean_inc(v_lowers_345_);
lean_inc(v_dvds_344_);
lean_inc(v_natDef_343_);
lean_inc(v_natToIntMap_342_);
lean_inc(v_varsHistory_341_);
lean_inc(v_varMap_340_);
lean_inc(v_vars_339_);
lean_dec(v_s_338_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_368_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_366_; 
v___x_363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_363_, 0, v_x_335_);
lean_ctor_set(v___x_363_, 1, v___y_336_);
v___x_364_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0___redArg(v_nonlinearOccs_359_, v_a_337_, v___x_363_);
if (v_isShared_362_ == 0)
{
lean_ctor_set(v___x_361_, 18, v___x_364_);
v___x_366_ = v___x_361_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_vars_339_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v_varMap_340_);
lean_ctor_set(v_reuseFailAlloc_367_, 2, v_varsHistory_341_);
lean_ctor_set(v_reuseFailAlloc_367_, 3, v_natToIntMap_342_);
lean_ctor_set(v_reuseFailAlloc_367_, 4, v_natDef_343_);
lean_ctor_set(v_reuseFailAlloc_367_, 5, v_dvds_344_);
lean_ctor_set(v_reuseFailAlloc_367_, 6, v_lowers_345_);
lean_ctor_set(v_reuseFailAlloc_367_, 7, v_uppers_346_);
lean_ctor_set(v_reuseFailAlloc_367_, 8, v_diseqs_347_);
lean_ctor_set(v_reuseFailAlloc_367_, 9, v_elimEqs_348_);
lean_ctor_set(v_reuseFailAlloc_367_, 10, v_elimStack_349_);
lean_ctor_set(v_reuseFailAlloc_367_, 11, v_occurs_350_);
lean_ctor_set(v_reuseFailAlloc_367_, 12, v_assignment_351_);
lean_ctor_set(v_reuseFailAlloc_367_, 13, v_nextCnstrId_352_);
lean_ctor_set(v_reuseFailAlloc_367_, 14, v_steps_354_);
lean_ctor_set(v_reuseFailAlloc_367_, 15, v_conflict_x3f_355_);
lean_ctor_set(v_reuseFailAlloc_367_, 16, v_diseqSplits_356_);
lean_ctor_set(v_reuseFailAlloc_367_, 17, v_divMod_357_);
lean_ctor_set(v_reuseFailAlloc_367_, 18, v___x_364_);
lean_ctor_set_uint8(v_reuseFailAlloc_367_, sizeof(void*)*19, v_caseSplits_353_);
lean_ctor_set_uint8(v_reuseFailAlloc_367_, sizeof(void*)*19 + 1, v_usedCommRing_358_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1(lean_object* v_a_369_, lean_object* v_x_370_){
_start:
{
if (lean_obj_tag(v_x_370_) == 0)
{
uint8_t v___x_371_; 
v___x_371_ = 0;
return v___x_371_;
}
else
{
lean_object* v_head_372_; lean_object* v_tail_373_; uint8_t v___x_374_; 
v_head_372_ = lean_ctor_get(v_x_370_, 0);
v_tail_373_ = lean_ctor_get(v_x_370_, 1);
v___x_374_ = lean_nat_dec_eq(v_a_369_, v_head_372_);
if (v___x_374_ == 0)
{
v_x_370_ = v_tail_373_;
goto _start;
}
else
{
return v___x_374_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___boxed(lean_object* v_a_376_, lean_object* v_x_377_){
_start:
{
uint8_t v_res_378_; lean_object* v_r_379_; 
v_res_378_ = l_List_elem___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1(v_a_376_, v_x_377_);
lean_dec(v_x_377_);
lean_dec(v_a_376_);
v_r_379_ = lean_box(v_res_378_);
return v_r_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6___redArg(lean_object* v_keys_380_, lean_object* v_vals_381_, lean_object* v_i_382_, lean_object* v_k_383_){
_start:
{
lean_object* v___x_384_; uint8_t v___x_385_; 
v___x_384_ = lean_array_get_size(v_keys_380_);
v___x_385_ = lean_nat_dec_lt(v_i_382_, v___x_384_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; 
lean_dec(v_i_382_);
v___x_386_ = lean_box(0);
return v___x_386_;
}
else
{
lean_object* v_k_x27_387_; uint8_t v___x_388_; 
v_k_x27_387_ = lean_array_fget_borrowed(v_keys_380_, v_i_382_);
v___x_388_ = lean_nat_dec_eq(v_k_383_, v_k_x27_387_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = lean_unsigned_to_nat(1u);
v___x_390_ = lean_nat_add(v_i_382_, v___x_389_);
lean_dec(v_i_382_);
v_i_382_ = v___x_390_;
goto _start;
}
else
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = lean_array_fget_borrowed(v_vals_381_, v_i_382_);
lean_dec(v_i_382_);
lean_inc(v___x_392_);
v___x_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
return v___x_393_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_keys_394_, lean_object* v_vals_395_, lean_object* v_i_396_, lean_object* v_k_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6___redArg(v_keys_394_, v_vals_395_, v_i_396_, v_k_397_);
lean_dec(v_k_397_);
lean_dec_ref(v_vals_395_);
lean_dec_ref(v_keys_394_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___redArg(lean_object* v_x_399_, size_t v_x_400_, lean_object* v_x_401_){
_start:
{
if (lean_obj_tag(v_x_399_) == 0)
{
lean_object* v_es_402_; lean_object* v___x_403_; size_t v___x_404_; size_t v___x_405_; lean_object* v_j_406_; lean_object* v___x_407_; 
v_es_402_ = lean_ctor_get(v_x_399_, 0);
v___x_403_ = lean_box(2);
v___x_404_ = ((size_t)31ULL);
v___x_405_ = lean_usize_land(v_x_400_, v___x_404_);
v_j_406_ = lean_usize_to_nat(v___x_405_);
v___x_407_ = lean_array_get_borrowed(v___x_403_, v_es_402_, v_j_406_);
lean_dec(v_j_406_);
switch(lean_obj_tag(v___x_407_))
{
case 0:
{
lean_object* v_key_408_; lean_object* v_val_409_; uint8_t v___x_410_; 
v_key_408_ = lean_ctor_get(v___x_407_, 0);
v_val_409_ = lean_ctor_get(v___x_407_, 1);
v___x_410_ = lean_nat_dec_eq(v_x_401_, v_key_408_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; 
v___x_411_ = lean_box(0);
return v___x_411_;
}
else
{
lean_object* v___x_412_; 
lean_inc(v_val_409_);
v___x_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_412_, 0, v_val_409_);
return v___x_412_;
}
}
case 1:
{
lean_object* v_node_413_; size_t v___x_414_; size_t v___x_415_; 
v_node_413_ = lean_ctor_get(v___x_407_, 0);
v___x_414_ = ((size_t)5ULL);
v___x_415_ = lean_usize_shift_right(v_x_400_, v___x_414_);
v_x_399_ = v_node_413_;
v_x_400_ = v___x_415_;
goto _start;
}
default: 
{
lean_object* v___x_417_; 
v___x_417_ = lean_box(0);
return v___x_417_;
}
}
}
else
{
lean_object* v_ks_418_; lean_object* v_vs_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v_ks_418_ = lean_ctor_get(v_x_399_, 0);
v_vs_419_ = lean_ctor_get(v_x_399_, 1);
v___x_420_ = lean_unsigned_to_nat(0u);
v___x_421_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6___redArg(v_ks_418_, v_vs_419_, v___x_420_, v_x_401_);
return v___x_421_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___redArg___boxed(lean_object* v_x_422_, lean_object* v_x_423_, lean_object* v_x_424_){
_start:
{
size_t v_x_8160__boxed_425_; lean_object* v_res_426_; 
v_x_8160__boxed_425_ = lean_unbox_usize(v_x_423_);
lean_dec(v_x_423_);
v_res_426_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___redArg(v_x_422_, v_x_8160__boxed_425_, v_x_424_);
lean_dec(v_x_424_);
lean_dec_ref(v_x_422_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2___redArg(lean_object* v_x_427_, lean_object* v_x_428_){
_start:
{
uint64_t v___x_429_; size_t v___x_430_; lean_object* v___x_431_; 
v___x_429_ = lean_uint64_of_nat(v_x_428_);
v___x_430_ = lean_uint64_to_usize(v___x_429_);
v___x_431_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___redArg(v_x_427_, v___x_430_, v_x_428_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2___redArg___boxed(lean_object* v_x_432_, lean_object* v_x_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2___redArg(v_x_432_, v_x_433_);
lean_dec(v_x_433_);
lean_dec_ref(v_x_432_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(lean_object* v_arg_435_, lean_object* v_x_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = lean_box(0);
lean_inc(v_a_446_);
lean_inc_ref(v_a_445_);
lean_inc(v_a_444_);
lean_inc_ref(v_a_443_);
lean_inc(v_a_442_);
lean_inc_ref(v_a_441_);
lean_inc(v_a_440_);
lean_inc_ref(v_a_439_);
lean_inc(v_a_438_);
lean_inc(v_a_437_);
v___x_449_ = lean_grind_cutsat_mk_var(v_arg_435_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_518_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_518_ == 0)
{
v___x_452_ = v___x_449_;
v_isShared_453_ = v_isSharedCheck_518_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_449_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_518_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___y_455_; lean_object* v___y_456_; lean_object* v___y_466_; lean_object* v___y_467_; lean_object* v___x_482_; 
v___x_482_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_437_, v_a_445_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; lean_object* v___y_485_; lean_object* v_elimEqs_505_; lean_object* v_size_506_; uint8_t v___x_507_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
lean_inc(v_a_483_);
lean_dec_ref_known(v___x_482_, 1);
v_elimEqs_505_ = lean_ctor_get(v_a_483_, 9);
lean_inc_ref(v_elimEqs_505_);
lean_dec(v_a_483_);
v_size_506_ = lean_ctor_get(v_elimEqs_505_, 2);
v___x_507_ = lean_nat_dec_lt(v_a_450_, v_size_506_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; 
lean_dec_ref(v_elimEqs_505_);
v___x_508_ = l_outOfBounds___redArg(v___x_448_);
v___y_485_ = v___x_508_;
goto v___jp_484_;
}
else
{
lean_object* v___x_509_; 
v___x_509_ = l_Lean_PersistentArray_get_x21___redArg(v___x_448_, v_elimEqs_505_, v_a_450_);
lean_dec_ref(v_elimEqs_505_);
v___y_485_ = v___x_509_;
goto v___jp_484_;
}
v___jp_484_:
{
if (lean_obj_tag(v___y_485_) == 0)
{
v___y_466_ = v_a_437_;
v___y_467_ = v_a_445_;
goto v___jp_465_;
}
else
{
lean_object* v___x_486_; 
lean_dec_ref_known(v___y_485_, 1);
lean_inc(v_a_446_);
lean_inc_ref(v_a_445_);
lean_inc(v_a_444_);
lean_inc_ref(v_a_443_);
lean_inc(v_a_442_);
lean_inc_ref(v_a_441_);
lean_inc(v_a_440_);
lean_inc_ref(v_a_439_);
lean_inc(v_a_438_);
lean_inc(v_a_437_);
lean_inc(v_x_436_);
lean_inc(v_a_450_);
v___x_486_ = lean_cutsat_propagate_nonlinear(v_a_450_, v_x_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_496_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_496_ == 0)
{
v___x_489_ = v___x_486_;
v_isShared_490_ = v_isSharedCheck_496_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___x_486_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_496_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
uint8_t v___x_491_; 
v___x_491_ = lean_unbox(v_a_487_);
lean_dec(v_a_487_);
if (v___x_491_ == 0)
{
lean_del_object(v___x_489_);
v___y_466_ = v_a_437_;
v___y_467_ = v_a_445_;
goto v___jp_465_;
}
else
{
lean_object* v___x_492_; lean_object* v___x_494_; 
lean_del_object(v___x_452_);
lean_dec(v_a_450_);
lean_dec(v_x_436_);
v___x_492_ = lean_box(0);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 0, v___x_492_);
v___x_494_ = v___x_489_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_492_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
else
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
lean_del_object(v___x_452_);
lean_dec(v_a_450_);
lean_dec(v_x_436_);
v_a_497_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_504_ == 0)
{
v___x_499_ = v___x_486_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_486_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_a_497_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
}
}
else
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
lean_del_object(v___x_452_);
lean_dec(v_a_450_);
lean_dec(v_x_436_);
v_a_510_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_482_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_482_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
v___jp_454_:
{
uint8_t v___x_457_; 
v___x_457_ = l_List_elem___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1(v_x_436_, v___y_456_);
if (v___x_457_ == 0)
{
lean_object* v___f_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
lean_del_object(v___x_452_);
v___f_458_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___lam__0), 4, 3);
lean_closure_set(v___f_458_, 0, v_x_436_);
lean_closure_set(v___f_458_, 1, v___y_456_);
lean_closure_set(v___f_458_, 2, v_a_450_);
v___x_459_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_460_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_459_, v___f_458_, v___y_455_);
return v___x_460_;
}
else
{
lean_object* v___x_461_; lean_object* v___x_463_; 
lean_dec(v___y_456_);
lean_dec(v_a_450_);
lean_dec(v_x_436_);
v___x_461_ = lean_box(0);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v___x_461_);
v___x_463_ = v___x_452_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_461_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
v___jp_465_:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v___y_466_, v___y_467_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v_nonlinearOccs_470_; lean_object* v___x_471_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_a_469_);
lean_dec_ref_known(v___x_468_, 1);
v_nonlinearOccs_470_ = lean_ctor_get(v_a_469_, 18);
lean_inc_ref(v_nonlinearOccs_470_);
lean_dec(v_a_469_);
v___x_471_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2___redArg(v_nonlinearOccs_470_, v_a_450_);
lean_dec_ref(v_nonlinearOccs_470_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v___x_472_; 
v___x_472_ = lean_box(0);
v___y_455_ = v___y_466_;
v___y_456_ = v___x_472_;
goto v___jp_454_;
}
else
{
lean_object* v_val_473_; 
v_val_473_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_val_473_);
lean_dec_ref_known(v___x_471_, 1);
v___y_455_ = v___y_466_;
v___y_456_ = v_val_473_;
goto v___jp_454_;
}
}
else
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_481_; 
lean_del_object(v___x_452_);
lean_dec(v_a_450_);
lean_dec(v_x_436_);
v_a_474_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_481_ == 0)
{
v___x_476_ = v___x_468_;
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_468_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_479_; 
if (v_isShared_477_ == 0)
{
v___x_479_ = v___x_476_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_a_474_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
}
}
else
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
lean_dec(v_x_436_);
v_a_519_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_526_ == 0)
{
v___x_521_ = v___x_449_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_449_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_a_519_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___boxed(lean_object* v_arg_527_, lean_object* v_x_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_arg_527_, v_x_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_);
lean_dec(v_a_538_);
lean_dec_ref(v_a_537_);
lean_dec(v_a_536_);
lean_dec_ref(v_a_535_);
lean_dec(v_a_534_);
lean_dec_ref(v_a_533_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
lean_dec(v_a_530_);
lean_dec(v_a_529_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0(lean_object* v_00_u03b2_541_, lean_object* v_x_542_, lean_object* v_x_543_, lean_object* v_x_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0___redArg(v_x_542_, v_x_543_, v_x_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2(lean_object* v_00_u03b2_546_, lean_object* v_x_547_, lean_object* v_x_548_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2___redArg(v_x_547_, v_x_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2___boxed(lean_object* v_00_u03b2_550_, lean_object* v_x_551_, lean_object* v_x_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2(v_00_u03b2_550_, v_x_551_, v_x_552_);
lean_dec(v_x_552_);
lean_dec_ref(v_x_551_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0(lean_object* v_00_u03b2_554_, lean_object* v_x_555_, size_t v_x_556_, size_t v_x_557_, lean_object* v_x_558_, lean_object* v_x_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_x_555_, v_x_556_, v_x_557_, v_x_558_, v_x_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___boxed(lean_object* v_00_u03b2_561_, lean_object* v_x_562_, lean_object* v_x_563_, lean_object* v_x_564_, lean_object* v_x_565_, lean_object* v_x_566_){
_start:
{
size_t v_x_8391__boxed_567_; size_t v_x_8392__boxed_568_; lean_object* v_res_569_; 
v_x_8391__boxed_567_ = lean_unbox_usize(v_x_563_);
lean_dec(v_x_563_);
v_x_8392__boxed_568_ = lean_unbox_usize(v_x_564_);
lean_dec(v_x_564_);
v_res_569_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0(v_00_u03b2_561_, v_x_562_, v_x_8391__boxed_567_, v_x_8392__boxed_568_, v_x_565_, v_x_566_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3(lean_object* v_00_u03b2_570_, lean_object* v_x_571_, size_t v_x_572_, lean_object* v_x_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___redArg(v_x_571_, v_x_572_, v_x_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___boxed(lean_object* v_00_u03b2_575_, lean_object* v_x_576_, lean_object* v_x_577_, lean_object* v_x_578_){
_start:
{
size_t v_x_8408__boxed_579_; lean_object* v_res_580_; 
v_x_8408__boxed_579_ = lean_unbox_usize(v_x_577_);
lean_dec(v_x_577_);
v_res_580_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3(v_00_u03b2_575_, v_x_576_, v_x_8408__boxed_579_, v_x_578_);
lean_dec(v_x_578_);
lean_dec_ref(v_x_576_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_581_, lean_object* v_n_582_, lean_object* v_k_583_, lean_object* v_v_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1___redArg(v_n_582_, v_k_583_, v_v_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_586_, size_t v_depth_587_, lean_object* v_keys_588_, lean_object* v_vals_589_, lean_object* v_heq_590_, lean_object* v_i_591_, lean_object* v_entries_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg(v_depth_587_, v_keys_588_, v_vals_589_, v_i_591_, v_entries_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_594_, lean_object* v_depth_595_, lean_object* v_keys_596_, lean_object* v_vals_597_, lean_object* v_heq_598_, lean_object* v_i_599_, lean_object* v_entries_600_){
_start:
{
size_t v_depth_boxed_601_; lean_object* v_res_602_; 
v_depth_boxed_601_ = lean_unbox_usize(v_depth_595_);
lean_dec(v_depth_595_);
v_res_602_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2(v_00_u03b2_594_, v_depth_boxed_601_, v_keys_596_, v_vals_597_, v_heq_598_, v_i_599_, v_entries_600_);
lean_dec_ref(v_vals_597_);
lean_dec_ref(v_keys_596_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_603_, lean_object* v_keys_604_, lean_object* v_vals_605_, lean_object* v_heq_606_, lean_object* v_i_607_, lean_object* v_k_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6___redArg(v_keys_604_, v_vals_605_, v_i_607_, v_k_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_610_, lean_object* v_keys_611_, lean_object* v_vals_612_, lean_object* v_heq_613_, lean_object* v_i_614_, lean_object* v_k_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6(v_00_u03b2_610_, v_keys_611_, v_vals_612_, v_heq_613_, v_i_614_, v_k_615_);
lean_dec(v_k_615_);
lean_dec_ref(v_vals_612_);
lean_dec_ref(v_keys_611_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_617_, lean_object* v_x_618_, lean_object* v_x_619_, lean_object* v_x_620_, lean_object* v_x_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__4___redArg(v_x_618_, v_x_619_, v_x_620_, v_x_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(lean_object* v_x_623_, lean_object* v_e_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_){
_start:
{
lean_object* v___x_636_; 
lean_inc_ref(v_e_624_);
v___x_636_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_624_, v_a_632_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_a_637_; lean_object* v___x_638_; uint8_t v___x_639_; 
v_a_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc(v_a_637_);
lean_dec_ref_known(v___x_636_, 1);
v___x_638_ = l_Lean_Expr_cleanupAnnotations(v_a_637_);
v___x_639_ = l_Lean_Expr_isApp(v___x_638_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; 
lean_dec_ref(v___x_638_);
v___x_640_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_624_, v_x_623_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_);
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
v___x_644_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_624_, v_x_623_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_);
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
v___x_648_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_624_, v_x_623_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_);
return v___x_648_;
}
else
{
lean_object* v_arg_649_; lean_object* v___x_650_; uint8_t v___x_651_; 
v_arg_649_ = lean_ctor_get(v___x_646_, 1);
lean_inc_ref(v_arg_649_);
v___x_650_ = l_Lean_Expr_appFnCleanup___redArg(v___x_646_);
v___x_651_ = l_Lean_Expr_isApp(v___x_650_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; 
lean_dec_ref(v___x_650_);
lean_dec_ref(v_arg_649_);
lean_dec_ref(v_arg_645_);
lean_dec_ref(v_arg_641_);
v___x_652_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_624_, v_x_623_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_);
return v___x_652_;
}
else
{
lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_653_ = l_Lean_Expr_appFnCleanup___redArg(v___x_650_);
v___x_654_ = l_Lean_Expr_isApp(v___x_653_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; 
lean_dec_ref(v___x_653_);
lean_dec_ref(v_arg_649_);
lean_dec_ref(v_arg_645_);
lean_dec_ref(v_arg_641_);
v___x_655_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_624_, v_x_623_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_);
return v___x_655_;
}
else
{
lean_object* v___x_656_; uint8_t v___x_657_; 
v___x_656_ = l_Lean_Expr_appFnCleanup___redArg(v___x_653_);
v___x_657_ = l_Lean_Expr_isApp(v___x_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; 
lean_dec_ref(v___x_656_);
lean_dec_ref(v_arg_649_);
lean_dec_ref(v_arg_645_);
lean_dec_ref(v_arg_641_);
v___x_658_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_624_, v_x_623_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_);
return v___x_658_;
}
else
{
lean_object* v___x_659_; lean_object* v___x_660_; uint8_t v___x_661_; 
v___x_659_ = l_Lean_Expr_appFnCleanup___redArg(v___x_656_);
v___x_660_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11));
v___x_661_ = l_Lean_Expr_isConstOf(v___x_659_, v___x_660_);
lean_dec_ref(v___x_659_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; 
lean_dec_ref(v_arg_649_);
lean_dec_ref(v_arg_645_);
lean_dec_ref(v_arg_641_);
v___x_662_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_624_, v_x_623_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_);
return v___x_662_;
}
else
{
lean_object* v___x_663_; 
v___x_663_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_649_, v_a_632_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v_a_664_; uint8_t v___x_665_; 
v_a_664_ = lean_ctor_get(v___x_663_, 0);
lean_inc(v_a_664_);
lean_dec_ref_known(v___x_663_, 1);
v___x_665_ = lean_unbox(v_a_664_);
lean_dec(v_a_664_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; 
lean_dec_ref(v_arg_645_);
lean_dec_ref(v_arg_641_);
v___x_666_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_624_, v_x_623_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_);
return v___x_666_;
}
else
{
lean_object* v___x_667_; 
lean_dec_ref(v_e_624_);
lean_inc(v_x_623_);
v___x_667_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(v_x_623_, v_arg_645_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_dec_ref_known(v___x_667_, 1);
v_e_624_ = v_arg_641_;
goto _start;
}
else
{
lean_dec_ref(v_arg_641_);
lean_dec(v_x_623_);
return v___x_667_;
}
}
}
else
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_676_; 
lean_dec_ref(v_arg_645_);
lean_dec_ref(v_arg_641_);
lean_dec_ref(v_e_624_);
lean_dec(v_x_623_);
v_a_669_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_676_ == 0)
{
v___x_671_ = v___x_663_;
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_663_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_674_; 
if (v_isShared_672_ == 0)
{
v___x_674_ = v___x_671_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_a_669_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
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
lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_684_; 
lean_dec_ref(v_e_624_);
lean_dec(v_x_623_);
v_a_677_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_684_ == 0)
{
v___x_679_ = v___x_636_;
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v___x_636_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_680_ == 0)
{
v___x_682_ = v___x_679_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_677_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go___boxed(lean_object* v_x_685_, lean_object* v_e_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(v_x_685_, v_e_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_);
lean_dec(v_a_696_);
lean_dec_ref(v_a_695_);
lean_dec(v_a_694_);
lean_dec_ref(v_a_693_);
lean_dec(v_a_692_);
lean_dec_ref(v_a_691_);
lean_dec(v_a_690_);
lean_dec_ref(v_a_689_);
lean_dec(v_a_688_);
lean_dec(v_a_687_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt(lean_object* v_e_699_, lean_object* v_x_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_699_, v_a_708_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_720_; uint8_t v___x_721_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_a_719_);
lean_dec_ref_known(v___x_718_, 1);
v___x_720_ = l_Lean_Expr_cleanupAnnotations(v_a_719_);
v___x_721_ = l_Lean_Expr_isApp(v___x_720_);
if (v___x_721_ == 0)
{
lean_dec_ref(v___x_720_);
lean_dec(v_x_700_);
goto v___jp_712_;
}
else
{
lean_object* v_arg_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v_arg_722_ = lean_ctor_get(v___x_720_, 1);
lean_inc_ref(v_arg_722_);
v___x_723_ = l_Lean_Expr_appFnCleanup___redArg(v___x_720_);
v___x_724_ = l_Lean_Expr_isApp(v___x_723_);
if (v___x_724_ == 0)
{
lean_dec_ref(v___x_723_);
lean_dec_ref(v_arg_722_);
lean_dec(v_x_700_);
goto v___jp_712_;
}
else
{
lean_object* v_arg_725_; lean_object* v___x_726_; uint8_t v___x_727_; 
v_arg_725_ = lean_ctor_get(v___x_723_, 1);
lean_inc_ref(v_arg_725_);
v___x_726_ = l_Lean_Expr_appFnCleanup___redArg(v___x_723_);
v___x_727_ = l_Lean_Expr_isApp(v___x_726_);
if (v___x_727_ == 0)
{
lean_dec_ref(v___x_726_);
lean_dec_ref(v_arg_725_);
lean_dec_ref(v_arg_722_);
lean_dec(v_x_700_);
goto v___jp_712_;
}
else
{
lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_728_ = l_Lean_Expr_appFnCleanup___redArg(v___x_726_);
v___x_729_ = l_Lean_Expr_isApp(v___x_728_);
if (v___x_729_ == 0)
{
lean_dec_ref(v___x_728_);
lean_dec_ref(v_arg_725_);
lean_dec_ref(v_arg_722_);
lean_dec(v_x_700_);
goto v___jp_712_;
}
else
{
lean_object* v___x_730_; uint8_t v___x_731_; 
v___x_730_ = l_Lean_Expr_appFnCleanup___redArg(v___x_728_);
v___x_731_ = l_Lean_Expr_isApp(v___x_730_);
if (v___x_731_ == 0)
{
lean_dec_ref(v___x_730_);
lean_dec_ref(v_arg_725_);
lean_dec_ref(v_arg_722_);
lean_dec(v_x_700_);
goto v___jp_712_;
}
else
{
lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_732_ = l_Lean_Expr_appFnCleanup___redArg(v___x_730_);
v___x_733_ = l_Lean_Expr_isApp(v___x_732_);
if (v___x_733_ == 0)
{
lean_dec_ref(v___x_732_);
lean_dec_ref(v_arg_725_);
lean_dec_ref(v_arg_722_);
lean_dec(v_x_700_);
goto v___jp_712_;
}
else
{
lean_object* v___x_734_; lean_object* v___x_735_; uint8_t v___x_736_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___y_747_; 
v___x_734_ = l_Lean_Expr_appFnCleanup___redArg(v___x_732_);
v___x_735_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__2));
v___x_736_ = l_Lean_Expr_isConstOf(v___x_734_, v___x_735_);
if (v___x_736_ == 0)
{
lean_object* v___x_792_; uint8_t v___x_793_; 
v___x_792_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__5));
v___x_793_ = l_Lean_Expr_isConstOf(v___x_734_, v___x_792_);
if (v___x_793_ == 0)
{
lean_object* v___x_794_; uint8_t v___x_795_; 
v___x_794_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__8));
v___x_795_ = l_Lean_Expr_isConstOf(v___x_734_, v___x_794_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; uint8_t v___x_797_; 
v___x_796_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11));
v___x_797_ = l_Lean_Expr_isConstOf(v___x_734_, v___x_796_);
lean_dec_ref(v___x_734_);
if (v___x_797_ == 0)
{
lean_dec_ref(v_arg_725_);
lean_dec_ref(v_arg_722_);
lean_dec(v_x_700_);
goto v___jp_712_;
}
else
{
lean_object* v___x_798_; 
lean_inc(v_x_700_);
v___x_798_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(v_x_700_, v_arg_725_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v___x_799_; 
lean_dec_ref_known(v___x_798_, 1);
v___x_799_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(v_x_700_, v_arg_722_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
return v___x_799_;
}
else
{
lean_dec_ref(v_arg_722_);
lean_dec(v_x_700_);
return v___x_798_;
}
}
}
else
{
lean_object* v___x_800_; 
lean_dec_ref(v___x_734_);
lean_dec_ref(v_arg_725_);
v___x_800_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_arg_722_, v_x_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
return v___x_800_;
}
}
else
{
lean_object* v___x_801_; 
lean_dec_ref(v___x_734_);
lean_dec_ref(v_arg_725_);
v___x_801_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_arg_722_, v_x_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
return v___x_801_;
}
}
else
{
lean_object* v___x_802_; 
lean_dec_ref(v___x_734_);
lean_inc_ref(v_arg_725_);
v___x_802_ = l_Lean_Meta_getIntValue_x3f(v_arg_725_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_a_803_);
lean_dec_ref_known(v___x_802_, 1);
if (lean_obj_tag(v_a_803_) == 0)
{
if (v___x_736_ == 0)
{
lean_dec_ref(v_arg_725_);
v___y_738_ = v_a_701_;
v___y_739_ = v_a_702_;
v___y_740_ = v_a_703_;
v___y_741_ = v_a_704_;
v___y_742_ = v_a_705_;
v___y_743_ = v_a_706_;
v___y_744_ = v_a_707_;
v___y_745_ = v_a_708_;
v___y_746_ = v_a_709_;
v___y_747_ = v_a_710_;
goto v___jp_737_;
}
else
{
lean_object* v___x_804_; 
lean_inc(v_x_700_);
v___x_804_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_arg_725_, v_x_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_dec_ref_known(v___x_804_, 1);
v___y_738_ = v_a_701_;
v___y_739_ = v_a_702_;
v___y_740_ = v_a_703_;
v___y_741_ = v_a_704_;
v___y_742_ = v_a_705_;
v___y_743_ = v_a_706_;
v___y_744_ = v_a_707_;
v___y_745_ = v_a_708_;
v___y_746_ = v_a_709_;
v___y_747_ = v_a_710_;
goto v___jp_737_;
}
else
{
lean_dec_ref(v_arg_722_);
lean_dec(v_x_700_);
return v___x_804_;
}
}
}
else
{
lean_dec_ref_known(v_a_803_, 1);
lean_dec_ref(v_arg_725_);
v___y_738_ = v_a_701_;
v___y_739_ = v_a_702_;
v___y_740_ = v_a_703_;
v___y_741_ = v_a_704_;
v___y_742_ = v_a_705_;
v___y_743_ = v_a_706_;
v___y_744_ = v_a_707_;
v___y_745_ = v_a_708_;
v___y_746_ = v_a_709_;
v___y_747_ = v_a_710_;
goto v___jp_737_;
}
}
else
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
lean_dec_ref(v_arg_725_);
lean_dec_ref(v_arg_722_);
lean_dec(v_x_700_);
v_a_805_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_812_ == 0)
{
v___x_807_ = v___x_802_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_802_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_a_805_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
v___jp_737_:
{
lean_object* v___x_748_; 
lean_inc_ref(v_arg_722_);
v___x_748_ = l_Lean_Meta_getIntValue_x3f(v_arg_722_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; lean_object* v___x_750_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_749_);
lean_dec_ref_known(v___x_748_, 1);
v___x_750_ = l_Lean_Meta_getNatValue_x3f(v_arg_722_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
if (lean_obj_tag(v___x_750_) == 0)
{
if (lean_obj_tag(v_a_749_) == 0)
{
if (v___x_736_ == 0)
{
lean_dec_ref_known(v___x_750_, 1);
lean_dec_ref(v_arg_722_);
lean_dec(v_x_700_);
goto v___jp_715_;
}
else
{
lean_object* v_a_751_; 
v_a_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_a_751_);
lean_dec_ref_known(v___x_750_, 1);
if (lean_obj_tag(v_a_751_) == 0)
{
lean_object* v___x_752_; 
lean_inc_ref(v_arg_722_);
v___x_752_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_arg_722_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_a_753_; lean_object* v_fst_754_; lean_object* v___x_755_; 
v_a_753_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_a_753_);
lean_dec_ref_known(v___x_752_, 1);
v_fst_754_ = lean_ctor_get(v_a_753_, 0);
lean_inc(v_fst_754_);
lean_dec(v_a_753_);
v___x_755_ = l_Lean_Meta_Grind_getGeneration___redArg(v_arg_722_, v___y_738_);
lean_dec_ref(v_arg_722_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v_a_756_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_a_756_);
lean_dec_ref_known(v___x_755_, 1);
v___x_757_ = lean_box(0);
lean_inc(v___y_747_);
lean_inc_ref(v___y_746_);
lean_inc(v___y_745_);
lean_inc_ref(v___y_744_);
lean_inc(v___y_743_);
lean_inc_ref(v___y_742_);
lean_inc(v___y_741_);
lean_inc_ref(v___y_740_);
lean_inc(v___y_739_);
lean_inc(v___y_738_);
lean_inc(v_fst_754_);
v___x_758_ = lean_grind_internalize(v_fst_754_, v_a_756_, v___x_757_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v___x_759_; 
lean_dec_ref_known(v___x_758_, 1);
v___x_759_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_fst_754_, v_x_700_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
return v___x_759_;
}
else
{
lean_dec(v_fst_754_);
lean_dec(v_x_700_);
return v___x_758_;
}
}
else
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
lean_dec(v_fst_754_);
lean_dec(v_x_700_);
v_a_760_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_755_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_755_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_760_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
else
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
lean_dec_ref(v_arg_722_);
lean_dec(v_x_700_);
v_a_768_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_752_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_752_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_768_);
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
else
{
lean_dec_ref_known(v_a_751_, 1);
lean_dec_ref(v_arg_722_);
lean_dec(v_x_700_);
goto v___jp_715_;
}
}
}
else
{
lean_dec_ref_known(v_a_749_, 1);
lean_dec_ref_known(v___x_750_, 1);
lean_dec_ref(v_arg_722_);
lean_dec(v_x_700_);
goto v___jp_715_;
}
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_dec(v_a_749_);
lean_dec_ref(v_arg_722_);
lean_dec(v_x_700_);
v_a_776_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_750_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_750_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
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
else
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
lean_dec_ref(v_arg_722_);
lean_dec(v_x_700_);
v_a_784_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___x_748_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_748_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_784_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
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
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_820_; 
lean_dec(v_x_700_);
v_a_813_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_820_ == 0)
{
v___x_815_ = v___x_718_;
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_718_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_820_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_818_; 
if (v_isShared_816_ == 0)
{
v___x_818_ = v___x_815_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_813_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
v___jp_712_:
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = lean_box(0);
v___x_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
return v___x_714_;
}
v___jp_715_:
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = lean_box(0);
v___x_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
return v___x_717_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt___boxed(lean_object* v_e_821_, lean_object* v_x_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt(v_e_821_, v_x_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_);
lean_dec(v_a_832_);
lean_dec_ref(v_a_831_);
lean_dec(v_a_830_);
lean_dec_ref(v_a_829_);
lean_dec(v_a_828_);
lean_dec_ref(v_a_827_);
lean_dec(v_a_826_);
lean_dec_ref(v_a_825_);
lean_dec(v_a_824_);
lean_dec(v_a_823_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_x_835_, lean_object* v_x_836_, lean_object* v_x_837_, lean_object* v_x_838_){
_start:
{
lean_object* v_ks_839_; lean_object* v_vs_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_866_; 
v_ks_839_ = lean_ctor_get(v_x_835_, 0);
v_vs_840_ = lean_ctor_get(v_x_835_, 1);
v_isSharedCheck_866_ = !lean_is_exclusive(v_x_835_);
if (v_isSharedCheck_866_ == 0)
{
v___x_842_ = v_x_835_;
v_isShared_843_ = v_isSharedCheck_866_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_vs_840_);
lean_inc(v_ks_839_);
lean_dec(v_x_835_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_866_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_844_; uint8_t v___x_845_; 
v___x_844_ = lean_array_get_size(v_ks_839_);
v___x_845_ = lean_nat_dec_lt(v_x_836_, v___x_844_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_849_; 
lean_dec(v_x_836_);
v___x_846_ = lean_array_push(v_ks_839_, v_x_837_);
v___x_847_ = lean_array_push(v_vs_840_, v_x_838_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 1, v___x_847_);
lean_ctor_set(v___x_842_, 0, v___x_846_);
v___x_849_ = v___x_842_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_846_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v___x_847_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
else
{
lean_object* v_k_x27_851_; size_t v___x_852_; size_t v___x_853_; uint8_t v___x_854_; 
v_k_x27_851_ = lean_array_fget_borrowed(v_ks_839_, v_x_836_);
v___x_852_ = lean_ptr_addr(v_x_837_);
v___x_853_ = lean_ptr_addr(v_k_x27_851_);
v___x_854_ = lean_usize_dec_eq(v___x_852_, v___x_853_);
if (v___x_854_ == 0)
{
lean_object* v___x_856_; 
if (v_isShared_843_ == 0)
{
v___x_856_ = v___x_842_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_ks_839_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v_vs_840_);
v___x_856_ = v_reuseFailAlloc_860_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_857_ = lean_unsigned_to_nat(1u);
v___x_858_ = lean_nat_add(v_x_836_, v___x_857_);
lean_dec(v_x_836_);
v_x_835_ = v___x_856_;
v_x_836_ = v___x_858_;
goto _start;
}
}
else
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_864_; 
v___x_861_ = lean_array_fset(v_ks_839_, v_x_836_, v_x_837_);
v___x_862_ = lean_array_fset(v_vs_840_, v_x_836_, v_x_838_);
lean_dec(v_x_836_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 1, v___x_862_);
lean_ctor_set(v___x_842_, 0, v___x_861_);
v___x_864_ = v___x_842_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_861_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v___x_862_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4___redArg(lean_object* v_n_867_, lean_object* v_k_868_, lean_object* v_v_869_){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = lean_unsigned_to_nat(0u);
v___x_871_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7___redArg(v_n_867_, v___x_870_, v_k_868_, v_v_869_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(lean_object* v_x_872_, size_t v_x_873_, size_t v_x_874_, lean_object* v_x_875_, lean_object* v_x_876_){
_start:
{
if (lean_obj_tag(v_x_872_) == 0)
{
lean_object* v_es_877_; size_t v___x_878_; size_t v___x_879_; lean_object* v_j_880_; lean_object* v___x_881_; uint8_t v___x_882_; 
v_es_877_ = lean_ctor_get(v_x_872_, 0);
v___x_878_ = ((size_t)31ULL);
v___x_879_ = lean_usize_land(v_x_873_, v___x_878_);
v_j_880_ = lean_usize_to_nat(v___x_879_);
v___x_881_ = lean_array_get_size(v_es_877_);
v___x_882_ = lean_nat_dec_lt(v_j_880_, v___x_881_);
if (v___x_882_ == 0)
{
lean_dec(v_j_880_);
lean_dec(v_x_876_);
lean_dec_ref(v_x_875_);
return v_x_872_;
}
else
{
lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_923_; 
lean_inc_ref(v_es_877_);
v_isSharedCheck_923_ = !lean_is_exclusive(v_x_872_);
if (v_isSharedCheck_923_ == 0)
{
lean_object* v_unused_924_; 
v_unused_924_ = lean_ctor_get(v_x_872_, 0);
lean_dec(v_unused_924_);
v___x_884_ = v_x_872_;
v_isShared_885_ = v_isSharedCheck_923_;
goto v_resetjp_883_;
}
else
{
lean_dec(v_x_872_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_923_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v_v_886_; lean_object* v___x_887_; lean_object* v_xs_x27_888_; lean_object* v___y_890_; 
v_v_886_ = lean_array_fget(v_es_877_, v_j_880_);
v___x_887_ = lean_box(0);
v_xs_x27_888_ = lean_array_fset(v_es_877_, v_j_880_, v___x_887_);
switch(lean_obj_tag(v_v_886_))
{
case 0:
{
lean_object* v_key_895_; lean_object* v_val_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_908_; 
v_key_895_ = lean_ctor_get(v_v_886_, 0);
v_val_896_ = lean_ctor_get(v_v_886_, 1);
v_isSharedCheck_908_ = !lean_is_exclusive(v_v_886_);
if (v_isSharedCheck_908_ == 0)
{
v___x_898_ = v_v_886_;
v_isShared_899_ = v_isSharedCheck_908_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_val_896_);
lean_inc(v_key_895_);
lean_dec(v_v_886_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_908_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
size_t v___x_900_; size_t v___x_901_; uint8_t v___x_902_; 
v___x_900_ = lean_ptr_addr(v_x_875_);
v___x_901_ = lean_ptr_addr(v_key_895_);
v___x_902_ = lean_usize_dec_eq(v___x_900_, v___x_901_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; lean_object* v___x_904_; 
lean_del_object(v___x_898_);
v___x_903_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_895_, v_val_896_, v_x_875_, v_x_876_);
v___x_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
v___y_890_ = v___x_904_;
goto v___jp_889_;
}
else
{
lean_object* v___x_906_; 
lean_dec(v_val_896_);
lean_dec(v_key_895_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 1, v_x_876_);
lean_ctor_set(v___x_898_, 0, v_x_875_);
v___x_906_ = v___x_898_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_x_875_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v_x_876_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
v___y_890_ = v___x_906_;
goto v___jp_889_;
}
}
}
}
case 1:
{
lean_object* v_node_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_921_; 
v_node_909_ = lean_ctor_get(v_v_886_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v_v_886_);
if (v_isSharedCheck_921_ == 0)
{
v___x_911_ = v_v_886_;
v_isShared_912_ = v_isSharedCheck_921_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_node_909_);
lean_dec(v_v_886_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_921_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
size_t v___x_913_; size_t v___x_914_; size_t v___x_915_; size_t v___x_916_; lean_object* v___x_917_; lean_object* v___x_919_; 
v___x_913_ = ((size_t)5ULL);
v___x_914_ = lean_usize_shift_right(v_x_873_, v___x_913_);
v___x_915_ = ((size_t)1ULL);
v___x_916_ = lean_usize_add(v_x_874_, v___x_915_);
v___x_917_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_node_909_, v___x_914_, v___x_916_, v_x_875_, v_x_876_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v___x_917_);
v___x_919_ = v___x_911_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_917_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
v___y_890_ = v___x_919_;
goto v___jp_889_;
}
}
}
default: 
{
lean_object* v___x_922_; 
v___x_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_922_, 0, v_x_875_);
lean_ctor_set(v___x_922_, 1, v_x_876_);
v___y_890_ = v___x_922_;
goto v___jp_889_;
}
}
v___jp_889_:
{
lean_object* v___x_891_; lean_object* v___x_893_; 
v___x_891_ = lean_array_fset(v_xs_x27_888_, v_j_880_, v___y_890_);
lean_dec(v_j_880_);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 0, v___x_891_);
v___x_893_ = v___x_884_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_891_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
}
else
{
lean_object* v_ks_925_; lean_object* v_vs_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_944_; 
v_ks_925_ = lean_ctor_get(v_x_872_, 0);
v_vs_926_ = lean_ctor_get(v_x_872_, 1);
v_isSharedCheck_944_ = !lean_is_exclusive(v_x_872_);
if (v_isSharedCheck_944_ == 0)
{
v___x_928_ = v_x_872_;
v_isShared_929_ = v_isSharedCheck_944_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_vs_926_);
lean_inc(v_ks_925_);
lean_dec(v_x_872_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_944_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_ks_925_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v_vs_926_);
v___x_931_ = v_reuseFailAlloc_943_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
lean_object* v_newNode_932_; size_t v___x_933_; uint8_t v___x_934_; 
v_newNode_932_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4___redArg(v___x_931_, v_x_875_, v_x_876_);
v___x_933_ = ((size_t)7ULL);
v___x_934_ = lean_usize_dec_le(v___x_933_, v_x_874_);
if (v___x_934_ == 0)
{
lean_object* v___x_935_; lean_object* v___x_936_; uint8_t v___x_937_; 
v___x_935_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_932_);
v___x_936_ = lean_unsigned_to_nat(4u);
v___x_937_ = lean_nat_dec_lt(v___x_935_, v___x_936_);
lean_dec(v___x_935_);
if (v___x_937_ == 0)
{
lean_object* v_ks_938_; lean_object* v_vs_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v_ks_938_ = lean_ctor_get(v_newNode_932_, 0);
lean_inc_ref(v_ks_938_);
v_vs_939_ = lean_ctor_get(v_newNode_932_, 1);
lean_inc_ref(v_vs_939_);
lean_dec_ref(v_newNode_932_);
v___x_940_ = lean_unsigned_to_nat(0u);
v___x_941_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0);
v___x_942_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(v_x_874_, v_ks_938_, v_vs_939_, v___x_940_, v___x_941_);
lean_dec_ref(v_vs_939_);
lean_dec_ref(v_ks_938_);
return v___x_942_;
}
else
{
return v_newNode_932_;
}
}
else
{
return v_newNode_932_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(size_t v_depth_945_, lean_object* v_keys_946_, lean_object* v_vals_947_, lean_object* v_i_948_, lean_object* v_entries_949_){
_start:
{
lean_object* v___x_950_; uint8_t v___x_951_; 
v___x_950_ = lean_array_get_size(v_keys_946_);
v___x_951_ = lean_nat_dec_lt(v_i_948_, v___x_950_);
if (v___x_951_ == 0)
{
lean_dec(v_i_948_);
return v_entries_949_;
}
else
{
lean_object* v_k_952_; lean_object* v_v_953_; size_t v___x_954_; size_t v___x_955_; size_t v___x_956_; uint64_t v___x_957_; size_t v_h_958_; size_t v___x_959_; lean_object* v___x_960_; size_t v___x_961_; size_t v___x_962_; size_t v___x_963_; size_t v_h_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v_k_952_ = lean_array_fget_borrowed(v_keys_946_, v_i_948_);
v_v_953_ = lean_array_fget_borrowed(v_vals_947_, v_i_948_);
v___x_954_ = lean_ptr_addr(v_k_952_);
v___x_955_ = ((size_t)3ULL);
v___x_956_ = lean_usize_shift_right(v___x_954_, v___x_955_);
v___x_957_ = lean_usize_to_uint64(v___x_956_);
v_h_958_ = lean_uint64_to_usize(v___x_957_);
v___x_959_ = ((size_t)5ULL);
v___x_960_ = lean_unsigned_to_nat(1u);
v___x_961_ = ((size_t)1ULL);
v___x_962_ = lean_usize_sub(v_depth_945_, v___x_961_);
v___x_963_ = lean_usize_mul(v___x_959_, v___x_962_);
v_h_964_ = lean_usize_shift_right(v_h_958_, v___x_963_);
v___x_965_ = lean_nat_add(v_i_948_, v___x_960_);
lean_dec(v_i_948_);
lean_inc(v_v_953_);
lean_inc(v_k_952_);
v___x_966_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_entries_949_, v_h_964_, v_depth_945_, v_k_952_, v_v_953_);
v_i_948_ = v___x_965_;
v_entries_949_ = v___x_966_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_968_, lean_object* v_keys_969_, lean_object* v_vals_970_, lean_object* v_i_971_, lean_object* v_entries_972_){
_start:
{
size_t v_depth_boxed_973_; lean_object* v_res_974_; 
v_depth_boxed_973_ = lean_unbox_usize(v_depth_968_);
lean_dec(v_depth_968_);
v_res_974_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(v_depth_boxed_973_, v_keys_969_, v_vals_970_, v_i_971_, v_entries_972_);
lean_dec_ref(v_vals_970_);
lean_dec_ref(v_keys_969_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg___boxed(lean_object* v_x_975_, lean_object* v_x_976_, lean_object* v_x_977_, lean_object* v_x_978_, lean_object* v_x_979_){
_start:
{
size_t v_x_27459__boxed_980_; size_t v_x_27460__boxed_981_; lean_object* v_res_982_; 
v_x_27459__boxed_980_ = lean_unbox_usize(v_x_976_);
lean_dec(v_x_976_);
v_x_27460__boxed_981_ = lean_unbox_usize(v_x_977_);
lean_dec(v_x_977_);
v_res_982_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_x_975_, v_x_27459__boxed_980_, v_x_27460__boxed_981_, v_x_978_, v_x_979_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg(lean_object* v_x_983_, lean_object* v_x_984_, lean_object* v_x_985_){
_start:
{
size_t v___x_986_; size_t v___x_987_; size_t v___x_988_; uint64_t v___x_989_; size_t v___x_990_; size_t v___x_991_; lean_object* v___x_992_; 
v___x_986_ = lean_ptr_addr(v_x_984_);
v___x_987_ = ((size_t)3ULL);
v___x_988_ = lean_usize_shift_right(v___x_986_, v___x_987_);
v___x_989_ = lean_usize_to_uint64(v___x_988_);
v___x_990_ = lean_uint64_to_usize(v___x_989_);
v___x_991_ = ((size_t)1ULL);
v___x_992_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_x_983_, v___x_990_, v___x_991_, v_x_984_, v_x_985_);
return v___x_992_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_993_ = lean_unsigned_to_nat(32u);
v___x_994_ = lean_mk_empty_array_with_capacity(v___x_993_);
v___x_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
return v___x_995_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1(void){
_start:
{
size_t v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_996_ = ((size_t)5ULL);
v___x_997_ = lean_unsigned_to_nat(0u);
v___x_998_ = lean_unsigned_to_nat(32u);
v___x_999_ = lean_mk_empty_array_with_capacity(v___x_998_);
v___x_1000_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0);
v___x_1001_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
lean_ctor_set(v___x_1001_, 1, v___x_999_);
lean_ctor_set(v___x_1001_, 2, v___x_997_);
lean_ctor_set(v___x_1001_, 3, v___x_997_);
lean_ctor_set_usize(v___x_1001_, 4, v___x_996_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0(lean_object* v_expr_1002_, lean_object* v_size_1003_, lean_object* v_s_1004_){
_start:
{
lean_object* v_vars_1005_; lean_object* v_varMap_1006_; lean_object* v_varsHistory_1007_; lean_object* v_natToIntMap_1008_; lean_object* v_natDef_1009_; lean_object* v_dvds_1010_; lean_object* v_lowers_1011_; lean_object* v_uppers_1012_; lean_object* v_diseqs_1013_; lean_object* v_elimEqs_1014_; lean_object* v_elimStack_1015_; lean_object* v_occurs_1016_; lean_object* v_assignment_1017_; lean_object* v_nextCnstrId_1018_; uint8_t v_caseSplits_1019_; lean_object* v_steps_1020_; lean_object* v_conflict_x3f_1021_; lean_object* v_diseqSplits_1022_; lean_object* v_divMod_1023_; uint8_t v_usedCommRing_1024_; lean_object* v_nonlinearOccs_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1043_; 
v_vars_1005_ = lean_ctor_get(v_s_1004_, 0);
v_varMap_1006_ = lean_ctor_get(v_s_1004_, 1);
v_varsHistory_1007_ = lean_ctor_get(v_s_1004_, 2);
v_natToIntMap_1008_ = lean_ctor_get(v_s_1004_, 3);
v_natDef_1009_ = lean_ctor_get(v_s_1004_, 4);
v_dvds_1010_ = lean_ctor_get(v_s_1004_, 5);
v_lowers_1011_ = lean_ctor_get(v_s_1004_, 6);
v_uppers_1012_ = lean_ctor_get(v_s_1004_, 7);
v_diseqs_1013_ = lean_ctor_get(v_s_1004_, 8);
v_elimEqs_1014_ = lean_ctor_get(v_s_1004_, 9);
v_elimStack_1015_ = lean_ctor_get(v_s_1004_, 10);
v_occurs_1016_ = lean_ctor_get(v_s_1004_, 11);
v_assignment_1017_ = lean_ctor_get(v_s_1004_, 12);
v_nextCnstrId_1018_ = lean_ctor_get(v_s_1004_, 13);
v_caseSplits_1019_ = lean_ctor_get_uint8(v_s_1004_, sizeof(void*)*19);
v_steps_1020_ = lean_ctor_get(v_s_1004_, 14);
v_conflict_x3f_1021_ = lean_ctor_get(v_s_1004_, 15);
v_diseqSplits_1022_ = lean_ctor_get(v_s_1004_, 16);
v_divMod_1023_ = lean_ctor_get(v_s_1004_, 17);
v_usedCommRing_1024_ = lean_ctor_get_uint8(v_s_1004_, sizeof(void*)*19 + 1);
v_nonlinearOccs_1025_ = lean_ctor_get(v_s_1004_, 18);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_s_1004_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1027_ = v_s_1004_;
v_isShared_1028_ = v_isSharedCheck_1043_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_nonlinearOccs_1025_);
lean_inc(v_divMod_1023_);
lean_inc(v_diseqSplits_1022_);
lean_inc(v_conflict_x3f_1021_);
lean_inc(v_steps_1020_);
lean_inc(v_nextCnstrId_1018_);
lean_inc(v_assignment_1017_);
lean_inc(v_occurs_1016_);
lean_inc(v_elimStack_1015_);
lean_inc(v_elimEqs_1014_);
lean_inc(v_diseqs_1013_);
lean_inc(v_uppers_1012_);
lean_inc(v_lowers_1011_);
lean_inc(v_dvds_1010_);
lean_inc(v_natDef_1009_);
lean_inc(v_natToIntMap_1008_);
lean_inc(v_varsHistory_1007_);
lean_inc(v_varMap_1006_);
lean_inc(v_vars_1005_);
lean_dec(v_s_1004_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1043_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1041_; 
lean_inc_ref(v_expr_1002_);
v___x_1029_ = l_Lean_PersistentArray_push___redArg(v_vars_1005_, v_expr_1002_);
v___x_1030_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg(v_varMap_1006_, v_expr_1002_, v_size_1003_);
v___x_1031_ = lean_box(0);
v___x_1032_ = l_Lean_PersistentArray_push___redArg(v_dvds_1010_, v___x_1031_);
v___x_1033_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1);
v___x_1034_ = l_Lean_PersistentArray_push___redArg(v_lowers_1011_, v___x_1033_);
v___x_1035_ = l_Lean_PersistentArray_push___redArg(v_uppers_1012_, v___x_1033_);
v___x_1036_ = l_Lean_PersistentArray_push___redArg(v_diseqs_1013_, v___x_1033_);
v___x_1037_ = l_Lean_PersistentArray_push___redArg(v_elimEqs_1014_, v___x_1031_);
v___x_1038_ = lean_box(1);
v___x_1039_ = l_Lean_PersistentArray_push___redArg(v_occurs_1016_, v___x_1038_);
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 11, v___x_1039_);
lean_ctor_set(v___x_1027_, 9, v___x_1037_);
lean_ctor_set(v___x_1027_, 8, v___x_1036_);
lean_ctor_set(v___x_1027_, 7, v___x_1035_);
lean_ctor_set(v___x_1027_, 6, v___x_1034_);
lean_ctor_set(v___x_1027_, 5, v___x_1032_);
lean_ctor_set(v___x_1027_, 1, v___x_1030_);
lean_ctor_set(v___x_1027_, 0, v___x_1029_);
v___x_1041_ = v___x_1027_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1029_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v___x_1030_);
lean_ctor_set(v_reuseFailAlloc_1042_, 2, v_varsHistory_1007_);
lean_ctor_set(v_reuseFailAlloc_1042_, 3, v_natToIntMap_1008_);
lean_ctor_set(v_reuseFailAlloc_1042_, 4, v_natDef_1009_);
lean_ctor_set(v_reuseFailAlloc_1042_, 5, v___x_1032_);
lean_ctor_set(v_reuseFailAlloc_1042_, 6, v___x_1034_);
lean_ctor_set(v_reuseFailAlloc_1042_, 7, v___x_1035_);
lean_ctor_set(v_reuseFailAlloc_1042_, 8, v___x_1036_);
lean_ctor_set(v_reuseFailAlloc_1042_, 9, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1042_, 10, v_elimStack_1015_);
lean_ctor_set(v_reuseFailAlloc_1042_, 11, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1042_, 12, v_assignment_1017_);
lean_ctor_set(v_reuseFailAlloc_1042_, 13, v_nextCnstrId_1018_);
lean_ctor_set(v_reuseFailAlloc_1042_, 14, v_steps_1020_);
lean_ctor_set(v_reuseFailAlloc_1042_, 15, v_conflict_x3f_1021_);
lean_ctor_set(v_reuseFailAlloc_1042_, 16, v_diseqSplits_1022_);
lean_ctor_set(v_reuseFailAlloc_1042_, 17, v_divMod_1023_);
lean_ctor_set(v_reuseFailAlloc_1042_, 18, v_nonlinearOccs_1025_);
lean_ctor_set_uint8(v_reuseFailAlloc_1042_, sizeof(void*)*19, v_caseSplits_1019_);
lean_ctor_set_uint8(v_reuseFailAlloc_1042_, sizeof(void*)*19 + 1, v_usedCommRing_1024_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1044_, lean_object* v_vals_1045_, lean_object* v_i_1046_, lean_object* v_k_1047_){
_start:
{
lean_object* v___x_1048_; uint8_t v___x_1049_; 
v___x_1048_ = lean_array_get_size(v_keys_1044_);
v___x_1049_ = lean_nat_dec_lt(v_i_1046_, v___x_1048_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1050_; 
lean_dec(v_i_1046_);
v___x_1050_ = lean_box(0);
return v___x_1050_;
}
else
{
lean_object* v_k_x27_1051_; size_t v___x_1052_; size_t v___x_1053_; uint8_t v___x_1054_; 
v_k_x27_1051_ = lean_array_fget_borrowed(v_keys_1044_, v_i_1046_);
v___x_1052_ = lean_ptr_addr(v_k_1047_);
v___x_1053_ = lean_ptr_addr(v_k_x27_1051_);
v___x_1054_ = lean_usize_dec_eq(v___x_1052_, v___x_1053_);
if (v___x_1054_ == 0)
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1055_ = lean_unsigned_to_nat(1u);
v___x_1056_ = lean_nat_add(v_i_1046_, v___x_1055_);
lean_dec(v_i_1046_);
v_i_1046_ = v___x_1056_;
goto _start;
}
else
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = lean_array_fget_borrowed(v_vals_1045_, v_i_1046_);
lean_dec(v_i_1046_);
lean_inc(v___x_1058_);
v___x_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
return v___x_1059_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1060_, lean_object* v_vals_1061_, lean_object* v_i_1062_, lean_object* v_k_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(v_keys_1060_, v_vals_1061_, v_i_1062_, v_k_1063_);
lean_dec_ref(v_k_1063_);
lean_dec_ref(v_vals_1061_);
lean_dec_ref(v_keys_1060_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(lean_object* v_x_1065_, size_t v_x_1066_, lean_object* v_x_1067_){
_start:
{
if (lean_obj_tag(v_x_1065_) == 0)
{
lean_object* v_es_1068_; lean_object* v___x_1069_; size_t v___x_1070_; size_t v___x_1071_; lean_object* v_j_1072_; lean_object* v___x_1073_; 
v_es_1068_ = lean_ctor_get(v_x_1065_, 0);
v___x_1069_ = lean_box(2);
v___x_1070_ = ((size_t)31ULL);
v___x_1071_ = lean_usize_land(v_x_1066_, v___x_1070_);
v_j_1072_ = lean_usize_to_nat(v___x_1071_);
v___x_1073_ = lean_array_get_borrowed(v___x_1069_, v_es_1068_, v_j_1072_);
lean_dec(v_j_1072_);
switch(lean_obj_tag(v___x_1073_))
{
case 0:
{
lean_object* v_key_1074_; lean_object* v_val_1075_; size_t v___x_1076_; size_t v___x_1077_; uint8_t v___x_1078_; 
v_key_1074_ = lean_ctor_get(v___x_1073_, 0);
v_val_1075_ = lean_ctor_get(v___x_1073_, 1);
v___x_1076_ = lean_ptr_addr(v_x_1067_);
v___x_1077_ = lean_ptr_addr(v_key_1074_);
v___x_1078_ = lean_usize_dec_eq(v___x_1076_, v___x_1077_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; 
v___x_1079_ = lean_box(0);
return v___x_1079_;
}
else
{
lean_object* v___x_1080_; 
lean_inc(v_val_1075_);
v___x_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1080_, 0, v_val_1075_);
return v___x_1080_;
}
}
case 1:
{
lean_object* v_node_1081_; size_t v___x_1082_; size_t v___x_1083_; 
v_node_1081_ = lean_ctor_get(v___x_1073_, 0);
v___x_1082_ = ((size_t)5ULL);
v___x_1083_ = lean_usize_shift_right(v_x_1066_, v___x_1082_);
v_x_1065_ = v_node_1081_;
v_x_1066_ = v___x_1083_;
goto _start;
}
default: 
{
lean_object* v___x_1085_; 
v___x_1085_ = lean_box(0);
return v___x_1085_;
}
}
}
else
{
lean_object* v_ks_1086_; lean_object* v_vs_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v_ks_1086_ = lean_ctor_get(v_x_1065_, 0);
v_vs_1087_ = lean_ctor_get(v_x_1065_, 1);
v___x_1088_ = lean_unsigned_to_nat(0u);
v___x_1089_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(v_ks_1086_, v_vs_1087_, v___x_1088_, v_x_1067_);
return v___x_1089_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg___boxed(lean_object* v_x_1090_, lean_object* v_x_1091_, lean_object* v_x_1092_){
_start:
{
size_t v_x_27724__boxed_1093_; lean_object* v_res_1094_; 
v_x_27724__boxed_1093_ = lean_unbox_usize(v_x_1091_);
lean_dec(v_x_1091_);
v_res_1094_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(v_x_1090_, v_x_27724__boxed_1093_, v_x_1092_);
lean_dec_ref(v_x_1092_);
lean_dec_ref(v_x_1090_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(lean_object* v_x_1095_, lean_object* v_x_1096_){
_start:
{
size_t v___x_1097_; size_t v___x_1098_; size_t v___x_1099_; uint64_t v___x_1100_; size_t v___x_1101_; lean_object* v___x_1102_; 
v___x_1097_ = lean_ptr_addr(v_x_1096_);
v___x_1098_ = ((size_t)3ULL);
v___x_1099_ = lean_usize_shift_right(v___x_1097_, v___x_1098_);
v___x_1100_ = lean_usize_to_uint64(v___x_1099_);
v___x_1101_ = lean_uint64_to_usize(v___x_1100_);
v___x_1102_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(v_x_1095_, v___x_1101_, v_x_1096_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg___boxed(lean_object* v_x_1103_, lean_object* v_x_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(v_x_1103_, v_x_1104_);
lean_dec_ref(v_x_1104_);
lean_dec_ref(v_x_1103_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4(lean_object* v_msgData_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
lean_object* v___x_1112_; lean_object* v_env_1113_; lean_object* v___x_1114_; lean_object* v_toCold_1115_; lean_object* v_mctx_1116_; lean_object* v_lctx_1117_; lean_object* v_options_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1112_ = lean_st_ref_get(v___y_1110_);
v_env_1113_ = lean_ctor_get(v___x_1112_, 0);
lean_inc_ref(v_env_1113_);
lean_dec(v___x_1112_);
v___x_1114_ = lean_st_ref_get(v___y_1108_);
v_toCold_1115_ = lean_ctor_get(v___y_1109_, 0);
v_mctx_1116_ = lean_ctor_get(v___x_1114_, 0);
lean_inc_ref(v_mctx_1116_);
lean_dec(v___x_1114_);
v_lctx_1117_ = lean_ctor_get(v___y_1107_, 2);
v_options_1118_ = lean_ctor_get(v_toCold_1115_, 2);
lean_inc_ref(v_options_1118_);
lean_inc_ref(v_lctx_1117_);
v___x_1119_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1119_, 0, v_env_1113_);
lean_ctor_set(v___x_1119_, 1, v_mctx_1116_);
lean_ctor_set(v___x_1119_, 2, v_lctx_1117_);
lean_ctor_set(v___x_1119_, 3, v_options_1118_);
v___x_1120_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
lean_ctor_set(v___x_1120_, 1, v_msgData_1106_);
v___x_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4___boxed(lean_object* v_msgData_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4(v_msgData_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
return v_res_1128_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1129_; double v___x_1130_; 
v___x_1129_ = lean_unsigned_to_nat(0u);
v___x_1130_ = lean_float_of_nat(v___x_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(lean_object* v_cls_1134_, lean_object* v_msg_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v_ref_1141_; lean_object* v___x_1142_; lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1188_; 
v_ref_1141_ = lean_ctor_get(v___y_1138_, 2);
v___x_1142_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4(v_msg_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1145_ = v___x_1142_;
v_isShared_1146_ = v_isSharedCheck_1188_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1142_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1188_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; lean_object* v_traceState_1148_; lean_object* v_env_1149_; lean_object* v_nextMacroScope_1150_; lean_object* v_ngen_1151_; lean_object* v_auxDeclNGen_1152_; lean_object* v_cache_1153_; lean_object* v_recordedDeps_1154_; lean_object* v_messages_1155_; lean_object* v_infoState_1156_; lean_object* v_snapshotTasks_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1187_; 
v___x_1147_ = lean_st_ref_take(v___y_1139_);
v_traceState_1148_ = lean_ctor_get(v___x_1147_, 4);
v_env_1149_ = lean_ctor_get(v___x_1147_, 0);
v_nextMacroScope_1150_ = lean_ctor_get(v___x_1147_, 1);
v_ngen_1151_ = lean_ctor_get(v___x_1147_, 2);
v_auxDeclNGen_1152_ = lean_ctor_get(v___x_1147_, 3);
v_cache_1153_ = lean_ctor_get(v___x_1147_, 5);
v_recordedDeps_1154_ = lean_ctor_get(v___x_1147_, 6);
v_messages_1155_ = lean_ctor_get(v___x_1147_, 7);
v_infoState_1156_ = lean_ctor_get(v___x_1147_, 8);
v_snapshotTasks_1157_ = lean_ctor_get(v___x_1147_, 9);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1159_ = v___x_1147_;
v_isShared_1160_ = v_isSharedCheck_1187_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_snapshotTasks_1157_);
lean_inc(v_infoState_1156_);
lean_inc(v_messages_1155_);
lean_inc(v_recordedDeps_1154_);
lean_inc(v_cache_1153_);
lean_inc(v_traceState_1148_);
lean_inc(v_auxDeclNGen_1152_);
lean_inc(v_ngen_1151_);
lean_inc(v_nextMacroScope_1150_);
lean_inc(v_env_1149_);
lean_dec(v___x_1147_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1187_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
uint64_t v_tid_1161_; lean_object* v_traces_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1186_; 
v_tid_1161_ = lean_ctor_get_uint64(v_traceState_1148_, sizeof(void*)*1);
v_traces_1162_ = lean_ctor_get(v_traceState_1148_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v_traceState_1148_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1164_ = v_traceState_1148_;
v_isShared_1165_ = v_isSharedCheck_1186_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_traces_1162_);
lean_dec(v_traceState_1148_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1186_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; double v___x_1168_; uint8_t v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1166_ = lean_box(0);
v___x_1167_ = lean_box(0);
v___x_1168_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0);
v___x_1169_ = 0;
v___x_1170_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__1));
v___x_1171_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1171_, 0, v_cls_1134_);
lean_ctor_set(v___x_1171_, 1, v___x_1167_);
lean_ctor_set(v___x_1171_, 2, v___x_1170_);
lean_ctor_set_float(v___x_1171_, sizeof(void*)*3, v___x_1168_);
lean_ctor_set_float(v___x_1171_, sizeof(void*)*3 + 8, v___x_1168_);
lean_ctor_set_uint8(v___x_1171_, sizeof(void*)*3 + 16, v___x_1169_);
v___x_1172_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__2));
v___x_1173_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1171_);
lean_ctor_set(v___x_1173_, 1, v_a_1143_);
lean_ctor_set(v___x_1173_, 2, v___x_1172_);
lean_inc(v_ref_1141_);
v___x_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1174_, 0, v_ref_1141_);
lean_ctor_set(v___x_1174_, 1, v___x_1173_);
v___x_1175_ = l_Lean_PersistentArray_push___redArg(v_traces_1162_, v___x_1174_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 0, v___x_1175_);
v___x_1177_ = v___x_1164_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1175_);
lean_ctor_set_uint64(v_reuseFailAlloc_1185_, sizeof(void*)*1, v_tid_1161_);
v___x_1177_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
lean_object* v___x_1179_; 
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 4, v___x_1177_);
v___x_1179_ = v___x_1159_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_env_1149_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v_nextMacroScope_1150_);
lean_ctor_set(v_reuseFailAlloc_1184_, 2, v_ngen_1151_);
lean_ctor_set(v_reuseFailAlloc_1184_, 3, v_auxDeclNGen_1152_);
lean_ctor_set(v_reuseFailAlloc_1184_, 4, v___x_1177_);
lean_ctor_set(v_reuseFailAlloc_1184_, 5, v_cache_1153_);
lean_ctor_set(v_reuseFailAlloc_1184_, 6, v_recordedDeps_1154_);
lean_ctor_set(v_reuseFailAlloc_1184_, 7, v_messages_1155_);
lean_ctor_set(v_reuseFailAlloc_1184_, 8, v_infoState_1156_);
lean_ctor_set(v_reuseFailAlloc_1184_, 9, v_snapshotTasks_1157_);
v___x_1179_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
lean_object* v___x_1180_; lean_object* v___x_1182_; 
v___x_1180_ = lean_st_ref_put(v___y_1139_, v___x_1179_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v___x_1166_);
v___x_1182_ = v___x_1145_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v___x_1166_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___boxed(lean_object* v_cls_1189_, lean_object* v_msg_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(v_cls_1189_, v_msg_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
return v_res_1196_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7(void){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1209_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4));
v___x_1210_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__6));
v___x_1211_ = l_Lean_Name_append(v___x_1210_, v___x_1209_);
return v___x_1211_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9(void){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__8));
v___x_1214_ = l_Lean_stringToMessageData(v___x_1213_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* lean_grind_cutsat_mk_var(lean_object* v_expr_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1216_, v_a_1224_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1357_; 
v_a_1228_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1230_ = v___x_1227_;
v_isShared_1231_ = v_isSharedCheck_1357_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v___x_1227_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1357_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v_varMap_1232_; lean_object* v___x_1233_; 
v_varMap_1232_ = lean_ctor_get(v_a_1228_, 1);
lean_inc_ref(v_varMap_1232_);
lean_dec(v_a_1228_);
v___x_1233_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(v_varMap_1232_, v_expr_1215_);
lean_dec_ref(v_varMap_1232_);
if (lean_obj_tag(v___x_1233_) == 1)
{
lean_object* v_val_1234_; lean_object* v___x_1236_; 
lean_dec(v_a_1225_);
lean_dec_ref(v_a_1224_);
lean_dec(v_a_1223_);
lean_dec_ref(v_a_1222_);
lean_dec(v_a_1221_);
lean_dec_ref(v_a_1220_);
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec(v_a_1216_);
lean_dec_ref(v_expr_1215_);
v_val_1234_ = lean_ctor_get(v___x_1233_, 0);
lean_inc(v_val_1234_);
lean_dec_ref_known(v___x_1233_, 1);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 0, v_val_1234_);
v___x_1236_ = v___x_1230_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_val_1234_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
else
{
lean_object* v___x_1238_; 
lean_dec(v___x_1233_);
lean_del_object(v___x_1230_);
v___x_1238_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1216_, v_a_1224_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; lean_object* v_vars_1240_; lean_object* v_toCold_1241_; lean_object* v_options_1242_; lean_object* v_size_1243_; lean_object* v_inheritedTraceOptions_1244_; uint8_t v_hasTrace_1245_; lean_object* v___f_1246_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1239_);
lean_dec_ref_known(v___x_1238_, 1);
v_vars_1240_ = lean_ctor_get(v_a_1239_, 0);
lean_inc_ref(v_vars_1240_);
lean_dec(v_a_1239_);
v_toCold_1241_ = lean_ctor_get(v_a_1224_, 0);
v_options_1242_ = lean_ctor_get(v_toCold_1241_, 2);
v_size_1243_ = lean_ctor_get(v_vars_1240_, 2);
lean_inc_n(v_size_1243_, 2);
lean_dec_ref(v_vars_1240_);
v_inheritedTraceOptions_1244_ = lean_ctor_get(v_toCold_1241_, 11);
v_hasTrace_1245_ = lean_ctor_get_uint8(v_options_1242_, sizeof(void*)*1);
lean_inc_ref(v_expr_1215_);
v___f_1246_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0), 3, 2);
lean_closure_set(v___f_1246_, 0, v_expr_1215_);
lean_closure_set(v___f_1246_, 1, v_size_1243_);
if (v_hasTrace_1245_ == 0)
{
v___y_1248_ = v_a_1216_;
v___y_1249_ = v_a_1217_;
v___y_1250_ = v_a_1218_;
v___y_1251_ = v_a_1219_;
v___y_1252_ = v_a_1220_;
v___y_1253_ = v_a_1221_;
v___y_1254_ = v_a_1222_;
v___y_1255_ = v_a_1223_;
v___y_1256_ = v_a_1224_;
v___y_1257_ = v_a_1225_;
goto v___jp_1247_;
}
else
{
lean_object* v___x_1330_; lean_object* v___x_1331_; uint8_t v___x_1332_; 
v___x_1330_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4));
v___x_1331_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7);
v___x_1332_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1244_, v_options_1242_, v___x_1331_);
if (v___x_1332_ == 0)
{
v___y_1248_ = v_a_1216_;
v___y_1249_ = v_a_1217_;
v___y_1250_ = v_a_1218_;
v___y_1251_ = v_a_1219_;
v___y_1252_ = v_a_1220_;
v___y_1253_ = v_a_1221_;
v___y_1254_ = v_a_1222_;
v___y_1255_ = v_a_1223_;
v___y_1256_ = v_a_1224_;
v___y_1257_ = v_a_1225_;
goto v___jp_1247_;
}
else
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
lean_inc_ref(v_expr_1215_);
v___x_1333_ = l_Lean_MessageData_ofExpr(v_expr_1215_);
v___x_1334_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9);
v___x_1335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1333_);
lean_ctor_set(v___x_1335_, 1, v___x_1334_);
lean_inc(v_size_1243_);
v___x_1336_ = l_Nat_reprFast(v_size_1243_);
v___x_1337_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1336_);
v___x_1338_ = l_Lean_MessageData_ofFormat(v___x_1337_);
v___x_1339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1335_);
lean_ctor_set(v___x_1339_, 1, v___x_1338_);
v___x_1340_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(v___x_1330_, v___x_1339_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_dec_ref_known(v___x_1340_, 1);
v___y_1248_ = v_a_1216_;
v___y_1249_ = v_a_1217_;
v___y_1250_ = v_a_1218_;
v___y_1251_ = v_a_1219_;
v___y_1252_ = v_a_1220_;
v___y_1253_ = v_a_1221_;
v___y_1254_ = v_a_1222_;
v___y_1255_ = v_a_1223_;
v___y_1256_ = v_a_1224_;
v___y_1257_ = v_a_1225_;
goto v___jp_1247_;
}
else
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
lean_dec_ref(v___f_1246_);
lean_dec(v_size_1243_);
lean_dec(v_a_1225_);
lean_dec_ref(v_a_1224_);
lean_dec(v_a_1223_);
lean_dec_ref(v_a_1222_);
lean_dec(v_a_1221_);
lean_dec_ref(v_a_1220_);
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec(v_a_1216_);
lean_dec_ref(v_expr_1215_);
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___x_1340_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1340_);
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
v___jp_1247_:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_1259_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1258_, v___f_1246_, v___y_1248_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v___x_1260_; 
lean_dec_ref_known(v___x_1259_, 1);
lean_inc_ref(v_expr_1215_);
v___x_1260_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_1258_, v_expr_1215_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v___x_1261_; 
lean_dec_ref_known(v___x_1260_, 1);
lean_inc(v_size_1243_);
lean_inc_ref(v_expr_1215_);
v___x_1261_ = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(v_expr_1215_, v_size_1243_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v___x_1262_; 
lean_dec_ref_known(v___x_1261_, 1);
lean_inc(v_size_1243_);
lean_inc_ref(v_expr_1215_);
v___x_1262_ = l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg(v_expr_1215_, v_size_1243_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v___x_1263_; 
lean_dec_ref_known(v___x_1262_, 1);
lean_inc_ref(v_expr_1215_);
v___x_1263_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm(v_expr_1215_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1289_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1266_ = v___x_1263_;
v_isShared_1267_ = v_isSharedCheck_1289_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1263_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1289_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
uint8_t v___x_1268_; 
v___x_1268_ = lean_unbox(v_a_1264_);
lean_dec(v_a_1264_);
if (v___x_1268_ == 0)
{
lean_object* v___x_1270_; 
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec_ref(v_expr_1215_);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 0, v_size_1243_);
v___x_1270_ = v___x_1266_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_size_1243_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
else
{
lean_object* v___x_1272_; 
lean_del_object(v___x_1266_);
lean_inc(v_size_1243_);
v___x_1272_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt(v_expr_1215_, v_size_1243_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec(v___y_1248_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1279_; 
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1279_ == 0)
{
lean_object* v_unused_1280_; 
v_unused_1280_ = lean_ctor_get(v___x_1272_, 0);
lean_dec(v_unused_1280_);
v___x_1274_ = v___x_1272_;
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
else
{
lean_dec(v___x_1272_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 0, v_size_1243_);
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_size_1243_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
lean_dec(v_size_1243_);
v_a_1281_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1272_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1272_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1281_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
}
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec(v_size_1243_);
lean_dec_ref(v_expr_1215_);
v_a_1290_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1263_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1263_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
else
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec(v_size_1243_);
lean_dec_ref(v_expr_1215_);
v_a_1298_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1262_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1262_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1298_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
}
else
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec(v_size_1243_);
lean_dec_ref(v_expr_1215_);
v_a_1306_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1308_ = v___x_1261_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1261_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_a_1306_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
else
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1321_; 
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec(v_size_1243_);
lean_dec_ref(v_expr_1215_);
v_a_1314_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1316_ = v___x_1260_;
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1260_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1319_; 
if (v_isShared_1317_ == 0)
{
v___x_1319_ = v___x_1316_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1314_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
else
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1329_; 
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec(v_size_1243_);
lean_dec_ref(v_expr_1215_);
v_a_1322_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1324_ = v___x_1259_;
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1259_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1327_; 
if (v_isShared_1325_ == 0)
{
v___x_1327_ = v___x_1324_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1322_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
}
}
else
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
lean_dec(v_a_1225_);
lean_dec_ref(v_a_1224_);
lean_dec(v_a_1223_);
lean_dec_ref(v_a_1222_);
lean_dec(v_a_1221_);
lean_dec_ref(v_a_1220_);
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec(v_a_1216_);
lean_dec_ref(v_expr_1215_);
v_a_1349_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1351_ = v___x_1238_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1238_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
}
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1365_; 
lean_dec(v_a_1225_);
lean_dec_ref(v_a_1224_);
lean_dec(v_a_1223_);
lean_dec_ref(v_a_1222_);
lean_dec(v_a_1221_);
lean_dec_ref(v_a_1220_);
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec(v_a_1216_);
lean_dec_ref(v_expr_1215_);
v_a_1358_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1360_ = v___x_1227_;
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1227_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1358_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___boxed(lean_object* v_expr_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = lean_grind_cutsat_mk_var(v_expr_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0(lean_object* v_00_u03b2_1379_, lean_object* v_x_1380_, lean_object* v_x_1381_){
_start:
{
lean_object* v___x_1382_; 
v___x_1382_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(v_x_1380_, v_x_1381_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___boxed(lean_object* v_00_u03b2_1383_, lean_object* v_x_1384_, lean_object* v_x_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0(v_00_u03b2_1383_, v_x_1384_, v_x_1385_);
lean_dec_ref(v_x_1385_);
lean_dec_ref(v_x_1384_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1(lean_object* v_00_u03b2_1387_, lean_object* v_x_1388_, lean_object* v_x_1389_, lean_object* v_x_1390_){
_start:
{
lean_object* v___x_1391_; 
v___x_1391_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg(v_x_1388_, v_x_1389_, v_x_1390_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2(lean_object* v_cls_1392_, lean_object* v_msg_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v___x_1405_; 
v___x_1405_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(v_cls_1392_, v_msg_1393_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___boxed(lean_object* v_cls_1406_, lean_object* v_msg_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2(v_cls_1406_, v_msg_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec(v___y_1409_);
lean_dec(v___y_1408_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0(lean_object* v_00_u03b2_1420_, lean_object* v_x_1421_, size_t v_x_1422_, lean_object* v_x_1423_){
_start:
{
lean_object* v___x_1424_; 
v___x_1424_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(v_x_1421_, v_x_1422_, v_x_1423_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1425_, lean_object* v_x_1426_, lean_object* v_x_1427_, lean_object* v_x_1428_){
_start:
{
size_t v_x_28297__boxed_1429_; lean_object* v_res_1430_; 
v_x_28297__boxed_1429_ = lean_unbox_usize(v_x_1427_);
lean_dec(v_x_1427_);
v_res_1430_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0(v_00_u03b2_1425_, v_x_1426_, v_x_28297__boxed_1429_, v_x_1428_);
lean_dec_ref(v_x_1428_);
lean_dec_ref(v_x_1426_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2(lean_object* v_00_u03b2_1431_, lean_object* v_x_1432_, size_t v_x_1433_, size_t v_x_1434_, lean_object* v_x_1435_, lean_object* v_x_1436_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_x_1432_, v_x_1433_, v_x_1434_, v_x_1435_, v_x_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1438_, lean_object* v_x_1439_, lean_object* v_x_1440_, lean_object* v_x_1441_, lean_object* v_x_1442_, lean_object* v_x_1443_){
_start:
{
size_t v_x_28308__boxed_1444_; size_t v_x_28309__boxed_1445_; lean_object* v_res_1446_; 
v_x_28308__boxed_1444_ = lean_unbox_usize(v_x_1440_);
lean_dec(v_x_1440_);
v_x_28309__boxed_1445_ = lean_unbox_usize(v_x_1441_);
lean_dec(v_x_1441_);
v_res_1446_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2(v_00_u03b2_1438_, v_x_1439_, v_x_28308__boxed_1444_, v_x_28309__boxed_1445_, v_x_1442_, v_x_1443_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1447_, lean_object* v_keys_1448_, lean_object* v_vals_1449_, lean_object* v_heq_1450_, lean_object* v_i_1451_, lean_object* v_k_1452_){
_start:
{
lean_object* v___x_1453_; 
v___x_1453_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(v_keys_1448_, v_vals_1449_, v_i_1451_, v_k_1452_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1454_, lean_object* v_keys_1455_, lean_object* v_vals_1456_, lean_object* v_heq_1457_, lean_object* v_i_1458_, lean_object* v_k_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1(v_00_u03b2_1454_, v_keys_1455_, v_vals_1456_, v_heq_1457_, v_i_1458_, v_k_1459_);
lean_dec_ref(v_k_1459_);
lean_dec_ref(v_vals_1456_);
lean_dec_ref(v_keys_1455_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1461_, lean_object* v_n_1462_, lean_object* v_k_1463_, lean_object* v_v_1464_){
_start:
{
lean_object* v___x_1465_; 
v___x_1465_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4___redArg(v_n_1462_, v_k_1463_, v_v_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1466_, size_t v_depth_1467_, lean_object* v_keys_1468_, lean_object* v_vals_1469_, lean_object* v_heq_1470_, lean_object* v_i_1471_, lean_object* v_entries_1472_){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(v_depth_1467_, v_keys_1468_, v_vals_1469_, v_i_1471_, v_entries_1472_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1474_, lean_object* v_depth_1475_, lean_object* v_keys_1476_, lean_object* v_vals_1477_, lean_object* v_heq_1478_, lean_object* v_i_1479_, lean_object* v_entries_1480_){
_start:
{
size_t v_depth_boxed_1481_; lean_object* v_res_1482_; 
v_depth_boxed_1481_ = lean_unbox_usize(v_depth_1475_);
lean_dec(v_depth_1475_);
v_res_1482_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5(v_00_u03b2_1474_, v_depth_boxed_1481_, v_keys_1476_, v_vals_1477_, v_heq_1478_, v_i_1479_, v_entries_1480_);
lean_dec_ref(v_vals_1477_);
lean_dec_ref(v_keys_1476_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_1483_, lean_object* v_x_1484_, lean_object* v_x_1485_, lean_object* v_x_1486_, lean_object* v_x_1487_){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7___redArg(v_x_1484_, v_x_1485_, v_x_1486_, v_x_1487_);
return v___x_1488_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2(void){
_start:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1492_ = lean_box(0);
v___x_1493_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__1));
v___x_1494_ = l_Lean_mkConst(v___x_1493_, v___x_1492_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(lean_object* v_e_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_){
_start:
{
lean_object* v___x_1501_; 
lean_inc(v_a_1499_);
lean_inc_ref(v_a_1498_);
lean_inc(v_a_1497_);
lean_inc_ref(v_a_1496_);
v___x_1501_ = lean_infer_type(v_e_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v_a_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v_a_1502_ = lean_ctor_get(v___x_1501_, 0);
lean_inc(v_a_1502_);
lean_dec_ref_known(v___x_1501_, 1);
v___x_1503_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2);
v___x_1504_ = l_Lean_Meta_isExprDefEq(v_a_1502_, v___x_1503_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_);
return v___x_1504_;
}
else
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1512_; 
v_a_1505_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1507_ = v___x_1501_;
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v___x_1501_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1510_; 
if (v_isShared_1508_ == 0)
{
v___x_1510_ = v___x_1507_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_a_1505_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___boxed(lean_object* v_e_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(v_e_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_);
lean_dec(v_a_1517_);
lean_dec_ref(v_a_1516_);
lean_dec(v_a_1515_);
lean_dec_ref(v_a_1514_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt(lean_object* v_e_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(v_e_1520_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___boxed(lean_object* v_e_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_Lean_Meta_Grind_Arith_Cutsat_isInt(v_e_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_);
lean_dec(v_a_1543_);
lean_dec_ref(v_a_1542_);
lean_dec(v_a_1541_);
lean_dec_ref(v_a_1540_);
lean_dec(v_a_1539_);
lean_dec_ref(v_a_1538_);
lean_dec(v_a_1537_);
lean_dec_ref(v_a_1536_);
lean_dec(v_a_1535_);
lean_dec(v_a_1534_);
return v_res_1545_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4(void){
_start:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1552_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__3));
v___x_1553_ = l_Lean_stringToMessageData(v___x_1552_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(lean_object* v_e_1554_, uint8_t v_report_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_){
_start:
{
lean_object* v___x_1569_; 
lean_inc_ref(v_e_1554_);
v___x_1569_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1554_, v_a_1559_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v___x_1571_; uint8_t v___x_1572_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_a_1570_);
lean_dec_ref_known(v___x_1569_, 1);
v___x_1571_ = l_Lean_Expr_cleanupAnnotations(v_a_1570_);
v___x_1572_ = l_Lean_Expr_isApp(v___x_1571_);
if (v___x_1572_ == 0)
{
lean_dec_ref(v___x_1571_);
lean_dec_ref(v_e_1554_);
goto v___jp_1563_;
}
else
{
lean_object* v_arg_1573_; lean_object* v___x_1574_; uint8_t v___x_1575_; 
v_arg_1573_ = lean_ctor_get(v___x_1571_, 1);
lean_inc_ref(v_arg_1573_);
v___x_1574_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1571_);
v___x_1575_ = l_Lean_Expr_isApp(v___x_1574_);
if (v___x_1575_ == 0)
{
lean_dec_ref(v___x_1574_);
lean_dec_ref(v_arg_1573_);
lean_dec_ref(v_e_1554_);
goto v___jp_1563_;
}
else
{
lean_object* v_arg_1576_; lean_object* v___x_1577_; uint8_t v___x_1578_; 
v_arg_1576_ = lean_ctor_get(v___x_1574_, 1);
lean_inc_ref(v_arg_1576_);
v___x_1577_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1574_);
v___x_1578_ = l_Lean_Expr_isApp(v___x_1577_);
if (v___x_1578_ == 0)
{
lean_dec_ref(v___x_1577_);
lean_dec_ref(v_arg_1576_);
lean_dec_ref(v_arg_1573_);
lean_dec_ref(v_e_1554_);
goto v___jp_1563_;
}
else
{
lean_object* v_arg_1579_; lean_object* v___x_1580_; uint8_t v___x_1581_; 
v_arg_1579_ = lean_ctor_get(v___x_1577_, 1);
lean_inc_ref(v_arg_1579_);
v___x_1580_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1577_);
v___x_1581_ = l_Lean_Expr_isApp(v___x_1580_);
if (v___x_1581_ == 0)
{
lean_dec_ref(v___x_1580_);
lean_dec_ref(v_arg_1579_);
lean_dec_ref(v_arg_1576_);
lean_dec_ref(v_arg_1573_);
lean_dec_ref(v_e_1554_);
goto v___jp_1563_;
}
else
{
lean_object* v___x_1582_; uint8_t v___x_1583_; 
v___x_1582_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1580_);
v___x_1583_ = l_Lean_Expr_isApp(v___x_1582_);
if (v___x_1583_ == 0)
{
lean_dec_ref(v___x_1582_);
lean_dec_ref(v_arg_1579_);
lean_dec_ref(v_arg_1576_);
lean_dec_ref(v_arg_1573_);
lean_dec_ref(v_e_1554_);
goto v___jp_1563_;
}
else
{
lean_object* v___x_1584_; uint8_t v___x_1585_; 
v___x_1584_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1582_);
v___x_1585_ = l_Lean_Expr_isApp(v___x_1584_);
if (v___x_1585_ == 0)
{
lean_dec_ref(v___x_1584_);
lean_dec_ref(v_arg_1579_);
lean_dec_ref(v_arg_1576_);
lean_dec_ref(v_arg_1573_);
lean_dec_ref(v_e_1554_);
goto v___jp_1563_;
}
else
{
lean_object* v___x_1586_; lean_object* v___x_1587_; uint8_t v___x_1588_; 
v___x_1586_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1584_);
v___x_1587_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__2));
v___x_1588_ = l_Lean_Expr_isConstOf(v___x_1586_, v___x_1587_);
lean_dec_ref(v___x_1586_);
if (v___x_1588_ == 0)
{
lean_dec_ref(v_arg_1579_);
lean_dec_ref(v_arg_1576_);
lean_dec_ref(v_arg_1573_);
lean_dec_ref(v_e_1554_);
goto v___jp_1563_;
}
else
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Lean_Meta_Structural_isInstHAddInt___redArg(v_arg_1579_, v_a_1559_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1623_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1592_ = v___x_1589_;
v_isShared_1593_ = v_isSharedCheck_1623_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1589_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1623_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
uint8_t v___x_1594_; 
v___x_1594_ = lean_unbox(v_a_1590_);
lean_dec(v_a_1590_);
if (v___x_1594_ == 0)
{
lean_del_object(v___x_1592_);
lean_dec_ref(v_arg_1576_);
lean_dec_ref(v_arg_1573_);
if (v_report_1555_ == 0)
{
lean_dec_ref(v_e_1554_);
goto v___jp_1566_;
}
else
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1595_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4);
v___x_1596_ = l_Lean_indentExpr(v_e_1554_);
v___x_1597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1595_);
lean_ctor_set(v___x_1597_, 1, v___x_1596_);
v___x_1598_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1556_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; uint8_t v_verbose_1600_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
lean_dec_ref_known(v___x_1598_, 1);
v_verbose_1600_ = lean_ctor_get_uint8(v_a_1599_, 0);
lean_dec(v_a_1599_);
if (v_verbose_1600_ == 0)
{
lean_dec_ref_known(v___x_1597_, 2);
goto v___jp_1566_;
}
else
{
lean_object* v___x_1601_; 
v___x_1601_ = l_Lean_Meta_Sym_reportIssue(v___x_1597_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_dec_ref_known(v___x_1601_, 1);
goto v___jp_1566_;
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1601_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1601_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1602_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
}
else
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
lean_dec_ref_known(v___x_1597_, 2);
v_a_1610_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1612_ = v___x_1598_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1598_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1615_; 
if (v_isShared_1613_ == 0)
{
v___x_1615_ = v___x_1612_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_a_1610_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
}
else
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1621_; 
lean_dec_ref(v_e_1554_);
v___x_1618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1618_, 0, v_arg_1576_);
lean_ctor_set(v___x_1618_, 1, v_arg_1573_);
v___x_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 0, v___x_1619_);
v___x_1621_ = v___x_1592_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1619_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
else
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
lean_dec_ref(v_arg_1576_);
lean_dec_ref(v_arg_1573_);
lean_dec_ref(v_e_1554_);
v_a_1624_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1626_ = v___x_1589_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1589_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1624_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
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
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
lean_dec_ref(v_e_1554_);
v_a_1632_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1569_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1569_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
v___jp_1563_:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1564_ = lean_box(0);
v___x_1565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1564_);
return v___x_1565_;
}
v___jp_1566_:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1567_ = lean_box(0);
v___x_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1567_);
return v___x_1568_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___boxed(lean_object* v_e_1640_, lean_object* v_report_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_){
_start:
{
uint8_t v_report_boxed_1649_; lean_object* v_res_1650_; 
v_report_boxed_1649_ = lean_unbox(v_report_1641_);
v_res_1650_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_1640_, v_report_boxed_1649_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_);
lean_dec(v_a_1647_);
lean_dec_ref(v_a_1646_);
lean_dec(v_a_1645_);
lean_dec_ref(v_a_1644_);
lean_dec(v_a_1643_);
lean_dec_ref(v_a_1642_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f(lean_object* v_e_1651_, uint8_t v_report_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_1651_, v_report_1652_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___boxed(lean_object* v_e_1665_, lean_object* v_report_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_){
_start:
{
uint8_t v_report_boxed_1678_; lean_object* v_res_1679_; 
v_report_boxed_1678_ = lean_unbox(v_report_1666_);
v_res_1679_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f(v_e_1665_, v_report_boxed_1678_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_);
lean_dec(v_a_1676_);
lean_dec_ref(v_a_1675_);
lean_dec(v_a_1674_);
lean_dec_ref(v_a_1673_);
lean_dec(v_a_1672_);
lean_dec_ref(v_a_1671_);
lean_dec(v_a_1670_);
lean_dec_ref(v_a_1669_);
lean_dec(v_a_1668_);
lean_dec(v_a_1667_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(lean_object* v_e_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_){
_start:
{
uint8_t v___x_1688_; lean_object* v___x_1689_; 
v___x_1688_ = 0;
v___x_1689_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_1680_, v___x_1688_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1703_; 
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1692_ = v___x_1689_;
v_isShared_1693_ = v_isSharedCheck_1703_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1689_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1703_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
if (lean_obj_tag(v_a_1690_) == 0)
{
lean_object* v___x_1694_; lean_object* v___x_1696_; 
v___x_1694_ = lean_box(v___x_1688_);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 0, v___x_1694_);
v___x_1696_ = v___x_1692_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v___x_1694_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
else
{
uint8_t v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1701_; 
lean_dec_ref_known(v_a_1690_, 1);
v___x_1698_ = 1;
v___x_1699_ = lean_box(v___x_1698_);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 0, v___x_1699_);
v___x_1701_ = v___x_1692_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1699_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
else
{
lean_object* v_a_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1711_; 
v_a_1704_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1706_ = v___x_1689_;
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_a_1704_);
lean_dec(v___x_1689_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1709_; 
if (v_isShared_1707_ == 0)
{
v___x_1709_ = v___x_1706_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_a_1704_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg___boxed(lean_object* v_e_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(v_e_1712_, v_a_1713_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_, v_a_1718_);
lean_dec(v_a_1718_);
lean_dec_ref(v_a_1717_);
lean_dec(v_a_1716_);
lean_dec_ref(v_a_1715_);
lean_dec(v_a_1714_);
lean_dec_ref(v_a_1713_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd(lean_object* v_e_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_){
_start:
{
lean_object* v___x_1733_; 
v___x_1733_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(v_e_1721_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___boxed(lean_object* v_e_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd(v_e_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_);
lean_dec(v_a_1744_);
lean_dec_ref(v_a_1743_);
lean_dec(v_a_1742_);
lean_dec_ref(v_a_1741_);
lean_dec(v_a_1740_);
lean_dec_ref(v_a_1739_);
lean_dec(v_a_1738_);
lean_dec_ref(v_a_1737_);
lean_dec(v_a_1736_);
lean_dec(v_a_1735_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(lean_object* v_e_1747_, uint8_t v_report_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_){
_start:
{
lean_object* v___x_1762_; 
lean_inc_ref(v_e_1747_);
v___x_1762_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1747_, v_a_1752_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v_a_1763_; lean_object* v___x_1764_; uint8_t v___x_1765_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
lean_inc(v_a_1763_);
lean_dec_ref_known(v___x_1762_, 1);
v___x_1764_ = l_Lean_Expr_cleanupAnnotations(v_a_1763_);
v___x_1765_ = l_Lean_Expr_isApp(v___x_1764_);
if (v___x_1765_ == 0)
{
lean_dec_ref(v___x_1764_);
lean_dec_ref(v_e_1747_);
goto v___jp_1756_;
}
else
{
lean_object* v_arg_1766_; lean_object* v___x_1767_; uint8_t v___x_1768_; 
v_arg_1766_ = lean_ctor_get(v___x_1764_, 1);
lean_inc_ref(v_arg_1766_);
v___x_1767_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1764_);
v___x_1768_ = l_Lean_Expr_isApp(v___x_1767_);
if (v___x_1768_ == 0)
{
lean_dec_ref(v___x_1767_);
lean_dec_ref(v_arg_1766_);
lean_dec_ref(v_e_1747_);
goto v___jp_1756_;
}
else
{
lean_object* v_arg_1769_; lean_object* v___x_1770_; uint8_t v___x_1771_; 
v_arg_1769_ = lean_ctor_get(v___x_1767_, 1);
lean_inc_ref(v_arg_1769_);
v___x_1770_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1767_);
v___x_1771_ = l_Lean_Expr_isApp(v___x_1770_);
if (v___x_1771_ == 0)
{
lean_dec_ref(v___x_1770_);
lean_dec_ref(v_arg_1769_);
lean_dec_ref(v_arg_1766_);
lean_dec_ref(v_e_1747_);
goto v___jp_1756_;
}
else
{
lean_object* v_arg_1772_; lean_object* v___x_1773_; uint8_t v___x_1774_; 
v_arg_1772_ = lean_ctor_get(v___x_1770_, 1);
lean_inc_ref(v_arg_1772_);
v___x_1773_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1770_);
v___x_1774_ = l_Lean_Expr_isApp(v___x_1773_);
if (v___x_1774_ == 0)
{
lean_dec_ref(v___x_1773_);
lean_dec_ref(v_arg_1772_);
lean_dec_ref(v_arg_1769_);
lean_dec_ref(v_arg_1766_);
lean_dec_ref(v_e_1747_);
goto v___jp_1756_;
}
else
{
lean_object* v___x_1775_; uint8_t v___x_1776_; 
v___x_1775_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1773_);
v___x_1776_ = l_Lean_Expr_isApp(v___x_1775_);
if (v___x_1776_ == 0)
{
lean_dec_ref(v___x_1775_);
lean_dec_ref(v_arg_1772_);
lean_dec_ref(v_arg_1769_);
lean_dec_ref(v_arg_1766_);
lean_dec_ref(v_e_1747_);
goto v___jp_1756_;
}
else
{
lean_object* v___x_1777_; uint8_t v___x_1778_; 
v___x_1777_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1775_);
v___x_1778_ = l_Lean_Expr_isApp(v___x_1777_);
if (v___x_1778_ == 0)
{
lean_dec_ref(v___x_1777_);
lean_dec_ref(v_arg_1772_);
lean_dec_ref(v_arg_1769_);
lean_dec_ref(v_arg_1766_);
lean_dec_ref(v_e_1747_);
goto v___jp_1756_;
}
else
{
lean_object* v___x_1779_; lean_object* v___x_1780_; uint8_t v___x_1781_; 
v___x_1779_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1777_);
v___x_1780_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11));
v___x_1781_ = l_Lean_Expr_isConstOf(v___x_1779_, v___x_1780_);
lean_dec_ref(v___x_1779_);
if (v___x_1781_ == 0)
{
lean_dec_ref(v_arg_1772_);
lean_dec_ref(v_arg_1769_);
lean_dec_ref(v_arg_1766_);
lean_dec_ref(v_e_1747_);
goto v___jp_1756_;
}
else
{
lean_object* v___x_1782_; 
v___x_1782_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_1772_, v_a_1752_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; uint8_t v___x_1784_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc(v_a_1783_);
lean_dec_ref_known(v___x_1782_, 1);
v___x_1784_ = lean_unbox(v_a_1783_);
lean_dec(v_a_1783_);
if (v___x_1784_ == 0)
{
lean_dec_ref(v_arg_1769_);
lean_dec_ref(v_arg_1766_);
if (v_report_1748_ == 0)
{
lean_dec_ref(v_e_1747_);
goto v___jp_1759_;
}
else
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1785_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4);
v___x_1786_ = l_Lean_indentExpr(v_e_1747_);
v___x_1787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1785_);
lean_ctor_set(v___x_1787_, 1, v___x_1786_);
v___x_1788_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1749_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; uint8_t v_verbose_1790_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_a_1789_);
lean_dec_ref_known(v___x_1788_, 1);
v_verbose_1790_ = lean_ctor_get_uint8(v_a_1789_, 0);
lean_dec(v_a_1789_);
if (v_verbose_1790_ == 0)
{
lean_dec_ref_known(v___x_1787_, 2);
goto v___jp_1759_;
}
else
{
lean_object* v___x_1791_; 
v___x_1791_ = l_Lean_Meta_Sym_reportIssue(v___x_1787_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_dec_ref_known(v___x_1791_, 1);
goto v___jp_1759_;
}
else
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1799_; 
v_a_1792_ = lean_ctor_get(v___x_1791_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1794_ = v___x_1791_;
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1791_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1797_; 
if (v_isShared_1795_ == 0)
{
v___x_1797_ = v___x_1794_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_a_1792_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
}
}
else
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1807_; 
lean_dec_ref_known(v___x_1787_, 2);
v_a_1800_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1802_ = v___x_1788_;
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1788_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1805_; 
if (v_isShared_1803_ == 0)
{
v___x_1805_ = v___x_1802_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_a_1800_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
}
}
else
{
lean_object* v___x_1808_; 
lean_dec_ref(v_e_1747_);
v___x_1808_ = l_Lean_Meta_getIntValue_x3f(v_arg_1769_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1829_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1811_ = v___x_1808_;
v_isShared_1812_ = v_isSharedCheck_1829_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1808_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1829_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
if (lean_obj_tag(v_a_1809_) == 1)
{
lean_object* v_val_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1824_; 
v_val_1813_ = lean_ctor_get(v_a_1809_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v_a_1809_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1815_ = v_a_1809_;
v_isShared_1816_ = v_isSharedCheck_1824_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_val_1813_);
lean_dec(v_a_1809_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1824_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1817_; lean_object* v___x_1819_; 
v___x_1817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1817_, 0, v_val_1813_);
lean_ctor_set(v___x_1817_, 1, v_arg_1766_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 0, v___x_1817_);
v___x_1819_ = v___x_1815_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v___x_1817_);
v___x_1819_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
lean_object* v___x_1821_; 
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 0, v___x_1819_);
v___x_1821_ = v___x_1811_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1819_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
}
else
{
lean_object* v___x_1825_; lean_object* v___x_1827_; 
lean_dec(v_a_1809_);
lean_dec_ref(v_arg_1766_);
v___x_1825_ = lean_box(0);
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 0, v___x_1825_);
v___x_1827_ = v___x_1811_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v___x_1825_);
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
else
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1837_; 
lean_dec_ref(v_arg_1766_);
v_a_1830_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1832_ = v___x_1808_;
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1808_);
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
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1845_; 
lean_dec_ref(v_arg_1769_);
lean_dec_ref(v_arg_1766_);
lean_dec_ref(v_e_1747_);
v_a_1838_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1840_ = v___x_1782_;
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1782_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1843_; 
if (v_isShared_1841_ == 0)
{
v___x_1843_ = v___x_1840_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1838_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
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
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1853_; 
lean_dec_ref(v_e_1747_);
v_a_1846_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1848_ = v___x_1762_;
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1762_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1851_; 
if (v_isShared_1849_ == 0)
{
v___x_1851_ = v___x_1848_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_a_1846_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
}
v___jp_1756_:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1757_ = lean_box(0);
v___x_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1757_);
return v___x_1758_;
}
v___jp_1759_:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1760_ = lean_box(0);
v___x_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1760_);
return v___x_1761_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg___boxed(lean_object* v_e_1854_, lean_object* v_report_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_){
_start:
{
uint8_t v_report_boxed_1863_; lean_object* v_res_1864_; 
v_report_boxed_1863_ = lean_unbox(v_report_1855_);
v_res_1864_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1854_, v_report_boxed_1863_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
lean_dec(v_a_1861_);
lean_dec_ref(v_a_1860_);
lean_dec(v_a_1859_);
lean_dec_ref(v_a_1858_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f(lean_object* v_e_1865_, uint8_t v_report_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1865_, v_report_1866_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___boxed(lean_object* v_e_1879_, lean_object* v_report_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_){
_start:
{
uint8_t v_report_boxed_1892_; lean_object* v_res_1893_; 
v_report_boxed_1892_ = lean_unbox(v_report_1880_);
v_res_1893_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f(v_e_1879_, v_report_boxed_1892_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
lean_dec(v_a_1890_);
lean_dec_ref(v_a_1889_);
lean_dec(v_a_1888_);
lean_dec_ref(v_a_1887_);
lean_dec(v_a_1886_);
lean_dec_ref(v_a_1885_);
lean_dec(v_a_1884_);
lean_dec_ref(v_a_1883_);
lean_dec(v_a_1882_);
lean_dec(v_a_1881_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(lean_object* v_e_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_){
_start:
{
uint8_t v___x_1902_; lean_object* v___x_1903_; 
v___x_1902_ = 0;
v___x_1903_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1894_, v___x_1902_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_);
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1917_; 
v_a_1904_ = lean_ctor_get(v___x_1903_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1906_ = v___x_1903_;
v_isShared_1907_ = v_isSharedCheck_1917_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1903_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1917_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
if (lean_obj_tag(v_a_1904_) == 0)
{
lean_object* v___x_1908_; lean_object* v___x_1910_; 
v___x_1908_ = lean_box(v___x_1902_);
if (v_isShared_1907_ == 0)
{
lean_ctor_set(v___x_1906_, 0, v___x_1908_);
v___x_1910_ = v___x_1906_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1908_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
else
{
uint8_t v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1915_; 
lean_dec_ref_known(v_a_1904_, 1);
v___x_1912_ = 1;
v___x_1913_ = lean_box(v___x_1912_);
if (v_isShared_1907_ == 0)
{
lean_ctor_set(v___x_1906_, 0, v___x_1913_);
v___x_1915_ = v___x_1906_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v___x_1913_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
}
else
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1925_; 
v_a_1918_ = lean_ctor_get(v___x_1903_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1920_ = v___x_1903_;
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1903_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1923_; 
if (v_isShared_1921_ == 0)
{
v___x_1923_ = v___x_1920_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_a_1918_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg___boxed(lean_object* v_e_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(v_e_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_);
lean_dec(v_a_1932_);
lean_dec_ref(v_a_1931_);
lean_dec(v_a_1930_);
lean_dec_ref(v_a_1929_);
lean_dec(v_a_1928_);
lean_dec_ref(v_a_1927_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul(lean_object* v_e_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_){
_start:
{
lean_object* v___x_1947_; 
v___x_1947_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(v_e_1935_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___boxed(lean_object* v_e_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul(v_e_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_);
lean_dec(v_a_1958_);
lean_dec_ref(v_a_1957_);
lean_dec(v_a_1956_);
lean_dec_ref(v_a_1955_);
lean_dec(v_a_1954_);
lean_dec_ref(v_a_1953_);
lean_dec(v_a_1952_);
lean_dec_ref(v_a_1951_);
lean_dec(v_a_1950_);
lean_dec(v_a_1949_);
return v_res_1960_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0(void){
_start:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1961_ = lean_unsigned_to_nat(1u);
v___x_1962_ = lean_nat_to_int(v___x_1961_);
return v___x_1962_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2(void){
_start:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1964_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__1));
v___x_1965_ = l_Lean_stringToMessageData(v___x_1964_);
return v___x_1965_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4(void){
_start:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1967_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__3));
v___x_1968_ = l_Lean_stringToMessageData(v___x_1967_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(lean_object* v_e_1969_, lean_object* v_p_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_){
_start:
{
lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; uint8_t v___x_2012_; lean_object* v___x_2013_; 
v___x_2012_ = 1;
lean_inc_ref(v_e_1969_);
v___x_2013_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1969_, v___x_2012_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v_a_2014_; 
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2014_);
lean_dec_ref_known(v___x_2013_, 1);
if (lean_obj_tag(v_a_2014_) == 1)
{
lean_object* v_val_2015_; lean_object* v_fst_2016_; lean_object* v_snd_2017_; lean_object* v___x_2018_; 
lean_dec_ref(v_e_1969_);
v_val_2015_ = lean_ctor_get(v_a_2014_, 0);
lean_inc(v_val_2015_);
lean_dec_ref_known(v_a_2014_, 1);
v_fst_2016_ = lean_ctor_get(v_val_2015_, 0);
lean_inc(v_fst_2016_);
v_snd_2017_ = lean_ctor_get(v_val_2015_, 1);
lean_inc(v_snd_2017_);
lean_dec(v_val_2015_);
lean_inc(v_a_1980_);
lean_inc_ref(v_a_1979_);
lean_inc(v_a_1978_);
lean_inc_ref(v_a_1977_);
lean_inc(v_a_1976_);
lean_inc_ref(v_a_1975_);
lean_inc(v_a_1974_);
lean_inc_ref(v_a_1973_);
lean_inc(v_a_1972_);
lean_inc(v_a_1971_);
v___x_2018_ = lean_grind_cutsat_mk_var(v_snd_2017_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2027_; 
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2021_ = v___x_2018_;
v_isShared_2022_ = v_isSharedCheck_2027_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_2018_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2027_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2023_; lean_object* v___x_2025_; 
v___x_2023_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2023_, 0, v_fst_2016_);
lean_ctor_set(v___x_2023_, 1, v_a_2019_);
lean_ctor_set(v___x_2023_, 2, v_p_1970_);
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 0, v___x_2023_);
v___x_2025_ = v___x_2021_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2023_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
else
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
lean_dec(v_fst_2016_);
lean_dec_ref(v_p_1970_);
v_a_2028_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2030_ = v___x_2018_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2018_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2028_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
else
{
lean_object* v___x_2036_; 
lean_dec(v_a_2014_);
lean_inc_ref(v_e_1969_);
v___x_2036_ = l_Lean_Meta_getIntValue_x3f(v_e_1969_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2078_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2039_ = v___x_2036_;
v_isShared_2040_ = v_isSharedCheck_2078_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_2036_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2078_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
if (lean_obj_tag(v_a_2037_) == 1)
{
lean_object* v_val_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2077_; 
v_val_2041_ = lean_ctor_get(v_a_2037_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v_a_2037_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2043_ = v_a_2037_;
v_isShared_2044_ = v_isSharedCheck_2077_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_val_2041_);
lean_dec(v_a_2037_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2077_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
uint8_t v___x_2045_; 
v___x_2045_ = l_Int_Internal_Linear_Poly_isZero(v_p_1970_);
if (v___x_2045_ == 0)
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
lean_del_object(v___x_2043_);
lean_dec(v_val_2041_);
lean_del_object(v___x_2039_);
v___x_2046_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2);
lean_inc_ref(v_e_1969_);
v___x_2047_ = l_Lean_indentExpr(v_e_1969_);
v___x_2048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2046_);
lean_ctor_set(v___x_2048_, 1, v___x_2047_);
v___x_2049_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4);
v___x_2050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2048_);
lean_ctor_set(v___x_2050_, 1, v___x_2049_);
v___x_2051_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1975_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; uint8_t v_verbose_2053_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_a_2052_);
lean_dec_ref_known(v___x_2051_, 1);
v_verbose_2053_ = lean_ctor_get_uint8(v_a_2052_, 0);
lean_dec(v_a_2052_);
if (v_verbose_2053_ == 0)
{
lean_dec_ref_known(v___x_2050_, 2);
v___y_1983_ = v_a_1971_;
v___y_1984_ = v_a_1972_;
v___y_1985_ = v_a_1973_;
v___y_1986_ = v_a_1974_;
v___y_1987_ = v_a_1975_;
v___y_1988_ = v_a_1976_;
v___y_1989_ = v_a_1977_;
v___y_1990_ = v_a_1978_;
v___y_1991_ = v_a_1979_;
v___y_1992_ = v_a_1980_;
goto v___jp_1982_;
}
else
{
lean_object* v___x_2054_; 
v___x_2054_ = l_Lean_Meta_Sym_reportIssue(v___x_2050_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_dec_ref_known(v___x_2054_, 1);
v___y_1983_ = v_a_1971_;
v___y_1984_ = v_a_1972_;
v___y_1985_ = v_a_1973_;
v___y_1986_ = v_a_1974_;
v___y_1987_ = v_a_1975_;
v___y_1988_ = v_a_1976_;
v___y_1989_ = v_a_1977_;
v___y_1990_ = v_a_1978_;
v___y_1991_ = v_a_1979_;
v___y_1992_ = v_a_1980_;
goto v___jp_1982_;
}
else
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2062_; 
lean_dec_ref(v_p_1970_);
lean_dec_ref(v_e_1969_);
v_a_2055_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2057_ = v___x_2054_;
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_2054_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2060_; 
if (v_isShared_2058_ == 0)
{
v___x_2060_ = v___x_2057_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_a_2055_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
}
else
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
lean_dec_ref_known(v___x_2050_, 2);
lean_dec_ref(v_p_1970_);
lean_dec_ref(v_e_1969_);
v_a_2063_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___x_2051_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2051_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_a_2063_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
}
else
{
lean_object* v___x_2072_; 
lean_dec_ref(v_p_1970_);
lean_dec_ref(v_e_1969_);
if (v_isShared_2044_ == 0)
{
lean_ctor_set_tag(v___x_2043_, 0);
v___x_2072_ = v___x_2043_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_val_2041_);
v___x_2072_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
lean_object* v___x_2074_; 
if (v_isShared_2040_ == 0)
{
lean_ctor_set(v___x_2039_, 0, v___x_2072_);
v___x_2074_ = v___x_2039_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2072_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
}
}
else
{
lean_del_object(v___x_2039_);
lean_dec(v_a_2037_);
v___y_1983_ = v_a_1971_;
v___y_1984_ = v_a_1972_;
v___y_1985_ = v_a_1973_;
v___y_1986_ = v_a_1974_;
v___y_1987_ = v_a_1975_;
v___y_1988_ = v_a_1976_;
v___y_1989_ = v_a_1977_;
v___y_1990_ = v_a_1978_;
v___y_1991_ = v_a_1979_;
v___y_1992_ = v_a_1980_;
goto v___jp_1982_;
}
}
}
else
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2086_; 
lean_dec_ref(v_p_1970_);
lean_dec_ref(v_e_1969_);
v_a_2079_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2081_ = v___x_2036_;
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2036_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2084_; 
if (v_isShared_2082_ == 0)
{
v___x_2084_ = v___x_2081_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_a_2079_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
}
}
else
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
lean_dec_ref(v_p_1970_);
lean_dec_ref(v_e_1969_);
v_a_2087_ = lean_ctor_get(v___x_2013_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_2013_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2013_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
v___jp_1982_:
{
lean_object* v___x_1993_; 
lean_inc(v___y_1992_);
lean_inc_ref(v___y_1991_);
lean_inc(v___y_1990_);
lean_inc_ref(v___y_1989_);
lean_inc(v___y_1988_);
lean_inc_ref(v___y_1987_);
lean_inc(v___y_1986_);
lean_inc_ref(v___y_1985_);
lean_inc(v___y_1984_);
lean_inc(v___y_1983_);
v___x_1993_ = lean_grind_cutsat_mk_var(v_e_1969_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2003_; 
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1996_ = v___x_1993_;
v_isShared_1997_ = v_isSharedCheck_2003_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1993_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2003_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2001_; 
v___x_1998_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0);
v___x_1999_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1998_);
lean_ctor_set(v___x_1999_, 1, v_a_1994_);
lean_ctor_set(v___x_1999_, 2, v_p_1970_);
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 0, v___x_1999_);
v___x_2001_ = v___x_1996_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1999_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
else
{
lean_object* v_a_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2011_; 
lean_dec_ref(v_p_1970_);
v_a_2004_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2006_ = v___x_1993_;
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_a_2004_);
lean_dec(v___x_1993_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2009_; 
if (v_isShared_2007_ == 0)
{
v___x_2009_ = v___x_2006_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_a_2004_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___boxed(lean_object* v_e_2095_, lean_object* v_p_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_){
_start:
{
lean_object* v_res_2108_; 
v_res_2108_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_e_2095_, v_p_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_);
lean_dec(v_a_2106_);
lean_dec_ref(v_a_2105_);
lean_dec(v_a_2104_);
lean_dec_ref(v_a_2103_);
lean_dec(v_a_2102_);
lean_dec_ref(v_a_2101_);
lean_dec(v_a_2100_);
lean_dec_ref(v_a_2099_);
lean_dec(v_a_2098_);
lean_dec(v_a_2097_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go(lean_object* v_e_2109_, lean_object* v_p_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_){
_start:
{
uint8_t v___x_2122_; lean_object* v___x_2123_; 
v___x_2122_ = 1;
lean_inc_ref(v_e_2109_);
v___x_2123_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_2109_, v___x_2122_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; 
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc(v_a_2124_);
lean_dec_ref_known(v___x_2123_, 1);
if (lean_obj_tag(v_a_2124_) == 1)
{
lean_object* v_val_2125_; lean_object* v_fst_2126_; lean_object* v_snd_2127_; lean_object* v___x_2128_; 
lean_dec_ref(v_e_2109_);
v_val_2125_ = lean_ctor_get(v_a_2124_, 0);
lean_inc(v_val_2125_);
lean_dec_ref_known(v_a_2124_, 1);
v_fst_2126_ = lean_ctor_get(v_val_2125_, 0);
lean_inc(v_fst_2126_);
v_snd_2127_ = lean_ctor_get(v_val_2125_, 1);
lean_inc(v_snd_2127_);
lean_dec(v_val_2125_);
v___x_2128_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_snd_2127_, v_p_2110_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v_a_2129_; 
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
lean_inc(v_a_2129_);
lean_dec_ref_known(v___x_2128_, 1);
v_e_2109_ = v_fst_2126_;
v_p_2110_ = v_a_2129_;
goto _start;
}
else
{
lean_dec(v_fst_2126_);
return v___x_2128_;
}
}
else
{
lean_object* v___x_2131_; 
lean_dec(v_a_2124_);
v___x_2131_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_e_2109_, v_p_2110_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
return v___x_2131_;
}
}
else
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2139_; 
lean_dec_ref(v_p_2110_);
lean_dec_ref(v_e_2109_);
v_a_2132_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2134_ = v___x_2123_;
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2123_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2137_; 
if (v_isShared_2135_ == 0)
{
v___x_2137_ = v___x_2134_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_a_2132_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go___boxed(lean_object* v_e_2140_, lean_object* v_p_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go(v_e_2140_, v_p_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_);
lean_dec(v_a_2151_);
lean_dec_ref(v_a_2150_);
lean_dec(v_a_2149_);
lean_dec_ref(v_a_2148_);
lean_dec(v_a_2147_);
lean_dec_ref(v_a_2146_);
lean_dec(v_a_2145_);
lean_dec_ref(v_a_2144_);
lean_dec(v_a_2143_);
lean_dec(v_a_2142_);
return v_res_2153_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0(void){
_start:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2154_ = lean_unsigned_to_nat(0u);
v___x_2155_ = lean_nat_to_int(v___x_2154_);
return v___x_2155_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1(void){
_start:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2156_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0);
v___x_2157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2156_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly(lean_object* v_e_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_){
_start:
{
uint8_t v___x_2170_; lean_object* v___x_2171_; 
v___x_2170_ = 1;
lean_inc_ref(v_e_2158_);
v___x_2171_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_2158_, v___x_2170_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v_a_2172_; 
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
lean_inc(v_a_2172_);
lean_dec_ref_known(v___x_2171_, 1);
if (lean_obj_tag(v_a_2172_) == 1)
{
lean_object* v_val_2173_; lean_object* v_fst_2174_; lean_object* v_snd_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
lean_dec_ref(v_e_2158_);
v_val_2173_ = lean_ctor_get(v_a_2172_, 0);
lean_inc(v_val_2173_);
lean_dec_ref_known(v_a_2172_, 1);
v_fst_2174_ = lean_ctor_get(v_val_2173_, 0);
lean_inc(v_fst_2174_);
v_snd_2175_ = lean_ctor_get(v_val_2173_, 1);
lean_inc(v_snd_2175_);
lean_dec(v_val_2173_);
v___x_2176_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1);
v___x_2177_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_snd_2175_, v___x_2176_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; lean_object* v___x_2179_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_a_2178_);
lean_dec_ref_known(v___x_2177_, 1);
v___x_2179_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go(v_fst_2174_, v_a_2178_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_);
return v___x_2179_;
}
else
{
lean_dec(v_fst_2174_);
return v___x_2177_;
}
}
else
{
lean_object* v___x_2180_; lean_object* v___x_2181_; 
lean_dec(v_a_2172_);
v___x_2180_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1);
v___x_2181_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_e_2158_, v___x_2180_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_);
return v___x_2181_;
}
}
else
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
lean_dec_ref(v_e_2158_);
v_a_2182_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2171_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2171_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2187_; 
if (v_isShared_2185_ == 0)
{
v___x_2187_ = v___x_2184_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_a_2182_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly___boxed(lean_object* v_e_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_e_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_);
lean_dec(v_a_2200_);
lean_dec_ref(v_a_2199_);
lean_dec(v_a_2198_);
lean_dec_ref(v_a_2197_);
lean_dec(v_a_2196_);
lean_dec_ref(v_a_2195_);
lean_dec(v_a_2194_);
lean_dec_ref(v_a_2193_);
lean_dec(v_a_2192_);
lean_dec(v_a_2191_);
return v_res_2202_;
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
