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
lean_inc(v_a_128_);
v___x_129_ = lean_unbox(v_a_128_);
if (v___x_129_ == 0)
{
lean_dec(v_a_128_);
lean_dec_ref(v_arg_65_);
lean_dec_ref(v_arg_62_);
return v___x_127_;
}
else
{
lean_object* v___x_130_; 
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
size_t v_x_8009__boxed_325_; size_t v_x_8010__boxed_326_; lean_object* v_res_327_; 
v_x_8009__boxed_325_ = lean_unbox_usize(v_x_321_);
lean_dec(v_x_321_);
v_x_8010__boxed_326_ = lean_unbox_usize(v_x_322_);
lean_dec(v_x_322_);
v_res_327_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_x_320_, v_x_8009__boxed_325_, v_x_8010__boxed_326_, v_x_323_, v_x_324_);
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
lean_object* v_vars_339_; lean_object* v_varMap_340_; lean_object* v_vars_x27_341_; lean_object* v_varMap_x27_342_; lean_object* v_natToIntMap_343_; lean_object* v_natDef_344_; lean_object* v_dvds_345_; lean_object* v_lowers_346_; lean_object* v_uppers_347_; lean_object* v_diseqs_348_; lean_object* v_elimEqs_349_; lean_object* v_elimStack_350_; lean_object* v_occurs_351_; lean_object* v_assignment_352_; lean_object* v_nextCnstrId_353_; uint8_t v_caseSplits_354_; lean_object* v_steps_355_; lean_object* v_conflict_x3f_356_; lean_object* v_diseqSplits_357_; lean_object* v_divMod_358_; uint8_t v_usedCommRing_359_; lean_object* v_nonlinearOccs_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_369_; 
v_vars_339_ = lean_ctor_get(v_s_338_, 0);
v_varMap_340_ = lean_ctor_get(v_s_338_, 1);
v_vars_x27_341_ = lean_ctor_get(v_s_338_, 2);
v_varMap_x27_342_ = lean_ctor_get(v_s_338_, 3);
v_natToIntMap_343_ = lean_ctor_get(v_s_338_, 4);
v_natDef_344_ = lean_ctor_get(v_s_338_, 5);
v_dvds_345_ = lean_ctor_get(v_s_338_, 6);
v_lowers_346_ = lean_ctor_get(v_s_338_, 7);
v_uppers_347_ = lean_ctor_get(v_s_338_, 8);
v_diseqs_348_ = lean_ctor_get(v_s_338_, 9);
v_elimEqs_349_ = lean_ctor_get(v_s_338_, 10);
v_elimStack_350_ = lean_ctor_get(v_s_338_, 11);
v_occurs_351_ = lean_ctor_get(v_s_338_, 12);
v_assignment_352_ = lean_ctor_get(v_s_338_, 13);
v_nextCnstrId_353_ = lean_ctor_get(v_s_338_, 14);
v_caseSplits_354_ = lean_ctor_get_uint8(v_s_338_, sizeof(void*)*20);
v_steps_355_ = lean_ctor_get(v_s_338_, 15);
v_conflict_x3f_356_ = lean_ctor_get(v_s_338_, 16);
v_diseqSplits_357_ = lean_ctor_get(v_s_338_, 17);
v_divMod_358_ = lean_ctor_get(v_s_338_, 18);
v_usedCommRing_359_ = lean_ctor_get_uint8(v_s_338_, sizeof(void*)*20 + 1);
v_nonlinearOccs_360_ = lean_ctor_get(v_s_338_, 19);
v_isSharedCheck_369_ = !lean_is_exclusive(v_s_338_);
if (v_isSharedCheck_369_ == 0)
{
v___x_362_ = v_s_338_;
v_isShared_363_ = v_isSharedCheck_369_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_nonlinearOccs_360_);
lean_inc(v_divMod_358_);
lean_inc(v_diseqSplits_357_);
lean_inc(v_conflict_x3f_356_);
lean_inc(v_steps_355_);
lean_inc(v_nextCnstrId_353_);
lean_inc(v_assignment_352_);
lean_inc(v_occurs_351_);
lean_inc(v_elimStack_350_);
lean_inc(v_elimEqs_349_);
lean_inc(v_diseqs_348_);
lean_inc(v_uppers_347_);
lean_inc(v_lowers_346_);
lean_inc(v_dvds_345_);
lean_inc(v_natDef_344_);
lean_inc(v_natToIntMap_343_);
lean_inc(v_varMap_x27_342_);
lean_inc(v_vars_x27_341_);
lean_inc(v_varMap_340_);
lean_inc(v_vars_339_);
lean_dec(v_s_338_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_369_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_367_; 
v___x_364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_364_, 0, v_x_335_);
lean_ctor_set(v___x_364_, 1, v___y_336_);
v___x_365_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0___redArg(v_nonlinearOccs_360_, v_a_337_, v___x_364_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 19, v___x_365_);
v___x_367_ = v___x_362_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 20, 2);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_vars_339_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v_varMap_340_);
lean_ctor_set(v_reuseFailAlloc_368_, 2, v_vars_x27_341_);
lean_ctor_set(v_reuseFailAlloc_368_, 3, v_varMap_x27_342_);
lean_ctor_set(v_reuseFailAlloc_368_, 4, v_natToIntMap_343_);
lean_ctor_set(v_reuseFailAlloc_368_, 5, v_natDef_344_);
lean_ctor_set(v_reuseFailAlloc_368_, 6, v_dvds_345_);
lean_ctor_set(v_reuseFailAlloc_368_, 7, v_lowers_346_);
lean_ctor_set(v_reuseFailAlloc_368_, 8, v_uppers_347_);
lean_ctor_set(v_reuseFailAlloc_368_, 9, v_diseqs_348_);
lean_ctor_set(v_reuseFailAlloc_368_, 10, v_elimEqs_349_);
lean_ctor_set(v_reuseFailAlloc_368_, 11, v_elimStack_350_);
lean_ctor_set(v_reuseFailAlloc_368_, 12, v_occurs_351_);
lean_ctor_set(v_reuseFailAlloc_368_, 13, v_assignment_352_);
lean_ctor_set(v_reuseFailAlloc_368_, 14, v_nextCnstrId_353_);
lean_ctor_set(v_reuseFailAlloc_368_, 15, v_steps_355_);
lean_ctor_set(v_reuseFailAlloc_368_, 16, v_conflict_x3f_356_);
lean_ctor_set(v_reuseFailAlloc_368_, 17, v_diseqSplits_357_);
lean_ctor_set(v_reuseFailAlloc_368_, 18, v_divMod_358_);
lean_ctor_set(v_reuseFailAlloc_368_, 19, v___x_365_);
lean_ctor_set_uint8(v_reuseFailAlloc_368_, sizeof(void*)*20, v_caseSplits_354_);
lean_ctor_set_uint8(v_reuseFailAlloc_368_, sizeof(void*)*20 + 1, v_usedCommRing_359_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1(lean_object* v_a_370_, lean_object* v_x_371_){
_start:
{
if (lean_obj_tag(v_x_371_) == 0)
{
uint8_t v___x_372_; 
v___x_372_ = 0;
return v___x_372_;
}
else
{
lean_object* v_head_373_; lean_object* v_tail_374_; uint8_t v___x_375_; 
v_head_373_ = lean_ctor_get(v_x_371_, 0);
v_tail_374_ = lean_ctor_get(v_x_371_, 1);
v___x_375_ = lean_nat_dec_eq(v_a_370_, v_head_373_);
if (v___x_375_ == 0)
{
v_x_371_ = v_tail_374_;
goto _start;
}
else
{
return v___x_375_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___boxed(lean_object* v_a_377_, lean_object* v_x_378_){
_start:
{
uint8_t v_res_379_; lean_object* v_r_380_; 
v_res_379_ = l_List_elem___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1(v_a_377_, v_x_378_);
lean_dec(v_x_378_);
lean_dec(v_a_377_);
v_r_380_ = lean_box(v_res_379_);
return v_r_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6___redArg(lean_object* v_keys_381_, lean_object* v_vals_382_, lean_object* v_i_383_, lean_object* v_k_384_){
_start:
{
lean_object* v___x_385_; uint8_t v___x_386_; 
v___x_385_ = lean_array_get_size(v_keys_381_);
v___x_386_ = lean_nat_dec_lt(v_i_383_, v___x_385_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; 
lean_dec(v_i_383_);
v___x_387_ = lean_box(0);
return v___x_387_;
}
else
{
lean_object* v_k_x27_388_; uint8_t v___x_389_; 
v_k_x27_388_ = lean_array_fget_borrowed(v_keys_381_, v_i_383_);
v___x_389_ = lean_nat_dec_eq(v_k_384_, v_k_x27_388_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = lean_unsigned_to_nat(1u);
v___x_391_ = lean_nat_add(v_i_383_, v___x_390_);
lean_dec(v_i_383_);
v_i_383_ = v___x_391_;
goto _start;
}
else
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = lean_array_fget_borrowed(v_vals_382_, v_i_383_);
lean_dec(v_i_383_);
lean_inc(v___x_393_);
v___x_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
return v___x_394_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_keys_395_, lean_object* v_vals_396_, lean_object* v_i_397_, lean_object* v_k_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6___redArg(v_keys_395_, v_vals_396_, v_i_397_, v_k_398_);
lean_dec(v_k_398_);
lean_dec_ref(v_vals_396_);
lean_dec_ref(v_keys_395_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___redArg(lean_object* v_x_400_, size_t v_x_401_, lean_object* v_x_402_){
_start:
{
if (lean_obj_tag(v_x_400_) == 0)
{
lean_object* v_es_403_; lean_object* v___x_404_; size_t v___x_405_; size_t v___x_406_; lean_object* v_j_407_; lean_object* v___x_408_; 
v_es_403_ = lean_ctor_get(v_x_400_, 0);
v___x_404_ = lean_box(2);
v___x_405_ = ((size_t)31ULL);
v___x_406_ = lean_usize_land(v_x_401_, v___x_405_);
v_j_407_ = lean_usize_to_nat(v___x_406_);
v___x_408_ = lean_array_get_borrowed(v___x_404_, v_es_403_, v_j_407_);
lean_dec(v_j_407_);
switch(lean_obj_tag(v___x_408_))
{
case 0:
{
lean_object* v_key_409_; lean_object* v_val_410_; uint8_t v___x_411_; 
v_key_409_ = lean_ctor_get(v___x_408_, 0);
v_val_410_ = lean_ctor_get(v___x_408_, 1);
v___x_411_ = lean_nat_dec_eq(v_x_402_, v_key_409_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; 
v___x_412_ = lean_box(0);
return v___x_412_;
}
else
{
lean_object* v___x_413_; 
lean_inc(v_val_410_);
v___x_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_413_, 0, v_val_410_);
return v___x_413_;
}
}
case 1:
{
lean_object* v_node_414_; size_t v___x_415_; size_t v___x_416_; 
v_node_414_ = lean_ctor_get(v___x_408_, 0);
v___x_415_ = ((size_t)5ULL);
v___x_416_ = lean_usize_shift_right(v_x_401_, v___x_415_);
v_x_400_ = v_node_414_;
v_x_401_ = v___x_416_;
goto _start;
}
default: 
{
lean_object* v___x_418_; 
v___x_418_ = lean_box(0);
return v___x_418_;
}
}
}
else
{
lean_object* v_ks_419_; lean_object* v_vs_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v_ks_419_ = lean_ctor_get(v_x_400_, 0);
v_vs_420_ = lean_ctor_get(v_x_400_, 1);
v___x_421_ = lean_unsigned_to_nat(0u);
v___x_422_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6___redArg(v_ks_419_, v_vs_420_, v___x_421_, v_x_402_);
return v___x_422_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___redArg___boxed(lean_object* v_x_423_, lean_object* v_x_424_, lean_object* v_x_425_){
_start:
{
size_t v_x_8228__boxed_426_; lean_object* v_res_427_; 
v_x_8228__boxed_426_ = lean_unbox_usize(v_x_424_);
lean_dec(v_x_424_);
v_res_427_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___redArg(v_x_423_, v_x_8228__boxed_426_, v_x_425_);
lean_dec(v_x_425_);
lean_dec_ref(v_x_423_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2___redArg(lean_object* v_x_428_, lean_object* v_x_429_){
_start:
{
uint64_t v___x_430_; size_t v___x_431_; lean_object* v___x_432_; 
v___x_430_ = lean_uint64_of_nat(v_x_429_);
v___x_431_ = lean_uint64_to_usize(v___x_430_);
v___x_432_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___redArg(v_x_428_, v___x_431_, v_x_429_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2___redArg___boxed(lean_object* v_x_433_, lean_object* v_x_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2___redArg(v_x_433_, v_x_434_);
lean_dec(v_x_434_);
lean_dec_ref(v_x_433_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(lean_object* v_arg_436_, lean_object* v_x_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = lean_box(0);
lean_inc(v_a_447_);
lean_inc_ref(v_a_446_);
lean_inc(v_a_445_);
lean_inc_ref(v_a_444_);
lean_inc(v_a_443_);
lean_inc_ref(v_a_442_);
lean_inc(v_a_441_);
lean_inc_ref(v_a_440_);
lean_inc(v_a_439_);
lean_inc(v_a_438_);
v___x_450_ = lean_grind_cutsat_mk_var(v_arg_436_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_519_; 
v_a_451_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_519_ == 0)
{
v___x_453_ = v___x_450_;
v_isShared_454_ = v_isSharedCheck_519_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_450_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_519_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___y_456_; lean_object* v___y_457_; lean_object* v___y_467_; lean_object* v___y_468_; lean_object* v___x_483_; 
v___x_483_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_438_, v_a_446_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v_a_484_; lean_object* v___y_486_; lean_object* v_elimEqs_506_; lean_object* v_size_507_; uint8_t v___x_508_; 
v_a_484_ = lean_ctor_get(v___x_483_, 0);
lean_inc(v_a_484_);
lean_dec_ref_known(v___x_483_, 1);
v_elimEqs_506_ = lean_ctor_get(v_a_484_, 10);
lean_inc_ref(v_elimEqs_506_);
lean_dec(v_a_484_);
v_size_507_ = lean_ctor_get(v_elimEqs_506_, 2);
v___x_508_ = lean_nat_dec_lt(v_a_451_, v_size_507_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; 
lean_dec_ref(v_elimEqs_506_);
v___x_509_ = l_outOfBounds___redArg(v___x_449_);
v___y_486_ = v___x_509_;
goto v___jp_485_;
}
else
{
lean_object* v___x_510_; 
v___x_510_ = l_Lean_PersistentArray_get_x21___redArg(v___x_449_, v_elimEqs_506_, v_a_451_);
lean_dec_ref(v_elimEqs_506_);
v___y_486_ = v___x_510_;
goto v___jp_485_;
}
v___jp_485_:
{
if (lean_obj_tag(v___y_486_) == 0)
{
v___y_467_ = v_a_438_;
v___y_468_ = v_a_446_;
goto v___jp_466_;
}
else
{
lean_object* v___x_487_; 
lean_dec_ref_known(v___y_486_, 1);
lean_inc(v_a_447_);
lean_inc_ref(v_a_446_);
lean_inc(v_a_445_);
lean_inc_ref(v_a_444_);
lean_inc(v_a_443_);
lean_inc_ref(v_a_442_);
lean_inc(v_a_441_);
lean_inc_ref(v_a_440_);
lean_inc(v_a_439_);
lean_inc(v_a_438_);
lean_inc(v_x_437_);
lean_inc(v_a_451_);
v___x_487_ = lean_cutsat_propagate_nonlinear(v_a_451_, v_x_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_497_; 
v_a_488_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_497_ == 0)
{
v___x_490_ = v___x_487_;
v_isShared_491_ = v_isSharedCheck_497_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_487_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_497_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
uint8_t v___x_492_; 
v___x_492_ = lean_unbox(v_a_488_);
lean_dec(v_a_488_);
if (v___x_492_ == 0)
{
lean_del_object(v___x_490_);
v___y_467_ = v_a_438_;
v___y_468_ = v_a_446_;
goto v___jp_466_;
}
else
{
lean_object* v___x_493_; lean_object* v___x_495_; 
lean_del_object(v___x_453_);
lean_dec(v_a_451_);
lean_dec(v_x_437_);
v___x_493_ = lean_box(0);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 0, v___x_493_);
v___x_495_ = v___x_490_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_493_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
else
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
lean_del_object(v___x_453_);
lean_dec(v_a_451_);
lean_dec(v_x_437_);
v_a_498_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___x_487_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_487_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
}
}
else
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
lean_del_object(v___x_453_);
lean_dec(v_a_451_);
lean_dec(v_x_437_);
v_a_511_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_518_ == 0)
{
v___x_513_ = v___x_483_;
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_483_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_a_511_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
v___jp_455_:
{
uint8_t v___x_458_; 
v___x_458_ = l_List_elem___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1(v_x_437_, v___y_457_);
if (v___x_458_ == 0)
{
lean_object* v___f_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
lean_del_object(v___x_453_);
v___f_459_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___lam__0), 4, 3);
lean_closure_set(v___f_459_, 0, v_x_437_);
lean_closure_set(v___f_459_, 1, v___y_457_);
lean_closure_set(v___f_459_, 2, v_a_451_);
v___x_460_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_461_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_460_, v___f_459_, v___y_456_);
return v___x_461_;
}
else
{
lean_object* v___x_462_; lean_object* v___x_464_; 
lean_dec(v___y_457_);
lean_dec(v_a_451_);
lean_dec(v_x_437_);
v___x_462_ = lean_box(0);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 0, v___x_462_);
v___x_464_ = v___x_453_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_462_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
v___jp_466_:
{
lean_object* v___x_469_; 
v___x_469_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v___y_467_, v___y_468_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; lean_object* v_nonlinearOccs_471_; lean_object* v___x_472_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_a_470_);
lean_dec_ref_known(v___x_469_, 1);
v_nonlinearOccs_471_ = lean_ctor_get(v_a_470_, 19);
lean_inc_ref(v_nonlinearOccs_471_);
lean_dec(v_a_470_);
v___x_472_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2___redArg(v_nonlinearOccs_471_, v_a_451_);
lean_dec_ref(v_nonlinearOccs_471_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v___x_473_; 
v___x_473_ = lean_box(0);
v___y_456_ = v___y_467_;
v___y_457_ = v___x_473_;
goto v___jp_455_;
}
else
{
lean_object* v_val_474_; 
v_val_474_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_val_474_);
lean_dec_ref_known(v___x_472_, 1);
v___y_456_ = v___y_467_;
v___y_457_ = v_val_474_;
goto v___jp_455_;
}
}
else
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
lean_del_object(v___x_453_);
lean_dec(v_a_451_);
lean_dec(v_x_437_);
v_a_475_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_482_ == 0)
{
v___x_477_ = v___x_469_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_469_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_475_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
}
}
else
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_527_; 
lean_dec(v_x_437_);
v_a_520_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_527_ == 0)
{
v___x_522_ = v___x_450_;
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_450_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_525_; 
if (v_isShared_523_ == 0)
{
v___x_525_ = v___x_522_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_a_520_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___boxed(lean_object* v_arg_528_, lean_object* v_x_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_arg_528_, v_x_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_);
lean_dec(v_a_539_);
lean_dec_ref(v_a_538_);
lean_dec(v_a_537_);
lean_dec_ref(v_a_536_);
lean_dec(v_a_535_);
lean_dec_ref(v_a_534_);
lean_dec(v_a_533_);
lean_dec_ref(v_a_532_);
lean_dec(v_a_531_);
lean_dec(v_a_530_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0(lean_object* v_00_u03b2_542_, lean_object* v_x_543_, lean_object* v_x_544_, lean_object* v_x_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0___redArg(v_x_543_, v_x_544_, v_x_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2(lean_object* v_00_u03b2_547_, lean_object* v_x_548_, lean_object* v_x_549_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2___redArg(v_x_548_, v_x_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2___boxed(lean_object* v_00_u03b2_551_, lean_object* v_x_552_, lean_object* v_x_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2(v_00_u03b2_551_, v_x_552_, v_x_553_);
lean_dec(v_x_553_);
lean_dec_ref(v_x_552_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0(lean_object* v_00_u03b2_555_, lean_object* v_x_556_, size_t v_x_557_, size_t v_x_558_, lean_object* v_x_559_, lean_object* v_x_560_){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_x_556_, v_x_557_, v_x_558_, v_x_559_, v_x_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___boxed(lean_object* v_00_u03b2_562_, lean_object* v_x_563_, lean_object* v_x_564_, lean_object* v_x_565_, lean_object* v_x_566_, lean_object* v_x_567_){
_start:
{
size_t v_x_8459__boxed_568_; size_t v_x_8460__boxed_569_; lean_object* v_res_570_; 
v_x_8459__boxed_568_ = lean_unbox_usize(v_x_564_);
lean_dec(v_x_564_);
v_x_8460__boxed_569_ = lean_unbox_usize(v_x_565_);
lean_dec(v_x_565_);
v_res_570_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0(v_00_u03b2_562_, v_x_563_, v_x_8459__boxed_568_, v_x_8460__boxed_569_, v_x_566_, v_x_567_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3(lean_object* v_00_u03b2_571_, lean_object* v_x_572_, size_t v_x_573_, lean_object* v_x_574_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___redArg(v_x_572_, v_x_573_, v_x_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___boxed(lean_object* v_00_u03b2_576_, lean_object* v_x_577_, lean_object* v_x_578_, lean_object* v_x_579_){
_start:
{
size_t v_x_8476__boxed_580_; lean_object* v_res_581_; 
v_x_8476__boxed_580_ = lean_unbox_usize(v_x_578_);
lean_dec(v_x_578_);
v_res_581_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3(v_00_u03b2_576_, v_x_577_, v_x_8476__boxed_580_, v_x_579_);
lean_dec(v_x_579_);
lean_dec_ref(v_x_577_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_582_, lean_object* v_n_583_, lean_object* v_k_584_, lean_object* v_v_585_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1___redArg(v_n_583_, v_k_584_, v_v_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_587_, size_t v_depth_588_, lean_object* v_keys_589_, lean_object* v_vals_590_, lean_object* v_heq_591_, lean_object* v_i_592_, lean_object* v_entries_593_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg(v_depth_588_, v_keys_589_, v_vals_590_, v_i_592_, v_entries_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_595_, lean_object* v_depth_596_, lean_object* v_keys_597_, lean_object* v_vals_598_, lean_object* v_heq_599_, lean_object* v_i_600_, lean_object* v_entries_601_){
_start:
{
size_t v_depth_boxed_602_; lean_object* v_res_603_; 
v_depth_boxed_602_ = lean_unbox_usize(v_depth_596_);
lean_dec(v_depth_596_);
v_res_603_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2(v_00_u03b2_595_, v_depth_boxed_602_, v_keys_597_, v_vals_598_, v_heq_599_, v_i_600_, v_entries_601_);
lean_dec_ref(v_vals_598_);
lean_dec_ref(v_keys_597_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_604_, lean_object* v_keys_605_, lean_object* v_vals_606_, lean_object* v_heq_607_, lean_object* v_i_608_, lean_object* v_k_609_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6___redArg(v_keys_605_, v_vals_606_, v_i_608_, v_k_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_611_, lean_object* v_keys_612_, lean_object* v_vals_613_, lean_object* v_heq_614_, lean_object* v_i_615_, lean_object* v_k_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6(v_00_u03b2_611_, v_keys_612_, v_vals_613_, v_heq_614_, v_i_615_, v_k_616_);
lean_dec(v_k_616_);
lean_dec_ref(v_vals_613_);
lean_dec_ref(v_keys_612_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_618_, lean_object* v_x_619_, lean_object* v_x_620_, lean_object* v_x_621_, lean_object* v_x_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__4___redArg(v_x_619_, v_x_620_, v_x_621_, v_x_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(lean_object* v_x_624_, lean_object* v_e_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_){
_start:
{
lean_object* v___x_637_; 
lean_inc_ref(v_e_625_);
v___x_637_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_625_, v_a_633_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_a_638_);
lean_dec_ref_known(v___x_637_, 1);
v___x_639_ = l_Lean_Expr_cleanupAnnotations(v_a_638_);
v___x_640_ = l_Lean_Expr_isApp(v___x_639_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; 
lean_dec_ref(v___x_639_);
v___x_641_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_625_, v_x_624_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_);
return v___x_641_;
}
else
{
lean_object* v_arg_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
v_arg_642_ = lean_ctor_get(v___x_639_, 1);
lean_inc_ref(v_arg_642_);
v___x_643_ = l_Lean_Expr_appFnCleanup___redArg(v___x_639_);
v___x_644_ = l_Lean_Expr_isApp(v___x_643_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; 
lean_dec_ref(v___x_643_);
lean_dec_ref(v_arg_642_);
v___x_645_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_625_, v_x_624_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_);
return v___x_645_;
}
else
{
lean_object* v_arg_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
v_arg_646_ = lean_ctor_get(v___x_643_, 1);
lean_inc_ref(v_arg_646_);
v___x_647_ = l_Lean_Expr_appFnCleanup___redArg(v___x_643_);
v___x_648_ = l_Lean_Expr_isApp(v___x_647_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; 
lean_dec_ref(v___x_647_);
lean_dec_ref(v_arg_646_);
lean_dec_ref(v_arg_642_);
v___x_649_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_625_, v_x_624_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_);
return v___x_649_;
}
else
{
lean_object* v_arg_650_; lean_object* v___x_651_; uint8_t v___x_652_; 
v_arg_650_ = lean_ctor_get(v___x_647_, 1);
lean_inc_ref(v_arg_650_);
v___x_651_ = l_Lean_Expr_appFnCleanup___redArg(v___x_647_);
v___x_652_ = l_Lean_Expr_isApp(v___x_651_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; 
lean_dec_ref(v___x_651_);
lean_dec_ref(v_arg_650_);
lean_dec_ref(v_arg_646_);
lean_dec_ref(v_arg_642_);
v___x_653_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_625_, v_x_624_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_);
return v___x_653_;
}
else
{
lean_object* v___x_654_; uint8_t v___x_655_; 
v___x_654_ = l_Lean_Expr_appFnCleanup___redArg(v___x_651_);
v___x_655_ = l_Lean_Expr_isApp(v___x_654_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; 
lean_dec_ref(v___x_654_);
lean_dec_ref(v_arg_650_);
lean_dec_ref(v_arg_646_);
lean_dec_ref(v_arg_642_);
v___x_656_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_625_, v_x_624_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_);
return v___x_656_;
}
else
{
lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_657_ = l_Lean_Expr_appFnCleanup___redArg(v___x_654_);
v___x_658_ = l_Lean_Expr_isApp(v___x_657_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; 
lean_dec_ref(v___x_657_);
lean_dec_ref(v_arg_650_);
lean_dec_ref(v_arg_646_);
lean_dec_ref(v_arg_642_);
v___x_659_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_625_, v_x_624_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_);
return v___x_659_;
}
else
{
lean_object* v___x_660_; lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_660_ = l_Lean_Expr_appFnCleanup___redArg(v___x_657_);
v___x_661_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11));
v___x_662_ = l_Lean_Expr_isConstOf(v___x_660_, v___x_661_);
lean_dec_ref(v___x_660_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; 
lean_dec_ref(v_arg_650_);
lean_dec_ref(v_arg_646_);
lean_dec_ref(v_arg_642_);
v___x_663_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_625_, v_x_624_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_);
return v___x_663_;
}
else
{
lean_object* v___x_664_; 
v___x_664_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_650_, v_a_633_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v_a_665_; uint8_t v___x_666_; 
v_a_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_a_665_);
lean_dec_ref_known(v___x_664_, 1);
v___x_666_ = lean_unbox(v_a_665_);
lean_dec(v_a_665_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; 
lean_dec_ref(v_arg_646_);
lean_dec_ref(v_arg_642_);
v___x_667_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_625_, v_x_624_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_);
return v___x_667_;
}
else
{
lean_object* v___x_668_; 
lean_dec_ref(v_e_625_);
lean_inc(v_x_624_);
v___x_668_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(v_x_624_, v_arg_646_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_dec_ref_known(v___x_668_, 1);
v_e_625_ = v_arg_642_;
goto _start;
}
else
{
lean_dec_ref(v_arg_642_);
lean_dec(v_x_624_);
return v___x_668_;
}
}
}
else
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
lean_dec_ref(v_arg_646_);
lean_dec_ref(v_arg_642_);
lean_dec_ref(v_e_625_);
lean_dec(v_x_624_);
v_a_670_ = lean_ctor_get(v___x_664_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_664_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_664_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_670_);
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
}
}
}
}
}
}
}
else
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_685_; 
lean_dec_ref(v_e_625_);
lean_dec(v_x_624_);
v_a_678_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_685_ == 0)
{
v___x_680_ = v___x_637_;
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_637_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_683_; 
if (v_isShared_681_ == 0)
{
v___x_683_ = v___x_680_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_a_678_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go___boxed(lean_object* v_x_686_, lean_object* v_e_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(v_x_686_, v_e_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_);
lean_dec(v_a_697_);
lean_dec_ref(v_a_696_);
lean_dec(v_a_695_);
lean_dec_ref(v_a_694_);
lean_dec(v_a_693_);
lean_dec_ref(v_a_692_);
lean_dec(v_a_691_);
lean_dec_ref(v_a_690_);
lean_dec(v_a_689_);
lean_dec(v_a_688_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt(lean_object* v_e_700_, lean_object* v_x_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_700_, v_a_709_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; lean_object* v___x_721_; uint8_t v___x_722_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_a_720_);
lean_dec_ref_known(v___x_719_, 1);
v___x_721_ = l_Lean_Expr_cleanupAnnotations(v_a_720_);
v___x_722_ = l_Lean_Expr_isApp(v___x_721_);
if (v___x_722_ == 0)
{
lean_dec_ref(v___x_721_);
lean_dec(v_x_701_);
goto v___jp_713_;
}
else
{
lean_object* v_arg_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
v_arg_723_ = lean_ctor_get(v___x_721_, 1);
lean_inc_ref(v_arg_723_);
v___x_724_ = l_Lean_Expr_appFnCleanup___redArg(v___x_721_);
v___x_725_ = l_Lean_Expr_isApp(v___x_724_);
if (v___x_725_ == 0)
{
lean_dec_ref(v___x_724_);
lean_dec_ref(v_arg_723_);
lean_dec(v_x_701_);
goto v___jp_713_;
}
else
{
lean_object* v_arg_726_; lean_object* v___x_727_; uint8_t v___x_728_; 
v_arg_726_ = lean_ctor_get(v___x_724_, 1);
lean_inc_ref(v_arg_726_);
v___x_727_ = l_Lean_Expr_appFnCleanup___redArg(v___x_724_);
v___x_728_ = l_Lean_Expr_isApp(v___x_727_);
if (v___x_728_ == 0)
{
lean_dec_ref(v___x_727_);
lean_dec_ref(v_arg_726_);
lean_dec_ref(v_arg_723_);
lean_dec(v_x_701_);
goto v___jp_713_;
}
else
{
lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_729_ = l_Lean_Expr_appFnCleanup___redArg(v___x_727_);
v___x_730_ = l_Lean_Expr_isApp(v___x_729_);
if (v___x_730_ == 0)
{
lean_dec_ref(v___x_729_);
lean_dec_ref(v_arg_726_);
lean_dec_ref(v_arg_723_);
lean_dec(v_x_701_);
goto v___jp_713_;
}
else
{
lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_731_ = l_Lean_Expr_appFnCleanup___redArg(v___x_729_);
v___x_732_ = l_Lean_Expr_isApp(v___x_731_);
if (v___x_732_ == 0)
{
lean_dec_ref(v___x_731_);
lean_dec_ref(v_arg_726_);
lean_dec_ref(v_arg_723_);
lean_dec(v_x_701_);
goto v___jp_713_;
}
else
{
lean_object* v___x_733_; uint8_t v___x_734_; 
v___x_733_ = l_Lean_Expr_appFnCleanup___redArg(v___x_731_);
v___x_734_ = l_Lean_Expr_isApp(v___x_733_);
if (v___x_734_ == 0)
{
lean_dec_ref(v___x_733_);
lean_dec_ref(v_arg_726_);
lean_dec_ref(v_arg_723_);
lean_dec(v_x_701_);
goto v___jp_713_;
}
else
{
lean_object* v___x_735_; lean_object* v___x_736_; uint8_t v___x_737_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v___y_748_; 
v___x_735_ = l_Lean_Expr_appFnCleanup___redArg(v___x_733_);
v___x_736_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__2));
v___x_737_ = l_Lean_Expr_isConstOf(v___x_735_, v___x_736_);
if (v___x_737_ == 0)
{
lean_object* v___x_793_; uint8_t v___x_794_; 
v___x_793_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__5));
v___x_794_ = l_Lean_Expr_isConstOf(v___x_735_, v___x_793_);
if (v___x_794_ == 0)
{
lean_object* v___x_795_; uint8_t v___x_796_; 
v___x_795_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__8));
v___x_796_ = l_Lean_Expr_isConstOf(v___x_735_, v___x_795_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; uint8_t v___x_798_; 
v___x_797_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11));
v___x_798_ = l_Lean_Expr_isConstOf(v___x_735_, v___x_797_);
lean_dec_ref(v___x_735_);
if (v___x_798_ == 0)
{
lean_dec_ref(v_arg_726_);
lean_dec_ref(v_arg_723_);
lean_dec(v_x_701_);
goto v___jp_713_;
}
else
{
lean_object* v___x_799_; 
lean_inc(v_x_701_);
v___x_799_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(v_x_701_, v_arg_726_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v___x_800_; 
lean_dec_ref_known(v___x_799_, 1);
v___x_800_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(v_x_701_, v_arg_723_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
return v___x_800_;
}
else
{
lean_dec_ref(v_arg_723_);
lean_dec(v_x_701_);
return v___x_799_;
}
}
}
else
{
lean_object* v___x_801_; 
lean_dec_ref(v___x_735_);
lean_dec_ref(v_arg_726_);
v___x_801_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_arg_723_, v_x_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
return v___x_801_;
}
}
else
{
lean_object* v___x_802_; 
lean_dec_ref(v___x_735_);
lean_dec_ref(v_arg_726_);
v___x_802_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_arg_723_, v_x_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
return v___x_802_;
}
}
else
{
lean_object* v___x_803_; 
lean_dec_ref(v___x_735_);
lean_inc_ref(v_arg_726_);
v___x_803_ = l_Lean_Meta_getIntValue_x3f(v_arg_726_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_a_804_);
lean_dec_ref_known(v___x_803_, 1);
if (lean_obj_tag(v_a_804_) == 0)
{
if (v___x_737_ == 0)
{
lean_dec_ref(v_arg_726_);
v___y_739_ = v_a_702_;
v___y_740_ = v_a_703_;
v___y_741_ = v_a_704_;
v___y_742_ = v_a_705_;
v___y_743_ = v_a_706_;
v___y_744_ = v_a_707_;
v___y_745_ = v_a_708_;
v___y_746_ = v_a_709_;
v___y_747_ = v_a_710_;
v___y_748_ = v_a_711_;
goto v___jp_738_;
}
else
{
lean_object* v___x_805_; 
lean_inc(v_x_701_);
v___x_805_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_arg_726_, v_x_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_dec_ref_known(v___x_805_, 1);
v___y_739_ = v_a_702_;
v___y_740_ = v_a_703_;
v___y_741_ = v_a_704_;
v___y_742_ = v_a_705_;
v___y_743_ = v_a_706_;
v___y_744_ = v_a_707_;
v___y_745_ = v_a_708_;
v___y_746_ = v_a_709_;
v___y_747_ = v_a_710_;
v___y_748_ = v_a_711_;
goto v___jp_738_;
}
else
{
lean_dec_ref(v_arg_723_);
lean_dec(v_x_701_);
return v___x_805_;
}
}
}
else
{
lean_dec_ref_known(v_a_804_, 1);
lean_dec_ref(v_arg_726_);
v___y_739_ = v_a_702_;
v___y_740_ = v_a_703_;
v___y_741_ = v_a_704_;
v___y_742_ = v_a_705_;
v___y_743_ = v_a_706_;
v___y_744_ = v_a_707_;
v___y_745_ = v_a_708_;
v___y_746_ = v_a_709_;
v___y_747_ = v_a_710_;
v___y_748_ = v_a_711_;
goto v___jp_738_;
}
}
else
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
lean_dec_ref(v_arg_726_);
lean_dec_ref(v_arg_723_);
lean_dec(v_x_701_);
v_a_806_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___x_803_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_803_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
v___jp_738_:
{
lean_object* v___x_749_; 
lean_inc_ref(v_arg_723_);
v___x_749_ = l_Lean_Meta_getIntValue_x3f(v_arg_723_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v_a_750_; lean_object* v___x_751_; 
v_a_750_ = lean_ctor_get(v___x_749_, 0);
lean_inc(v_a_750_);
lean_dec_ref_known(v___x_749_, 1);
v___x_751_ = l_Lean_Meta_getNatValue_x3f(v_arg_723_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
if (lean_obj_tag(v___x_751_) == 0)
{
if (lean_obj_tag(v_a_750_) == 0)
{
if (v___x_737_ == 0)
{
lean_dec_ref_known(v___x_751_, 1);
lean_dec_ref(v_arg_723_);
lean_dec(v_x_701_);
goto v___jp_716_;
}
else
{
lean_object* v_a_752_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_a_752_);
lean_dec_ref_known(v___x_751_, 1);
if (lean_obj_tag(v_a_752_) == 0)
{
lean_object* v___x_753_; 
lean_inc_ref(v_arg_723_);
v___x_753_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_arg_723_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v_a_754_; lean_object* v_fst_755_; lean_object* v___x_756_; 
v_a_754_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_a_754_);
lean_dec_ref_known(v___x_753_, 1);
v_fst_755_ = lean_ctor_get(v_a_754_, 0);
lean_inc(v_fst_755_);
lean_dec(v_a_754_);
v___x_756_ = l_Lean_Meta_Grind_getGeneration___redArg(v_arg_723_, v___y_739_);
lean_dec_ref(v_arg_723_);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_object* v_a_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v_a_757_ = lean_ctor_get(v___x_756_, 0);
lean_inc(v_a_757_);
lean_dec_ref_known(v___x_756_, 1);
v___x_758_ = lean_box(0);
lean_inc(v___y_748_);
lean_inc_ref(v___y_747_);
lean_inc(v___y_746_);
lean_inc_ref(v___y_745_);
lean_inc(v___y_744_);
lean_inc_ref(v___y_743_);
lean_inc(v___y_742_);
lean_inc_ref(v___y_741_);
lean_inc(v___y_740_);
lean_inc(v___y_739_);
lean_inc(v_fst_755_);
v___x_759_ = lean_grind_internalize(v_fst_755_, v_a_757_, v___x_758_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v___x_760_; 
lean_dec_ref_known(v___x_759_, 1);
v___x_760_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_fst_755_, v_x_701_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
return v___x_760_;
}
else
{
lean_dec(v_fst_755_);
lean_dec(v_x_701_);
return v___x_759_;
}
}
else
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
lean_dec(v_fst_755_);
lean_dec(v_x_701_);
v_a_761_ = lean_ctor_get(v___x_756_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_768_ == 0)
{
v___x_763_ = v___x_756_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_756_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_761_);
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
else
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_776_; 
lean_dec_ref(v_arg_723_);
lean_dec(v_x_701_);
v_a_769_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_776_ == 0)
{
v___x_771_ = v___x_753_;
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_753_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_774_; 
if (v_isShared_772_ == 0)
{
v___x_774_ = v___x_771_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_a_769_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_752_, 1);
lean_dec_ref(v_arg_723_);
lean_dec(v_x_701_);
goto v___jp_716_;
}
}
}
else
{
lean_dec_ref_known(v_a_750_, 1);
lean_dec_ref_known(v___x_751_, 1);
lean_dec_ref(v_arg_723_);
lean_dec(v_x_701_);
goto v___jp_716_;
}
}
else
{
lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_784_; 
lean_dec(v_a_750_);
lean_dec_ref(v_arg_723_);
lean_dec(v_x_701_);
v_a_777_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_784_ == 0)
{
v___x_779_ = v___x_751_;
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v___x_751_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_782_; 
if (v_isShared_780_ == 0)
{
v___x_782_ = v___x_779_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_a_777_);
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
else
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
lean_dec_ref(v_arg_723_);
lean_dec(v_x_701_);
v_a_785_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_792_ == 0)
{
v___x_787_ = v___x_749_;
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_749_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_a_785_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
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
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
lean_dec(v_x_701_);
v_a_814_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___x_719_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_719_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_a_814_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
v___jp_713_:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = lean_box(0);
v___x_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
return v___x_715_;
}
v___jp_716_:
{
lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_717_ = lean_box(0);
v___x_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
return v___x_718_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt___boxed(lean_object* v_e_822_, lean_object* v_x_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt(v_e_822_, v_x_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_);
lean_dec(v_a_833_);
lean_dec_ref(v_a_832_);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
lean_dec(v_a_827_);
lean_dec_ref(v_a_826_);
lean_dec(v_a_825_);
lean_dec(v_a_824_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_x_836_, lean_object* v_x_837_, lean_object* v_x_838_, lean_object* v_x_839_){
_start:
{
lean_object* v_ks_840_; lean_object* v_vs_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_867_; 
v_ks_840_ = lean_ctor_get(v_x_836_, 0);
v_vs_841_ = lean_ctor_get(v_x_836_, 1);
v_isSharedCheck_867_ = !lean_is_exclusive(v_x_836_);
if (v_isSharedCheck_867_ == 0)
{
v___x_843_ = v_x_836_;
v_isShared_844_ = v_isSharedCheck_867_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_vs_841_);
lean_inc(v_ks_840_);
lean_dec(v_x_836_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_867_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_845_; uint8_t v___x_846_; 
v___x_845_ = lean_array_get_size(v_ks_840_);
v___x_846_ = lean_nat_dec_lt(v_x_837_, v___x_845_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_850_; 
lean_dec(v_x_837_);
v___x_847_ = lean_array_push(v_ks_840_, v_x_838_);
v___x_848_ = lean_array_push(v_vs_841_, v_x_839_);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 1, v___x_848_);
lean_ctor_set(v___x_843_, 0, v___x_847_);
v___x_850_ = v___x_843_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_847_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v___x_848_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
else
{
lean_object* v_k_x27_852_; size_t v___x_853_; size_t v___x_854_; uint8_t v___x_855_; 
v_k_x27_852_ = lean_array_fget_borrowed(v_ks_840_, v_x_837_);
v___x_853_ = lean_ptr_addr(v_x_838_);
v___x_854_ = lean_ptr_addr(v_k_x27_852_);
v___x_855_ = lean_usize_dec_eq(v___x_853_, v___x_854_);
if (v___x_855_ == 0)
{
lean_object* v___x_857_; 
if (v_isShared_844_ == 0)
{
v___x_857_ = v___x_843_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_ks_840_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v_vs_841_);
v___x_857_ = v_reuseFailAlloc_861_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = lean_unsigned_to_nat(1u);
v___x_859_ = lean_nat_add(v_x_837_, v___x_858_);
lean_dec(v_x_837_);
v_x_836_ = v___x_857_;
v_x_837_ = v___x_859_;
goto _start;
}
}
else
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_865_; 
v___x_862_ = lean_array_fset(v_ks_840_, v_x_837_, v_x_838_);
v___x_863_ = lean_array_fset(v_vs_841_, v_x_837_, v_x_839_);
lean_dec(v_x_837_);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 1, v___x_863_);
lean_ctor_set(v___x_843_, 0, v___x_862_);
v___x_865_ = v___x_843_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_862_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v___x_863_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4___redArg(lean_object* v_n_868_, lean_object* v_k_869_, lean_object* v_v_870_){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = lean_unsigned_to_nat(0u);
v___x_872_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7___redArg(v_n_868_, v___x_871_, v_k_869_, v_v_870_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(lean_object* v_x_873_, size_t v_x_874_, size_t v_x_875_, lean_object* v_x_876_, lean_object* v_x_877_){
_start:
{
if (lean_obj_tag(v_x_873_) == 0)
{
lean_object* v_es_878_; size_t v___x_879_; size_t v___x_880_; lean_object* v_j_881_; lean_object* v___x_882_; uint8_t v___x_883_; 
v_es_878_ = lean_ctor_get(v_x_873_, 0);
v___x_879_ = ((size_t)31ULL);
v___x_880_ = lean_usize_land(v_x_874_, v___x_879_);
v_j_881_ = lean_usize_to_nat(v___x_880_);
v___x_882_ = lean_array_get_size(v_es_878_);
v___x_883_ = lean_nat_dec_lt(v_j_881_, v___x_882_);
if (v___x_883_ == 0)
{
lean_dec(v_j_881_);
lean_dec(v_x_877_);
lean_dec_ref(v_x_876_);
return v_x_873_;
}
else
{
lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_924_; 
lean_inc_ref(v_es_878_);
v_isSharedCheck_924_ = !lean_is_exclusive(v_x_873_);
if (v_isSharedCheck_924_ == 0)
{
lean_object* v_unused_925_; 
v_unused_925_ = lean_ctor_get(v_x_873_, 0);
lean_dec(v_unused_925_);
v___x_885_ = v_x_873_;
v_isShared_886_ = v_isSharedCheck_924_;
goto v_resetjp_884_;
}
else
{
lean_dec(v_x_873_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_924_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v_v_887_; lean_object* v___x_888_; lean_object* v_xs_x27_889_; lean_object* v___y_891_; 
v_v_887_ = lean_array_fget(v_es_878_, v_j_881_);
v___x_888_ = lean_box(0);
v_xs_x27_889_ = lean_array_fset(v_es_878_, v_j_881_, v___x_888_);
switch(lean_obj_tag(v_v_887_))
{
case 0:
{
lean_object* v_key_896_; lean_object* v_val_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_909_; 
v_key_896_ = lean_ctor_get(v_v_887_, 0);
v_val_897_ = lean_ctor_get(v_v_887_, 1);
v_isSharedCheck_909_ = !lean_is_exclusive(v_v_887_);
if (v_isSharedCheck_909_ == 0)
{
v___x_899_ = v_v_887_;
v_isShared_900_ = v_isSharedCheck_909_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_val_897_);
lean_inc(v_key_896_);
lean_dec(v_v_887_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_909_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
size_t v___x_901_; size_t v___x_902_; uint8_t v___x_903_; 
v___x_901_ = lean_ptr_addr(v_x_876_);
v___x_902_ = lean_ptr_addr(v_key_896_);
v___x_903_ = lean_usize_dec_eq(v___x_901_, v___x_902_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; lean_object* v___x_905_; 
lean_del_object(v___x_899_);
v___x_904_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_896_, v_val_897_, v_x_876_, v_x_877_);
v___x_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
v___y_891_ = v___x_905_;
goto v___jp_890_;
}
else
{
lean_object* v___x_907_; 
lean_dec(v_val_897_);
lean_dec(v_key_896_);
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 1, v_x_877_);
lean_ctor_set(v___x_899_, 0, v_x_876_);
v___x_907_ = v___x_899_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_x_876_);
lean_ctor_set(v_reuseFailAlloc_908_, 1, v_x_877_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
v___y_891_ = v___x_907_;
goto v___jp_890_;
}
}
}
}
case 1:
{
lean_object* v_node_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_922_; 
v_node_910_ = lean_ctor_get(v_v_887_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v_v_887_);
if (v_isSharedCheck_922_ == 0)
{
v___x_912_ = v_v_887_;
v_isShared_913_ = v_isSharedCheck_922_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_node_910_);
lean_dec(v_v_887_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_922_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
size_t v___x_914_; size_t v___x_915_; size_t v___x_916_; size_t v___x_917_; lean_object* v___x_918_; lean_object* v___x_920_; 
v___x_914_ = ((size_t)5ULL);
v___x_915_ = lean_usize_shift_right(v_x_874_, v___x_914_);
v___x_916_ = ((size_t)1ULL);
v___x_917_ = lean_usize_add(v_x_875_, v___x_916_);
v___x_918_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_node_910_, v___x_915_, v___x_917_, v_x_876_, v_x_877_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 0, v___x_918_);
v___x_920_ = v___x_912_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_918_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
v___y_891_ = v___x_920_;
goto v___jp_890_;
}
}
}
default: 
{
lean_object* v___x_923_; 
v___x_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_923_, 0, v_x_876_);
lean_ctor_set(v___x_923_, 1, v_x_877_);
v___y_891_ = v___x_923_;
goto v___jp_890_;
}
}
v___jp_890_:
{
lean_object* v___x_892_; lean_object* v___x_894_; 
v___x_892_ = lean_array_fset(v_xs_x27_889_, v_j_881_, v___y_891_);
lean_dec(v_j_881_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v___x_892_);
v___x_894_ = v___x_885_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_892_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
}
else
{
lean_object* v_ks_926_; lean_object* v_vs_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_945_; 
v_ks_926_ = lean_ctor_get(v_x_873_, 0);
v_vs_927_ = lean_ctor_get(v_x_873_, 1);
v_isSharedCheck_945_ = !lean_is_exclusive(v_x_873_);
if (v_isSharedCheck_945_ == 0)
{
v___x_929_ = v_x_873_;
v_isShared_930_ = v_isSharedCheck_945_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_vs_927_);
lean_inc(v_ks_926_);
lean_dec(v_x_873_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_945_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_ks_926_);
lean_ctor_set(v_reuseFailAlloc_944_, 1, v_vs_927_);
v___x_932_ = v_reuseFailAlloc_944_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
lean_object* v_newNode_933_; size_t v___x_934_; uint8_t v___x_935_; 
v_newNode_933_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4___redArg(v___x_932_, v_x_876_, v_x_877_);
v___x_934_ = ((size_t)7ULL);
v___x_935_ = lean_usize_dec_le(v___x_934_, v_x_875_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; lean_object* v___x_937_; uint8_t v___x_938_; 
v___x_936_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_933_);
v___x_937_ = lean_unsigned_to_nat(4u);
v___x_938_ = lean_nat_dec_lt(v___x_936_, v___x_937_);
lean_dec(v___x_936_);
if (v___x_938_ == 0)
{
lean_object* v_ks_939_; lean_object* v_vs_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v_ks_939_ = lean_ctor_get(v_newNode_933_, 0);
lean_inc_ref(v_ks_939_);
v_vs_940_ = lean_ctor_get(v_newNode_933_, 1);
lean_inc_ref(v_vs_940_);
lean_dec_ref(v_newNode_933_);
v___x_941_ = lean_unsigned_to_nat(0u);
v___x_942_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0);
v___x_943_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(v_x_875_, v_ks_939_, v_vs_940_, v___x_941_, v___x_942_);
lean_dec_ref(v_vs_940_);
lean_dec_ref(v_ks_939_);
return v___x_943_;
}
else
{
return v_newNode_933_;
}
}
else
{
return v_newNode_933_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(size_t v_depth_946_, lean_object* v_keys_947_, lean_object* v_vals_948_, lean_object* v_i_949_, lean_object* v_entries_950_){
_start:
{
lean_object* v___x_951_; uint8_t v___x_952_; 
v___x_951_ = lean_array_get_size(v_keys_947_);
v___x_952_ = lean_nat_dec_lt(v_i_949_, v___x_951_);
if (v___x_952_ == 0)
{
lean_dec(v_i_949_);
return v_entries_950_;
}
else
{
lean_object* v_k_953_; lean_object* v_v_954_; size_t v___x_955_; size_t v___x_956_; size_t v___x_957_; uint64_t v___x_958_; size_t v_h_959_; size_t v___x_960_; lean_object* v___x_961_; size_t v___x_962_; size_t v___x_963_; size_t v___x_964_; size_t v_h_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v_k_953_ = lean_array_fget_borrowed(v_keys_947_, v_i_949_);
v_v_954_ = lean_array_fget_borrowed(v_vals_948_, v_i_949_);
v___x_955_ = lean_ptr_addr(v_k_953_);
v___x_956_ = ((size_t)3ULL);
v___x_957_ = lean_usize_shift_right(v___x_955_, v___x_956_);
v___x_958_ = lean_usize_to_uint64(v___x_957_);
v_h_959_ = lean_uint64_to_usize(v___x_958_);
v___x_960_ = ((size_t)5ULL);
v___x_961_ = lean_unsigned_to_nat(1u);
v___x_962_ = ((size_t)1ULL);
v___x_963_ = lean_usize_sub(v_depth_946_, v___x_962_);
v___x_964_ = lean_usize_mul(v___x_960_, v___x_963_);
v_h_965_ = lean_usize_shift_right(v_h_959_, v___x_964_);
v___x_966_ = lean_nat_add(v_i_949_, v___x_961_);
lean_dec(v_i_949_);
lean_inc(v_v_954_);
lean_inc(v_k_953_);
v___x_967_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_entries_950_, v_h_965_, v_depth_946_, v_k_953_, v_v_954_);
v_i_949_ = v___x_966_;
v_entries_950_ = v___x_967_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_969_, lean_object* v_keys_970_, lean_object* v_vals_971_, lean_object* v_i_972_, lean_object* v_entries_973_){
_start:
{
size_t v_depth_boxed_974_; lean_object* v_res_975_; 
v_depth_boxed_974_ = lean_unbox_usize(v_depth_969_);
lean_dec(v_depth_969_);
v_res_975_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(v_depth_boxed_974_, v_keys_970_, v_vals_971_, v_i_972_, v_entries_973_);
lean_dec_ref(v_vals_971_);
lean_dec_ref(v_keys_970_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg___boxed(lean_object* v_x_976_, lean_object* v_x_977_, lean_object* v_x_978_, lean_object* v_x_979_, lean_object* v_x_980_){
_start:
{
size_t v_x_27427__boxed_981_; size_t v_x_27428__boxed_982_; lean_object* v_res_983_; 
v_x_27427__boxed_981_ = lean_unbox_usize(v_x_977_);
lean_dec(v_x_977_);
v_x_27428__boxed_982_ = lean_unbox_usize(v_x_978_);
lean_dec(v_x_978_);
v_res_983_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_x_976_, v_x_27427__boxed_981_, v_x_27428__boxed_982_, v_x_979_, v_x_980_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg(lean_object* v_x_984_, lean_object* v_x_985_, lean_object* v_x_986_){
_start:
{
size_t v___x_987_; size_t v___x_988_; size_t v___x_989_; uint64_t v___x_990_; size_t v___x_991_; size_t v___x_992_; lean_object* v___x_993_; 
v___x_987_ = lean_ptr_addr(v_x_985_);
v___x_988_ = ((size_t)3ULL);
v___x_989_ = lean_usize_shift_right(v___x_987_, v___x_988_);
v___x_990_ = lean_usize_to_uint64(v___x_989_);
v___x_991_ = lean_uint64_to_usize(v___x_990_);
v___x_992_ = ((size_t)1ULL);
v___x_993_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_x_984_, v___x_991_, v___x_992_, v_x_985_, v_x_986_);
return v___x_993_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_994_ = lean_unsigned_to_nat(32u);
v___x_995_ = lean_mk_empty_array_with_capacity(v___x_994_);
v___x_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
return v___x_996_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1(void){
_start:
{
size_t v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_997_ = ((size_t)5ULL);
v___x_998_ = lean_unsigned_to_nat(0u);
v___x_999_ = lean_unsigned_to_nat(32u);
v___x_1000_ = lean_mk_empty_array_with_capacity(v___x_999_);
v___x_1001_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0);
v___x_1002_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
lean_ctor_set(v___x_1002_, 1, v___x_1000_);
lean_ctor_set(v___x_1002_, 2, v___x_998_);
lean_ctor_set(v___x_1002_, 3, v___x_998_);
lean_ctor_set_usize(v___x_1002_, 4, v___x_997_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0(lean_object* v_expr_1003_, lean_object* v_size_1004_, lean_object* v_s_1005_){
_start:
{
lean_object* v_vars_1006_; lean_object* v_varMap_1007_; lean_object* v_vars_x27_1008_; lean_object* v_varMap_x27_1009_; lean_object* v_natToIntMap_1010_; lean_object* v_natDef_1011_; lean_object* v_dvds_1012_; lean_object* v_lowers_1013_; lean_object* v_uppers_1014_; lean_object* v_diseqs_1015_; lean_object* v_elimEqs_1016_; lean_object* v_elimStack_1017_; lean_object* v_occurs_1018_; lean_object* v_assignment_1019_; lean_object* v_nextCnstrId_1020_; uint8_t v_caseSplits_1021_; lean_object* v_steps_1022_; lean_object* v_conflict_x3f_1023_; lean_object* v_diseqSplits_1024_; lean_object* v_divMod_1025_; uint8_t v_usedCommRing_1026_; lean_object* v_nonlinearOccs_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1045_; 
v_vars_1006_ = lean_ctor_get(v_s_1005_, 0);
v_varMap_1007_ = lean_ctor_get(v_s_1005_, 1);
v_vars_x27_1008_ = lean_ctor_get(v_s_1005_, 2);
v_varMap_x27_1009_ = lean_ctor_get(v_s_1005_, 3);
v_natToIntMap_1010_ = lean_ctor_get(v_s_1005_, 4);
v_natDef_1011_ = lean_ctor_get(v_s_1005_, 5);
v_dvds_1012_ = lean_ctor_get(v_s_1005_, 6);
v_lowers_1013_ = lean_ctor_get(v_s_1005_, 7);
v_uppers_1014_ = lean_ctor_get(v_s_1005_, 8);
v_diseqs_1015_ = lean_ctor_get(v_s_1005_, 9);
v_elimEqs_1016_ = lean_ctor_get(v_s_1005_, 10);
v_elimStack_1017_ = lean_ctor_get(v_s_1005_, 11);
v_occurs_1018_ = lean_ctor_get(v_s_1005_, 12);
v_assignment_1019_ = lean_ctor_get(v_s_1005_, 13);
v_nextCnstrId_1020_ = lean_ctor_get(v_s_1005_, 14);
v_caseSplits_1021_ = lean_ctor_get_uint8(v_s_1005_, sizeof(void*)*20);
v_steps_1022_ = lean_ctor_get(v_s_1005_, 15);
v_conflict_x3f_1023_ = lean_ctor_get(v_s_1005_, 16);
v_diseqSplits_1024_ = lean_ctor_get(v_s_1005_, 17);
v_divMod_1025_ = lean_ctor_get(v_s_1005_, 18);
v_usedCommRing_1026_ = lean_ctor_get_uint8(v_s_1005_, sizeof(void*)*20 + 1);
v_nonlinearOccs_1027_ = lean_ctor_get(v_s_1005_, 19);
v_isSharedCheck_1045_ = !lean_is_exclusive(v_s_1005_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1029_ = v_s_1005_;
v_isShared_1030_ = v_isSharedCheck_1045_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_nonlinearOccs_1027_);
lean_inc(v_divMod_1025_);
lean_inc(v_diseqSplits_1024_);
lean_inc(v_conflict_x3f_1023_);
lean_inc(v_steps_1022_);
lean_inc(v_nextCnstrId_1020_);
lean_inc(v_assignment_1019_);
lean_inc(v_occurs_1018_);
lean_inc(v_elimStack_1017_);
lean_inc(v_elimEqs_1016_);
lean_inc(v_diseqs_1015_);
lean_inc(v_uppers_1014_);
lean_inc(v_lowers_1013_);
lean_inc(v_dvds_1012_);
lean_inc(v_natDef_1011_);
lean_inc(v_natToIntMap_1010_);
lean_inc(v_varMap_x27_1009_);
lean_inc(v_vars_x27_1008_);
lean_inc(v_varMap_1007_);
lean_inc(v_vars_1006_);
lean_dec(v_s_1005_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1045_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1043_; 
lean_inc_ref(v_expr_1003_);
v___x_1031_ = l_Lean_PersistentArray_push___redArg(v_vars_1006_, v_expr_1003_);
v___x_1032_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg(v_varMap_1007_, v_expr_1003_, v_size_1004_);
v___x_1033_ = lean_box(0);
v___x_1034_ = l_Lean_PersistentArray_push___redArg(v_dvds_1012_, v___x_1033_);
v___x_1035_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1);
v___x_1036_ = l_Lean_PersistentArray_push___redArg(v_lowers_1013_, v___x_1035_);
v___x_1037_ = l_Lean_PersistentArray_push___redArg(v_uppers_1014_, v___x_1035_);
v___x_1038_ = l_Lean_PersistentArray_push___redArg(v_diseqs_1015_, v___x_1035_);
v___x_1039_ = l_Lean_PersistentArray_push___redArg(v_elimEqs_1016_, v___x_1033_);
v___x_1040_ = lean_box(1);
v___x_1041_ = l_Lean_PersistentArray_push___redArg(v_occurs_1018_, v___x_1040_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 12, v___x_1041_);
lean_ctor_set(v___x_1029_, 10, v___x_1039_);
lean_ctor_set(v___x_1029_, 9, v___x_1038_);
lean_ctor_set(v___x_1029_, 8, v___x_1037_);
lean_ctor_set(v___x_1029_, 7, v___x_1036_);
lean_ctor_set(v___x_1029_, 6, v___x_1034_);
lean_ctor_set(v___x_1029_, 1, v___x_1032_);
lean_ctor_set(v___x_1029_, 0, v___x_1031_);
v___x_1043_ = v___x_1029_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 20, 2);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1031_);
lean_ctor_set(v_reuseFailAlloc_1044_, 1, v___x_1032_);
lean_ctor_set(v_reuseFailAlloc_1044_, 2, v_vars_x27_1008_);
lean_ctor_set(v_reuseFailAlloc_1044_, 3, v_varMap_x27_1009_);
lean_ctor_set(v_reuseFailAlloc_1044_, 4, v_natToIntMap_1010_);
lean_ctor_set(v_reuseFailAlloc_1044_, 5, v_natDef_1011_);
lean_ctor_set(v_reuseFailAlloc_1044_, 6, v___x_1034_);
lean_ctor_set(v_reuseFailAlloc_1044_, 7, v___x_1036_);
lean_ctor_set(v_reuseFailAlloc_1044_, 8, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1044_, 9, v___x_1038_);
lean_ctor_set(v_reuseFailAlloc_1044_, 10, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1044_, 11, v_elimStack_1017_);
lean_ctor_set(v_reuseFailAlloc_1044_, 12, v___x_1041_);
lean_ctor_set(v_reuseFailAlloc_1044_, 13, v_assignment_1019_);
lean_ctor_set(v_reuseFailAlloc_1044_, 14, v_nextCnstrId_1020_);
lean_ctor_set(v_reuseFailAlloc_1044_, 15, v_steps_1022_);
lean_ctor_set(v_reuseFailAlloc_1044_, 16, v_conflict_x3f_1023_);
lean_ctor_set(v_reuseFailAlloc_1044_, 17, v_diseqSplits_1024_);
lean_ctor_set(v_reuseFailAlloc_1044_, 18, v_divMod_1025_);
lean_ctor_set(v_reuseFailAlloc_1044_, 19, v_nonlinearOccs_1027_);
lean_ctor_set_uint8(v_reuseFailAlloc_1044_, sizeof(void*)*20, v_caseSplits_1021_);
lean_ctor_set_uint8(v_reuseFailAlloc_1044_, sizeof(void*)*20 + 1, v_usedCommRing_1026_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1046_, lean_object* v_vals_1047_, lean_object* v_i_1048_, lean_object* v_k_1049_){
_start:
{
lean_object* v___x_1050_; uint8_t v___x_1051_; 
v___x_1050_ = lean_array_get_size(v_keys_1046_);
v___x_1051_ = lean_nat_dec_lt(v_i_1048_, v___x_1050_);
if (v___x_1051_ == 0)
{
lean_object* v___x_1052_; 
lean_dec(v_i_1048_);
v___x_1052_ = lean_box(0);
return v___x_1052_;
}
else
{
lean_object* v_k_x27_1053_; size_t v___x_1054_; size_t v___x_1055_; uint8_t v___x_1056_; 
v_k_x27_1053_ = lean_array_fget_borrowed(v_keys_1046_, v_i_1048_);
v___x_1054_ = lean_ptr_addr(v_k_1049_);
v___x_1055_ = lean_ptr_addr(v_k_x27_1053_);
v___x_1056_ = lean_usize_dec_eq(v___x_1054_, v___x_1055_);
if (v___x_1056_ == 0)
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = lean_unsigned_to_nat(1u);
v___x_1058_ = lean_nat_add(v_i_1048_, v___x_1057_);
lean_dec(v_i_1048_);
v_i_1048_ = v___x_1058_;
goto _start;
}
else
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = lean_array_fget_borrowed(v_vals_1047_, v_i_1048_);
lean_dec(v_i_1048_);
lean_inc(v___x_1060_);
v___x_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
return v___x_1061_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1062_, lean_object* v_vals_1063_, lean_object* v_i_1064_, lean_object* v_k_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(v_keys_1062_, v_vals_1063_, v_i_1064_, v_k_1065_);
lean_dec_ref(v_k_1065_);
lean_dec_ref(v_vals_1063_);
lean_dec_ref(v_keys_1062_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(lean_object* v_x_1067_, size_t v_x_1068_, lean_object* v_x_1069_){
_start:
{
if (lean_obj_tag(v_x_1067_) == 0)
{
lean_object* v_es_1070_; lean_object* v___x_1071_; size_t v___x_1072_; size_t v___x_1073_; lean_object* v_j_1074_; lean_object* v___x_1075_; 
v_es_1070_ = lean_ctor_get(v_x_1067_, 0);
v___x_1071_ = lean_box(2);
v___x_1072_ = ((size_t)31ULL);
v___x_1073_ = lean_usize_land(v_x_1068_, v___x_1072_);
v_j_1074_ = lean_usize_to_nat(v___x_1073_);
v___x_1075_ = lean_array_get_borrowed(v___x_1071_, v_es_1070_, v_j_1074_);
lean_dec(v_j_1074_);
switch(lean_obj_tag(v___x_1075_))
{
case 0:
{
lean_object* v_key_1076_; lean_object* v_val_1077_; size_t v___x_1078_; size_t v___x_1079_; uint8_t v___x_1080_; 
v_key_1076_ = lean_ctor_get(v___x_1075_, 0);
v_val_1077_ = lean_ctor_get(v___x_1075_, 1);
v___x_1078_ = lean_ptr_addr(v_x_1069_);
v___x_1079_ = lean_ptr_addr(v_key_1076_);
v___x_1080_ = lean_usize_dec_eq(v___x_1078_, v___x_1079_);
if (v___x_1080_ == 0)
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_box(0);
return v___x_1081_;
}
else
{
lean_object* v___x_1082_; 
lean_inc(v_val_1077_);
v___x_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1082_, 0, v_val_1077_);
return v___x_1082_;
}
}
case 1:
{
lean_object* v_node_1083_; size_t v___x_1084_; size_t v___x_1085_; 
v_node_1083_ = lean_ctor_get(v___x_1075_, 0);
v___x_1084_ = ((size_t)5ULL);
v___x_1085_ = lean_usize_shift_right(v_x_1068_, v___x_1084_);
v_x_1067_ = v_node_1083_;
v_x_1068_ = v___x_1085_;
goto _start;
}
default: 
{
lean_object* v___x_1087_; 
v___x_1087_ = lean_box(0);
return v___x_1087_;
}
}
}
else
{
lean_object* v_ks_1088_; lean_object* v_vs_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v_ks_1088_ = lean_ctor_get(v_x_1067_, 0);
v_vs_1089_ = lean_ctor_get(v_x_1067_, 1);
v___x_1090_ = lean_unsigned_to_nat(0u);
v___x_1091_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(v_ks_1088_, v_vs_1089_, v___x_1090_, v_x_1069_);
return v___x_1091_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg___boxed(lean_object* v_x_1092_, lean_object* v_x_1093_, lean_object* v_x_1094_){
_start:
{
size_t v_x_27692__boxed_1095_; lean_object* v_res_1096_; 
v_x_27692__boxed_1095_ = lean_unbox_usize(v_x_1093_);
lean_dec(v_x_1093_);
v_res_1096_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(v_x_1092_, v_x_27692__boxed_1095_, v_x_1094_);
lean_dec_ref(v_x_1094_);
lean_dec_ref(v_x_1092_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(lean_object* v_x_1097_, lean_object* v_x_1098_){
_start:
{
size_t v___x_1099_; size_t v___x_1100_; size_t v___x_1101_; uint64_t v___x_1102_; size_t v___x_1103_; lean_object* v___x_1104_; 
v___x_1099_ = lean_ptr_addr(v_x_1098_);
v___x_1100_ = ((size_t)3ULL);
v___x_1101_ = lean_usize_shift_right(v___x_1099_, v___x_1100_);
v___x_1102_ = lean_usize_to_uint64(v___x_1101_);
v___x_1103_ = lean_uint64_to_usize(v___x_1102_);
v___x_1104_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(v_x_1097_, v___x_1103_, v_x_1098_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg___boxed(lean_object* v_x_1105_, lean_object* v_x_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(v_x_1105_, v_x_1106_);
lean_dec_ref(v_x_1106_);
lean_dec_ref(v_x_1105_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4(lean_object* v_msgData_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v___x_1114_; lean_object* v_env_1115_; lean_object* v___x_1116_; lean_object* v_toCold_1117_; lean_object* v_mctx_1118_; lean_object* v_lctx_1119_; lean_object* v_options_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1114_ = lean_st_ref_get(v___y_1112_);
v_env_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc_ref(v_env_1115_);
lean_dec(v___x_1114_);
v___x_1116_ = lean_st_ref_get(v___y_1110_);
v_toCold_1117_ = lean_ctor_get(v___y_1111_, 0);
v_mctx_1118_ = lean_ctor_get(v___x_1116_, 0);
lean_inc_ref(v_mctx_1118_);
lean_dec(v___x_1116_);
v_lctx_1119_ = lean_ctor_get(v___y_1109_, 2);
v_options_1120_ = lean_ctor_get(v_toCold_1117_, 2);
lean_inc_ref(v_options_1120_);
lean_inc_ref(v_lctx_1119_);
v___x_1121_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1121_, 0, v_env_1115_);
lean_ctor_set(v___x_1121_, 1, v_mctx_1118_);
lean_ctor_set(v___x_1121_, 2, v_lctx_1119_);
lean_ctor_set(v___x_1121_, 3, v_options_1120_);
v___x_1122_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1121_);
lean_ctor_set(v___x_1122_, 1, v_msgData_1108_);
v___x_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1122_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4___boxed(lean_object* v_msgData_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4(v_msgData_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
return v_res_1130_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1131_; double v___x_1132_; 
v___x_1131_ = lean_unsigned_to_nat(0u);
v___x_1132_ = lean_float_of_nat(v___x_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(lean_object* v_cls_1136_, lean_object* v_msg_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v_ref_1143_; lean_object* v___x_1144_; lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1189_; 
v_ref_1143_ = lean_ctor_get(v___y_1140_, 2);
v___x_1144_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4(v_msg_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1147_ = v___x_1144_;
v_isShared_1148_ = v_isSharedCheck_1189_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1144_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1189_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1149_; lean_object* v_traceState_1150_; lean_object* v_env_1151_; lean_object* v_nextMacroScope_1152_; lean_object* v_ngen_1153_; lean_object* v_auxDeclNGen_1154_; lean_object* v_cache_1155_; lean_object* v_messages_1156_; lean_object* v_infoState_1157_; lean_object* v_snapshotTasks_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1188_; 
v___x_1149_ = lean_st_ref_take(v___y_1141_);
v_traceState_1150_ = lean_ctor_get(v___x_1149_, 4);
v_env_1151_ = lean_ctor_get(v___x_1149_, 0);
v_nextMacroScope_1152_ = lean_ctor_get(v___x_1149_, 1);
v_ngen_1153_ = lean_ctor_get(v___x_1149_, 2);
v_auxDeclNGen_1154_ = lean_ctor_get(v___x_1149_, 3);
v_cache_1155_ = lean_ctor_get(v___x_1149_, 5);
v_messages_1156_ = lean_ctor_get(v___x_1149_, 6);
v_infoState_1157_ = lean_ctor_get(v___x_1149_, 7);
v_snapshotTasks_1158_ = lean_ctor_get(v___x_1149_, 8);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1160_ = v___x_1149_;
v_isShared_1161_ = v_isSharedCheck_1188_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_snapshotTasks_1158_);
lean_inc(v_infoState_1157_);
lean_inc(v_messages_1156_);
lean_inc(v_cache_1155_);
lean_inc(v_traceState_1150_);
lean_inc(v_auxDeclNGen_1154_);
lean_inc(v_ngen_1153_);
lean_inc(v_nextMacroScope_1152_);
lean_inc(v_env_1151_);
lean_dec(v___x_1149_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1188_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
uint64_t v_tid_1162_; lean_object* v_traces_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1187_; 
v_tid_1162_ = lean_ctor_get_uint64(v_traceState_1150_, sizeof(void*)*1);
v_traces_1163_ = lean_ctor_get(v_traceState_1150_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v_traceState_1150_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1165_ = v_traceState_1150_;
v_isShared_1166_ = v_isSharedCheck_1187_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_traces_1163_);
lean_dec(v_traceState_1150_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1187_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; double v___x_1169_; uint8_t v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1178_; 
v___x_1167_ = lean_box(0);
v___x_1168_ = lean_box(0);
v___x_1169_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0);
v___x_1170_ = 0;
v___x_1171_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__1));
v___x_1172_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1172_, 0, v_cls_1136_);
lean_ctor_set(v___x_1172_, 1, v___x_1168_);
lean_ctor_set(v___x_1172_, 2, v___x_1171_);
lean_ctor_set_float(v___x_1172_, sizeof(void*)*3, v___x_1169_);
lean_ctor_set_float(v___x_1172_, sizeof(void*)*3 + 8, v___x_1169_);
lean_ctor_set_uint8(v___x_1172_, sizeof(void*)*3 + 16, v___x_1170_);
v___x_1173_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__2));
v___x_1174_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1172_);
lean_ctor_set(v___x_1174_, 1, v_a_1145_);
lean_ctor_set(v___x_1174_, 2, v___x_1173_);
lean_inc(v_ref_1143_);
v___x_1175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1175_, 0, v_ref_1143_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
v___x_1176_ = l_Lean_PersistentArray_push___redArg(v_traces_1163_, v___x_1175_);
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 0, v___x_1176_);
v___x_1178_ = v___x_1165_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1176_);
lean_ctor_set_uint64(v_reuseFailAlloc_1186_, sizeof(void*)*1, v_tid_1162_);
v___x_1178_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
lean_object* v___x_1180_; 
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 4, v___x_1178_);
v___x_1180_ = v___x_1160_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_env_1151_);
lean_ctor_set(v_reuseFailAlloc_1185_, 1, v_nextMacroScope_1152_);
lean_ctor_set(v_reuseFailAlloc_1185_, 2, v_ngen_1153_);
lean_ctor_set(v_reuseFailAlloc_1185_, 3, v_auxDeclNGen_1154_);
lean_ctor_set(v_reuseFailAlloc_1185_, 4, v___x_1178_);
lean_ctor_set(v_reuseFailAlloc_1185_, 5, v_cache_1155_);
lean_ctor_set(v_reuseFailAlloc_1185_, 6, v_messages_1156_);
lean_ctor_set(v_reuseFailAlloc_1185_, 7, v_infoState_1157_);
lean_ctor_set(v_reuseFailAlloc_1185_, 8, v_snapshotTasks_1158_);
v___x_1180_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
lean_object* v___x_1181_; lean_object* v___x_1183_; 
v___x_1181_ = lean_st_ref_put(v___y_1141_, v___x_1180_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 0, v___x_1167_);
v___x_1183_ = v___x_1147_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1167_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___boxed(lean_object* v_cls_1190_, lean_object* v_msg_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(v_cls_1190_, v_msg_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
return v_res_1197_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7(void){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1210_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4));
v___x_1211_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__6));
v___x_1212_ = l_Lean_Name_append(v___x_1211_, v___x_1210_);
return v___x_1212_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9(void){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1214_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__8));
v___x_1215_ = l_Lean_stringToMessageData(v___x_1214_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* lean_grind_cutsat_mk_var(lean_object* v_expr_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_){
_start:
{
lean_object* v___x_1228_; 
v___x_1228_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1217_, v_a_1225_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1358_; 
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1231_ = v___x_1228_;
v_isShared_1232_ = v_isSharedCheck_1358_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1228_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1358_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v_varMap_1233_; lean_object* v___x_1234_; 
v_varMap_1233_ = lean_ctor_get(v_a_1229_, 1);
lean_inc_ref(v_varMap_1233_);
lean_dec(v_a_1229_);
v___x_1234_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(v_varMap_1233_, v_expr_1216_);
lean_dec_ref(v_varMap_1233_);
if (lean_obj_tag(v___x_1234_) == 1)
{
lean_object* v_val_1235_; lean_object* v___x_1237_; 
lean_dec(v_a_1226_);
lean_dec_ref(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec_ref(v_a_1223_);
lean_dec(v_a_1222_);
lean_dec_ref(v_a_1221_);
lean_dec(v_a_1220_);
lean_dec_ref(v_a_1219_);
lean_dec(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec_ref(v_expr_1216_);
v_val_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_val_1235_);
lean_dec_ref_known(v___x_1234_, 1);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 0, v_val_1235_);
v___x_1237_ = v___x_1231_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_val_1235_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
else
{
lean_object* v___x_1239_; 
lean_dec(v___x_1234_);
lean_del_object(v___x_1231_);
v___x_1239_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1217_, v_a_1225_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v_a_1240_; lean_object* v_vars_1241_; lean_object* v_toCold_1242_; lean_object* v_options_1243_; lean_object* v_size_1244_; lean_object* v_inheritedTraceOptions_1245_; uint8_t v_hasTrace_1246_; lean_object* v___f_1247_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; 
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
lean_inc(v_a_1240_);
lean_dec_ref_known(v___x_1239_, 1);
v_vars_1241_ = lean_ctor_get(v_a_1240_, 0);
lean_inc_ref(v_vars_1241_);
lean_dec(v_a_1240_);
v_toCold_1242_ = lean_ctor_get(v_a_1225_, 0);
v_options_1243_ = lean_ctor_get(v_toCold_1242_, 2);
v_size_1244_ = lean_ctor_get(v_vars_1241_, 2);
lean_inc_n(v_size_1244_, 2);
lean_dec_ref(v_vars_1241_);
v_inheritedTraceOptions_1245_ = lean_ctor_get(v_toCold_1242_, 11);
v_hasTrace_1246_ = lean_ctor_get_uint8(v_options_1243_, sizeof(void*)*1);
lean_inc_ref(v_expr_1216_);
v___f_1247_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0), 3, 2);
lean_closure_set(v___f_1247_, 0, v_expr_1216_);
lean_closure_set(v___f_1247_, 1, v_size_1244_);
if (v_hasTrace_1246_ == 0)
{
v___y_1249_ = v_a_1217_;
v___y_1250_ = v_a_1218_;
v___y_1251_ = v_a_1219_;
v___y_1252_ = v_a_1220_;
v___y_1253_ = v_a_1221_;
v___y_1254_ = v_a_1222_;
v___y_1255_ = v_a_1223_;
v___y_1256_ = v_a_1224_;
v___y_1257_ = v_a_1225_;
v___y_1258_ = v_a_1226_;
goto v___jp_1248_;
}
else
{
lean_object* v___x_1331_; lean_object* v___x_1332_; uint8_t v___x_1333_; 
v___x_1331_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4));
v___x_1332_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7);
v___x_1333_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1245_, v_options_1243_, v___x_1332_);
if (v___x_1333_ == 0)
{
v___y_1249_ = v_a_1217_;
v___y_1250_ = v_a_1218_;
v___y_1251_ = v_a_1219_;
v___y_1252_ = v_a_1220_;
v___y_1253_ = v_a_1221_;
v___y_1254_ = v_a_1222_;
v___y_1255_ = v_a_1223_;
v___y_1256_ = v_a_1224_;
v___y_1257_ = v_a_1225_;
v___y_1258_ = v_a_1226_;
goto v___jp_1248_;
}
else
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
lean_inc_ref(v_expr_1216_);
v___x_1334_ = l_Lean_MessageData_ofExpr(v_expr_1216_);
v___x_1335_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9);
v___x_1336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1334_);
lean_ctor_set(v___x_1336_, 1, v___x_1335_);
lean_inc(v_size_1244_);
v___x_1337_ = l_Nat_reprFast(v_size_1244_);
v___x_1338_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1337_);
v___x_1339_ = l_Lean_MessageData_ofFormat(v___x_1338_);
v___x_1340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1336_);
lean_ctor_set(v___x_1340_, 1, v___x_1339_);
v___x_1341_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(v___x_1331_, v___x_1340_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_dec_ref_known(v___x_1341_, 1);
v___y_1249_ = v_a_1217_;
v___y_1250_ = v_a_1218_;
v___y_1251_ = v_a_1219_;
v___y_1252_ = v_a_1220_;
v___y_1253_ = v_a_1221_;
v___y_1254_ = v_a_1222_;
v___y_1255_ = v_a_1223_;
v___y_1256_ = v_a_1224_;
v___y_1257_ = v_a_1225_;
v___y_1258_ = v_a_1226_;
goto v___jp_1248_;
}
else
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
lean_dec_ref(v___f_1247_);
lean_dec(v_size_1244_);
lean_dec(v_a_1226_);
lean_dec_ref(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec_ref(v_a_1223_);
lean_dec(v_a_1222_);
lean_dec_ref(v_a_1221_);
lean_dec(v_a_1220_);
lean_dec_ref(v_a_1219_);
lean_dec(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec_ref(v_expr_1216_);
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1344_ = v___x_1341_;
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1341_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_a_1342_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
}
v___jp_1248_:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_1260_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1259_, v___f_1247_, v___y_1249_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v___x_1261_; 
lean_dec_ref_known(v___x_1260_, 1);
lean_inc_ref(v_expr_1216_);
v___x_1261_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_1259_, v_expr_1216_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v___x_1262_; 
lean_dec_ref_known(v___x_1261_, 1);
lean_inc(v_size_1244_);
lean_inc_ref(v_expr_1216_);
v___x_1262_ = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(v_expr_1216_, v_size_1244_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v___x_1263_; 
lean_dec_ref_known(v___x_1262_, 1);
lean_inc(v_size_1244_);
lean_inc_ref(v_expr_1216_);
v___x_1263_ = l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg(v_expr_1216_, v_size_1244_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v___x_1264_; 
lean_dec_ref_known(v___x_1263_, 1);
lean_inc_ref(v_expr_1216_);
v___x_1264_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm(v_expr_1216_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1290_; 
v_a_1265_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1267_ = v___x_1264_;
v_isShared_1268_ = v_isSharedCheck_1290_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1264_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1290_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
uint8_t v___x_1269_; 
v___x_1269_ = lean_unbox(v_a_1265_);
lean_dec(v_a_1265_);
if (v___x_1269_ == 0)
{
lean_object* v___x_1271_; 
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v_expr_1216_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 0, v_size_1244_);
v___x_1271_ = v___x_1267_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_size_1244_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
else
{
lean_object* v___x_1273_; 
lean_del_object(v___x_1267_);
lean_inc(v_size_1244_);
v___x_1273_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt(v_expr_1216_, v_size_1244_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec(v___y_1249_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1280_; 
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1280_ == 0)
{
lean_object* v_unused_1281_; 
v_unused_1281_ = lean_ctor_get(v___x_1273_, 0);
lean_dec(v_unused_1281_);
v___x_1275_ = v___x_1273_;
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
else
{
lean_dec(v___x_1273_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 0, v_size_1244_);
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_size_1244_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
else
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
lean_dec(v_size_1244_);
v_a_1282_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v___x_1273_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1273_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1282_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
}
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec(v_size_1244_);
lean_dec_ref(v_expr_1216_);
v_a_1291_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1264_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1264_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
else
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1306_; 
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec(v_size_1244_);
lean_dec_ref(v_expr_1216_);
v_a_1299_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1301_ = v___x_1263_;
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1263_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1304_; 
if (v_isShared_1302_ == 0)
{
v___x_1304_ = v___x_1301_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_a_1299_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
else
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec(v_size_1244_);
lean_dec_ref(v_expr_1216_);
v_a_1307_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1309_ = v___x_1262_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1262_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1307_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
else
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1322_; 
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec(v_size_1244_);
lean_dec_ref(v_expr_1216_);
v_a_1315_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1317_ = v___x_1261_;
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1261_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1320_; 
if (v_isShared_1318_ == 0)
{
v___x_1320_ = v___x_1317_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_a_1315_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
}
else
{
lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1330_; 
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec(v_size_1244_);
lean_dec_ref(v_expr_1216_);
v_a_1323_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1325_ = v___x_1260_;
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_dec(v___x_1260_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1328_; 
if (v_isShared_1326_ == 0)
{
v___x_1328_ = v___x_1325_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_a_1323_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
}
}
else
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
lean_dec(v_a_1226_);
lean_dec_ref(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec_ref(v_a_1223_);
lean_dec(v_a_1222_);
lean_dec_ref(v_a_1221_);
lean_dec(v_a_1220_);
lean_dec_ref(v_a_1219_);
lean_dec(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec_ref(v_expr_1216_);
v_a_1350_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1352_ = v___x_1239_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1239_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1350_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
}
}
else
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1366_; 
lean_dec(v_a_1226_);
lean_dec_ref(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec_ref(v_a_1223_);
lean_dec(v_a_1222_);
lean_dec_ref(v_a_1221_);
lean_dec(v_a_1220_);
lean_dec_ref(v_a_1219_);
lean_dec(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec_ref(v_expr_1216_);
v_a_1359_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1361_ = v___x_1228_;
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1228_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1364_; 
if (v_isShared_1362_ == 0)
{
v___x_1364_ = v___x_1361_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_a_1359_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___boxed(lean_object* v_expr_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = lean_grind_cutsat_mk_var(v_expr_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0(lean_object* v_00_u03b2_1380_, lean_object* v_x_1381_, lean_object* v_x_1382_){
_start:
{
lean_object* v___x_1383_; 
v___x_1383_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(v_x_1381_, v_x_1382_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___boxed(lean_object* v_00_u03b2_1384_, lean_object* v_x_1385_, lean_object* v_x_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0(v_00_u03b2_1384_, v_x_1385_, v_x_1386_);
lean_dec_ref(v_x_1386_);
lean_dec_ref(v_x_1385_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1(lean_object* v_00_u03b2_1388_, lean_object* v_x_1389_, lean_object* v_x_1390_, lean_object* v_x_1391_){
_start:
{
lean_object* v___x_1392_; 
v___x_1392_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg(v_x_1389_, v_x_1390_, v_x_1391_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2(lean_object* v_cls_1393_, lean_object* v_msg_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v___x_1406_; 
v___x_1406_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(v_cls_1393_, v_msg_1394_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___boxed(lean_object* v_cls_1407_, lean_object* v_msg_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
lean_object* v_res_1420_; 
v_res_1420_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2(v_cls_1407_, v_msg_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
lean_dec(v___y_1410_);
lean_dec(v___y_1409_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0(lean_object* v_00_u03b2_1421_, lean_object* v_x_1422_, size_t v_x_1423_, lean_object* v_x_1424_){
_start:
{
lean_object* v___x_1425_; 
v___x_1425_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(v_x_1422_, v_x_1423_, v_x_1424_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1426_, lean_object* v_x_1427_, lean_object* v_x_1428_, lean_object* v_x_1429_){
_start:
{
size_t v_x_28265__boxed_1430_; lean_object* v_res_1431_; 
v_x_28265__boxed_1430_ = lean_unbox_usize(v_x_1428_);
lean_dec(v_x_1428_);
v_res_1431_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0(v_00_u03b2_1426_, v_x_1427_, v_x_28265__boxed_1430_, v_x_1429_);
lean_dec_ref(v_x_1429_);
lean_dec_ref(v_x_1427_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2(lean_object* v_00_u03b2_1432_, lean_object* v_x_1433_, size_t v_x_1434_, size_t v_x_1435_, lean_object* v_x_1436_, lean_object* v_x_1437_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_x_1433_, v_x_1434_, v_x_1435_, v_x_1436_, v_x_1437_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1439_, lean_object* v_x_1440_, lean_object* v_x_1441_, lean_object* v_x_1442_, lean_object* v_x_1443_, lean_object* v_x_1444_){
_start:
{
size_t v_x_28276__boxed_1445_; size_t v_x_28277__boxed_1446_; lean_object* v_res_1447_; 
v_x_28276__boxed_1445_ = lean_unbox_usize(v_x_1441_);
lean_dec(v_x_1441_);
v_x_28277__boxed_1446_ = lean_unbox_usize(v_x_1442_);
lean_dec(v_x_1442_);
v_res_1447_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2(v_00_u03b2_1439_, v_x_1440_, v_x_28276__boxed_1445_, v_x_28277__boxed_1446_, v_x_1443_, v_x_1444_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1448_, lean_object* v_keys_1449_, lean_object* v_vals_1450_, lean_object* v_heq_1451_, lean_object* v_i_1452_, lean_object* v_k_1453_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(v_keys_1449_, v_vals_1450_, v_i_1452_, v_k_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1455_, lean_object* v_keys_1456_, lean_object* v_vals_1457_, lean_object* v_heq_1458_, lean_object* v_i_1459_, lean_object* v_k_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1(v_00_u03b2_1455_, v_keys_1456_, v_vals_1457_, v_heq_1458_, v_i_1459_, v_k_1460_);
lean_dec_ref(v_k_1460_);
lean_dec_ref(v_vals_1457_);
lean_dec_ref(v_keys_1456_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1462_, lean_object* v_n_1463_, lean_object* v_k_1464_, lean_object* v_v_1465_){
_start:
{
lean_object* v___x_1466_; 
v___x_1466_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4___redArg(v_n_1463_, v_k_1464_, v_v_1465_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1467_, size_t v_depth_1468_, lean_object* v_keys_1469_, lean_object* v_vals_1470_, lean_object* v_heq_1471_, lean_object* v_i_1472_, lean_object* v_entries_1473_){
_start:
{
lean_object* v___x_1474_; 
v___x_1474_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(v_depth_1468_, v_keys_1469_, v_vals_1470_, v_i_1472_, v_entries_1473_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1475_, lean_object* v_depth_1476_, lean_object* v_keys_1477_, lean_object* v_vals_1478_, lean_object* v_heq_1479_, lean_object* v_i_1480_, lean_object* v_entries_1481_){
_start:
{
size_t v_depth_boxed_1482_; lean_object* v_res_1483_; 
v_depth_boxed_1482_ = lean_unbox_usize(v_depth_1476_);
lean_dec(v_depth_1476_);
v_res_1483_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5(v_00_u03b2_1475_, v_depth_boxed_1482_, v_keys_1477_, v_vals_1478_, v_heq_1479_, v_i_1480_, v_entries_1481_);
lean_dec_ref(v_vals_1478_);
lean_dec_ref(v_keys_1477_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_1484_, lean_object* v_x_1485_, lean_object* v_x_1486_, lean_object* v_x_1487_, lean_object* v_x_1488_){
_start:
{
lean_object* v___x_1489_; 
v___x_1489_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7___redArg(v_x_1485_, v_x_1486_, v_x_1487_, v_x_1488_);
return v___x_1489_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2(void){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1493_ = lean_box(0);
v___x_1494_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__1));
v___x_1495_ = l_Lean_mkConst(v___x_1494_, v___x_1493_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(lean_object* v_e_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_){
_start:
{
lean_object* v___x_1502_; 
lean_inc(v_a_1500_);
lean_inc_ref(v_a_1499_);
lean_inc(v_a_1498_);
lean_inc_ref(v_a_1497_);
v___x_1502_ = lean_infer_type(v_e_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v_a_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_a_1503_);
lean_dec_ref_known(v___x_1502_, 1);
v___x_1504_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2);
v___x_1505_ = l_Lean_Meta_isExprDefEq(v_a_1503_, v___x_1504_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_);
return v___x_1505_;
}
else
{
lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1513_; 
v_a_1506_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1508_ = v___x_1502_;
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1502_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1511_; 
if (v_isShared_1509_ == 0)
{
v___x_1511_ = v___x_1508_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_a_1506_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___boxed(lean_object* v_e_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(v_e_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
lean_dec(v_a_1518_);
lean_dec_ref(v_a_1517_);
lean_dec(v_a_1516_);
lean_dec_ref(v_a_1515_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt(lean_object* v_e_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(v_e_1521_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___boxed(lean_object* v_e_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_Lean_Meta_Grind_Arith_Cutsat_isInt(v_e_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_);
lean_dec(v_a_1544_);
lean_dec_ref(v_a_1543_);
lean_dec(v_a_1542_);
lean_dec_ref(v_a_1541_);
lean_dec(v_a_1540_);
lean_dec_ref(v_a_1539_);
lean_dec(v_a_1538_);
lean_dec_ref(v_a_1537_);
lean_dec(v_a_1536_);
lean_dec(v_a_1535_);
return v_res_1546_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4(void){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1553_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__3));
v___x_1554_ = l_Lean_stringToMessageData(v___x_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(lean_object* v_e_1555_, uint8_t v_report_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_){
_start:
{
lean_object* v___x_1570_; 
lean_inc_ref(v_e_1555_);
v___x_1570_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1555_, v_a_1560_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; lean_object* v___x_1572_; uint8_t v___x_1573_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_a_1571_);
lean_dec_ref_known(v___x_1570_, 1);
v___x_1572_ = l_Lean_Expr_cleanupAnnotations(v_a_1571_);
v___x_1573_ = l_Lean_Expr_isApp(v___x_1572_);
if (v___x_1573_ == 0)
{
lean_dec_ref(v___x_1572_);
lean_dec_ref(v_e_1555_);
goto v___jp_1564_;
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
lean_dec_ref(v_e_1555_);
goto v___jp_1564_;
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
lean_dec_ref(v_e_1555_);
goto v___jp_1564_;
}
else
{
lean_object* v_arg_1580_; lean_object* v___x_1581_; uint8_t v___x_1582_; 
v_arg_1580_ = lean_ctor_get(v___x_1578_, 1);
lean_inc_ref(v_arg_1580_);
v___x_1581_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1578_);
v___x_1582_ = l_Lean_Expr_isApp(v___x_1581_);
if (v___x_1582_ == 0)
{
lean_dec_ref(v___x_1581_);
lean_dec_ref(v_arg_1580_);
lean_dec_ref(v_arg_1577_);
lean_dec_ref(v_arg_1574_);
lean_dec_ref(v_e_1555_);
goto v___jp_1564_;
}
else
{
lean_object* v___x_1583_; uint8_t v___x_1584_; 
v___x_1583_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1581_);
v___x_1584_ = l_Lean_Expr_isApp(v___x_1583_);
if (v___x_1584_ == 0)
{
lean_dec_ref(v___x_1583_);
lean_dec_ref(v_arg_1580_);
lean_dec_ref(v_arg_1577_);
lean_dec_ref(v_arg_1574_);
lean_dec_ref(v_e_1555_);
goto v___jp_1564_;
}
else
{
lean_object* v___x_1585_; uint8_t v___x_1586_; 
v___x_1585_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1583_);
v___x_1586_ = l_Lean_Expr_isApp(v___x_1585_);
if (v___x_1586_ == 0)
{
lean_dec_ref(v___x_1585_);
lean_dec_ref(v_arg_1580_);
lean_dec_ref(v_arg_1577_);
lean_dec_ref(v_arg_1574_);
lean_dec_ref(v_e_1555_);
goto v___jp_1564_;
}
else
{
lean_object* v___x_1587_; lean_object* v___x_1588_; uint8_t v___x_1589_; 
v___x_1587_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1585_);
v___x_1588_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__2));
v___x_1589_ = l_Lean_Expr_isConstOf(v___x_1587_, v___x_1588_);
lean_dec_ref(v___x_1587_);
if (v___x_1589_ == 0)
{
lean_dec_ref(v_arg_1580_);
lean_dec_ref(v_arg_1577_);
lean_dec_ref(v_arg_1574_);
lean_dec_ref(v_e_1555_);
goto v___jp_1564_;
}
else
{
lean_object* v___x_1590_; 
v___x_1590_ = l_Lean_Meta_Structural_isInstHAddInt___redArg(v_arg_1580_, v_a_1560_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1624_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1593_ = v___x_1590_;
v_isShared_1594_ = v_isSharedCheck_1624_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1590_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1624_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
uint8_t v___x_1595_; 
v___x_1595_ = lean_unbox(v_a_1591_);
lean_dec(v_a_1591_);
if (v___x_1595_ == 0)
{
lean_del_object(v___x_1593_);
lean_dec_ref(v_arg_1577_);
lean_dec_ref(v_arg_1574_);
if (v_report_1556_ == 0)
{
lean_dec_ref(v_e_1555_);
goto v___jp_1567_;
}
else
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1596_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4);
v___x_1597_ = l_Lean_indentExpr(v_e_1555_);
v___x_1598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1596_);
lean_ctor_set(v___x_1598_, 1, v___x_1597_);
v___x_1599_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1557_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v_a_1600_; uint8_t v_verbose_1601_; 
v_a_1600_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_a_1600_);
lean_dec_ref_known(v___x_1599_, 1);
v_verbose_1601_ = lean_ctor_get_uint8(v_a_1600_, 0);
lean_dec(v_a_1600_);
if (v_verbose_1601_ == 0)
{
lean_dec_ref_known(v___x_1598_, 2);
goto v___jp_1567_;
}
else
{
lean_object* v___x_1602_; 
v___x_1602_ = l_Lean_Meta_Sym_reportIssue(v___x_1598_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_dec_ref_known(v___x_1602_, 1);
goto v___jp_1567_;
}
else
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
v_a_1603_ = lean_ctor_get(v___x_1602_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1602_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1602_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1602_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
}
else
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
lean_dec_ref_known(v___x_1598_, 2);
v_a_1611_ = lean_ctor_get(v___x_1599_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1599_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1599_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
}
else
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1622_; 
lean_dec_ref(v_e_1555_);
v___x_1619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1619_, 0, v_arg_1577_);
lean_ctor_set(v___x_1619_, 1, v_arg_1574_);
v___x_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1619_);
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 0, v___x_1620_);
v___x_1622_ = v___x_1593_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1620_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
else
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1632_; 
lean_dec_ref(v_arg_1577_);
lean_dec_ref(v_arg_1574_);
lean_dec_ref(v_e_1555_);
v_a_1625_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1627_ = v___x_1590_;
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1590_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1630_; 
if (v_isShared_1628_ == 0)
{
v___x_1630_ = v___x_1627_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_a_1625_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
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
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
lean_dec_ref(v_e_1555_);
v_a_1633_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1635_ = v___x_1570_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1570_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
if (v_isShared_1636_ == 0)
{
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_a_1633_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
v___jp_1564_:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1565_ = lean_box(0);
v___x_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
return v___x_1566_;
}
v___jp_1567_:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = lean_box(0);
v___x_1569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1568_);
return v___x_1569_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___boxed(lean_object* v_e_1641_, lean_object* v_report_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_){
_start:
{
uint8_t v_report_boxed_1650_; lean_object* v_res_1651_; 
v_report_boxed_1650_ = lean_unbox(v_report_1642_);
v_res_1651_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_1641_, v_report_boxed_1650_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_);
lean_dec(v_a_1648_);
lean_dec_ref(v_a_1647_);
lean_dec(v_a_1646_);
lean_dec_ref(v_a_1645_);
lean_dec(v_a_1644_);
lean_dec_ref(v_a_1643_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f(lean_object* v_e_1652_, uint8_t v_report_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_){
_start:
{
lean_object* v___x_1665_; 
v___x_1665_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_1652_, v_report_1653_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___boxed(lean_object* v_e_1666_, lean_object* v_report_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_){
_start:
{
uint8_t v_report_boxed_1679_; lean_object* v_res_1680_; 
v_report_boxed_1679_ = lean_unbox(v_report_1667_);
v_res_1680_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f(v_e_1666_, v_report_boxed_1679_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_);
lean_dec(v_a_1677_);
lean_dec_ref(v_a_1676_);
lean_dec(v_a_1675_);
lean_dec_ref(v_a_1674_);
lean_dec(v_a_1673_);
lean_dec_ref(v_a_1672_);
lean_dec(v_a_1671_);
lean_dec_ref(v_a_1670_);
lean_dec(v_a_1669_);
lean_dec(v_a_1668_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(lean_object* v_e_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_){
_start:
{
uint8_t v___x_1689_; lean_object* v___x_1690_; 
v___x_1689_ = 0;
v___x_1690_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_1681_, v___x_1689_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1704_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1693_ = v___x_1690_;
v_isShared_1694_ = v_isSharedCheck_1704_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1690_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1704_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
if (lean_obj_tag(v_a_1691_) == 0)
{
lean_object* v___x_1695_; lean_object* v___x_1697_; 
v___x_1695_ = lean_box(v___x_1689_);
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 0, v___x_1695_);
v___x_1697_ = v___x_1693_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v___x_1695_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
else
{
uint8_t v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1702_; 
lean_dec_ref_known(v_a_1691_, 1);
v___x_1699_ = 1;
v___x_1700_ = lean_box(v___x_1699_);
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 0, v___x_1700_);
v___x_1702_ = v___x_1693_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v___x_1700_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
}
else
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1712_; 
v_a_1705_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1707_ = v___x_1690_;
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1690_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1710_; 
if (v_isShared_1708_ == 0)
{
v___x_1710_ = v___x_1707_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1705_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg___boxed(lean_object* v_e_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(v_e_1713_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_);
lean_dec(v_a_1719_);
lean_dec_ref(v_a_1718_);
lean_dec(v_a_1717_);
lean_dec_ref(v_a_1716_);
lean_dec(v_a_1715_);
lean_dec_ref(v_a_1714_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd(lean_object* v_e_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_){
_start:
{
lean_object* v___x_1734_; 
v___x_1734_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(v_e_1722_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___boxed(lean_object* v_e_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd(v_e_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_);
lean_dec(v_a_1745_);
lean_dec_ref(v_a_1744_);
lean_dec(v_a_1743_);
lean_dec_ref(v_a_1742_);
lean_dec(v_a_1741_);
lean_dec_ref(v_a_1740_);
lean_dec(v_a_1739_);
lean_dec_ref(v_a_1738_);
lean_dec(v_a_1737_);
lean_dec(v_a_1736_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(lean_object* v_e_1748_, uint8_t v_report_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_){
_start:
{
lean_object* v___x_1763_; 
lean_inc_ref(v_e_1748_);
v___x_1763_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1748_, v_a_1753_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; lean_object* v___x_1765_; uint8_t v___x_1766_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1764_);
lean_dec_ref_known(v___x_1763_, 1);
v___x_1765_ = l_Lean_Expr_cleanupAnnotations(v_a_1764_);
v___x_1766_ = l_Lean_Expr_isApp(v___x_1765_);
if (v___x_1766_ == 0)
{
lean_dec_ref(v___x_1765_);
lean_dec_ref(v_e_1748_);
goto v___jp_1757_;
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
lean_dec_ref(v_e_1748_);
goto v___jp_1757_;
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
lean_dec_ref(v_e_1748_);
goto v___jp_1757_;
}
else
{
lean_object* v_arg_1773_; lean_object* v___x_1774_; uint8_t v___x_1775_; 
v_arg_1773_ = lean_ctor_get(v___x_1771_, 1);
lean_inc_ref(v_arg_1773_);
v___x_1774_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1771_);
v___x_1775_ = l_Lean_Expr_isApp(v___x_1774_);
if (v___x_1775_ == 0)
{
lean_dec_ref(v___x_1774_);
lean_dec_ref(v_arg_1773_);
lean_dec_ref(v_arg_1770_);
lean_dec_ref(v_arg_1767_);
lean_dec_ref(v_e_1748_);
goto v___jp_1757_;
}
else
{
lean_object* v___x_1776_; uint8_t v___x_1777_; 
v___x_1776_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1774_);
v___x_1777_ = l_Lean_Expr_isApp(v___x_1776_);
if (v___x_1777_ == 0)
{
lean_dec_ref(v___x_1776_);
lean_dec_ref(v_arg_1773_);
lean_dec_ref(v_arg_1770_);
lean_dec_ref(v_arg_1767_);
lean_dec_ref(v_e_1748_);
goto v___jp_1757_;
}
else
{
lean_object* v___x_1778_; uint8_t v___x_1779_; 
v___x_1778_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1776_);
v___x_1779_ = l_Lean_Expr_isApp(v___x_1778_);
if (v___x_1779_ == 0)
{
lean_dec_ref(v___x_1778_);
lean_dec_ref(v_arg_1773_);
lean_dec_ref(v_arg_1770_);
lean_dec_ref(v_arg_1767_);
lean_dec_ref(v_e_1748_);
goto v___jp_1757_;
}
else
{
lean_object* v___x_1780_; lean_object* v___x_1781_; uint8_t v___x_1782_; 
v___x_1780_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1778_);
v___x_1781_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11));
v___x_1782_ = l_Lean_Expr_isConstOf(v___x_1780_, v___x_1781_);
lean_dec_ref(v___x_1780_);
if (v___x_1782_ == 0)
{
lean_dec_ref(v_arg_1773_);
lean_dec_ref(v_arg_1770_);
lean_dec_ref(v_arg_1767_);
lean_dec_ref(v_e_1748_);
goto v___jp_1757_;
}
else
{
lean_object* v___x_1783_; 
v___x_1783_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_1773_, v_a_1753_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v_a_1784_; uint8_t v___x_1785_; 
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
lean_inc(v_a_1784_);
lean_dec_ref_known(v___x_1783_, 1);
v___x_1785_ = lean_unbox(v_a_1784_);
lean_dec(v_a_1784_);
if (v___x_1785_ == 0)
{
lean_dec_ref(v_arg_1770_);
lean_dec_ref(v_arg_1767_);
if (v_report_1749_ == 0)
{
lean_dec_ref(v_e_1748_);
goto v___jp_1760_;
}
else
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1786_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4);
v___x_1787_ = l_Lean_indentExpr(v_e_1748_);
v___x_1788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1786_);
lean_ctor_set(v___x_1788_, 1, v___x_1787_);
v___x_1789_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1750_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v_a_1790_; uint8_t v_verbose_1791_; 
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
lean_inc(v_a_1790_);
lean_dec_ref_known(v___x_1789_, 1);
v_verbose_1791_ = lean_ctor_get_uint8(v_a_1790_, 0);
lean_dec(v_a_1790_);
if (v_verbose_1791_ == 0)
{
lean_dec_ref_known(v___x_1788_, 2);
goto v___jp_1760_;
}
else
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Lean_Meta_Sym_reportIssue(v___x_1788_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_dec_ref_known(v___x_1792_, 1);
goto v___jp_1760_;
}
else
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
v_a_1793_ = lean_ctor_get(v___x_1792_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1792_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1795_ = v___x_1792_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v___x_1792_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1793_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
}
else
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1808_; 
lean_dec_ref_known(v___x_1788_, 2);
v_a_1801_ = lean_ctor_get(v___x_1789_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1789_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1803_ = v___x_1789_;
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1789_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1808_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1806_; 
if (v_isShared_1804_ == 0)
{
v___x_1806_ = v___x_1803_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_a_1801_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
}
else
{
lean_object* v___x_1809_; 
lean_dec_ref(v_e_1748_);
v___x_1809_ = l_Lean_Meta_getIntValue_x3f(v_arg_1770_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1830_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1812_ = v___x_1809_;
v_isShared_1813_ = v_isSharedCheck_1830_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1809_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1830_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
if (lean_obj_tag(v_a_1810_) == 1)
{
lean_object* v_val_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1825_; 
v_val_1814_ = lean_ctor_get(v_a_1810_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v_a_1810_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1816_ = v_a_1810_;
v_isShared_1817_ = v_isSharedCheck_1825_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_val_1814_);
lean_dec(v_a_1810_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1825_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1818_; lean_object* v___x_1820_; 
v___x_1818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1818_, 0, v_val_1814_);
lean_ctor_set(v___x_1818_, 1, v_arg_1767_);
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 0, v___x_1818_);
v___x_1820_ = v___x_1816_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v___x_1818_);
v___x_1820_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
lean_object* v___x_1822_; 
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 0, v___x_1820_);
v___x_1822_ = v___x_1812_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v___x_1820_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
}
else
{
lean_object* v___x_1826_; lean_object* v___x_1828_; 
lean_dec(v_a_1810_);
lean_dec_ref(v_arg_1767_);
v___x_1826_ = lean_box(0);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 0, v___x_1826_);
v___x_1828_ = v___x_1812_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v___x_1826_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
}
else
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1838_; 
lean_dec_ref(v_arg_1767_);
v_a_1831_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1833_ = v___x_1809_;
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v___x_1809_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1836_; 
if (v_isShared_1834_ == 0)
{
v___x_1836_ = v___x_1833_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_a_1831_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
}
}
else
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1846_; 
lean_dec_ref(v_arg_1770_);
lean_dec_ref(v_arg_1767_);
lean_dec_ref(v_e_1748_);
v_a_1839_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1841_ = v___x_1783_;
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1783_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1844_; 
if (v_isShared_1842_ == 0)
{
v___x_1844_ = v___x_1841_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_a_1839_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
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
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
lean_dec_ref(v_e_1748_);
v_a_1847_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___x_1763_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1763_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
v___jp_1757_:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1758_ = lean_box(0);
v___x_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
return v___x_1759_;
}
v___jp_1760_:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = lean_box(0);
v___x_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1761_);
return v___x_1762_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg___boxed(lean_object* v_e_1855_, lean_object* v_report_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_){
_start:
{
uint8_t v_report_boxed_1864_; lean_object* v_res_1865_; 
v_report_boxed_1864_ = lean_unbox(v_report_1856_);
v_res_1865_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1855_, v_report_boxed_1864_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_);
lean_dec(v_a_1862_);
lean_dec_ref(v_a_1861_);
lean_dec(v_a_1860_);
lean_dec_ref(v_a_1859_);
lean_dec(v_a_1858_);
lean_dec_ref(v_a_1857_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f(lean_object* v_e_1866_, uint8_t v_report_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1866_, v_report_1867_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___boxed(lean_object* v_e_1880_, lean_object* v_report_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_){
_start:
{
uint8_t v_report_boxed_1893_; lean_object* v_res_1894_; 
v_report_boxed_1893_ = lean_unbox(v_report_1881_);
v_res_1894_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f(v_e_1880_, v_report_boxed_1893_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_);
lean_dec(v_a_1891_);
lean_dec_ref(v_a_1890_);
lean_dec(v_a_1889_);
lean_dec_ref(v_a_1888_);
lean_dec(v_a_1887_);
lean_dec_ref(v_a_1886_);
lean_dec(v_a_1885_);
lean_dec_ref(v_a_1884_);
lean_dec(v_a_1883_);
lean_dec(v_a_1882_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(lean_object* v_e_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_){
_start:
{
uint8_t v___x_1903_; lean_object* v___x_1904_; 
v___x_1903_ = 0;
v___x_1904_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1895_, v___x_1903_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1918_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1907_ = v___x_1904_;
v_isShared_1908_ = v_isSharedCheck_1918_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1904_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1918_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
if (lean_obj_tag(v_a_1905_) == 0)
{
lean_object* v___x_1909_; lean_object* v___x_1911_; 
v___x_1909_ = lean_box(v___x_1903_);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 0, v___x_1909_);
v___x_1911_ = v___x_1907_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1909_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
else
{
uint8_t v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1916_; 
lean_dec_ref_known(v_a_1905_, 1);
v___x_1913_ = 1;
v___x_1914_ = lean_box(v___x_1913_);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 0, v___x_1914_);
v___x_1916_ = v___x_1907_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1914_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
v_a_1919_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1904_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1904_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1919_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg___boxed(lean_object* v_e_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(v_e_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
lean_dec(v_a_1933_);
lean_dec_ref(v_a_1932_);
lean_dec(v_a_1931_);
lean_dec_ref(v_a_1930_);
lean_dec(v_a_1929_);
lean_dec_ref(v_a_1928_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul(lean_object* v_e_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_){
_start:
{
lean_object* v___x_1948_; 
v___x_1948_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(v_e_1936_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___boxed(lean_object* v_e_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul(v_e_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_);
lean_dec(v_a_1959_);
lean_dec_ref(v_a_1958_);
lean_dec(v_a_1957_);
lean_dec_ref(v_a_1956_);
lean_dec(v_a_1955_);
lean_dec_ref(v_a_1954_);
lean_dec(v_a_1953_);
lean_dec_ref(v_a_1952_);
lean_dec(v_a_1951_);
lean_dec(v_a_1950_);
return v_res_1961_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0(void){
_start:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1962_ = lean_unsigned_to_nat(1u);
v___x_1963_ = lean_nat_to_int(v___x_1962_);
return v___x_1963_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2(void){
_start:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1965_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__1));
v___x_1966_ = l_Lean_stringToMessageData(v___x_1965_);
return v___x_1966_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4(void){
_start:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1968_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__3));
v___x_1969_ = l_Lean_stringToMessageData(v___x_1968_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(lean_object* v_e_1970_, lean_object* v_p_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_){
_start:
{
lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; uint8_t v___x_2013_; lean_object* v___x_2014_; 
v___x_2013_ = 1;
lean_inc_ref(v_e_1970_);
v___x_2014_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1970_, v___x_2013_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2015_);
lean_dec_ref_known(v___x_2014_, 1);
if (lean_obj_tag(v_a_2015_) == 1)
{
lean_object* v_val_2016_; lean_object* v_fst_2017_; lean_object* v_snd_2018_; lean_object* v___x_2019_; 
lean_dec_ref(v_e_1970_);
v_val_2016_ = lean_ctor_get(v_a_2015_, 0);
lean_inc(v_val_2016_);
lean_dec_ref_known(v_a_2015_, 1);
v_fst_2017_ = lean_ctor_get(v_val_2016_, 0);
lean_inc(v_fst_2017_);
v_snd_2018_ = lean_ctor_get(v_val_2016_, 1);
lean_inc(v_snd_2018_);
lean_dec(v_val_2016_);
lean_inc(v_a_1981_);
lean_inc_ref(v_a_1980_);
lean_inc(v_a_1979_);
lean_inc_ref(v_a_1978_);
lean_inc(v_a_1977_);
lean_inc_ref(v_a_1976_);
lean_inc(v_a_1975_);
lean_inc_ref(v_a_1974_);
lean_inc(v_a_1973_);
lean_inc(v_a_1972_);
v___x_2019_ = lean_grind_cutsat_mk_var(v_snd_2018_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2028_; 
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2022_ = v___x_2019_;
v_isShared_2023_ = v_isSharedCheck_2028_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_2019_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2028_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2024_; lean_object* v___x_2026_; 
v___x_2024_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2024_, 0, v_fst_2017_);
lean_ctor_set(v___x_2024_, 1, v_a_2020_);
lean_ctor_set(v___x_2024_, 2, v_p_1971_);
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 0, v___x_2024_);
v___x_2026_ = v___x_2022_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2024_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
lean_dec(v_fst_2017_);
lean_dec_ref(v_p_1971_);
v_a_2029_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_2019_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2019_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
else
{
lean_object* v___x_2037_; 
lean_dec(v_a_2015_);
lean_inc_ref(v_e_1970_);
v___x_2037_ = l_Lean_Meta_getIntValue_x3f(v_e_1970_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2079_; 
v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2040_ = v___x_2037_;
v_isShared_2041_ = v_isSharedCheck_2079_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2037_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2079_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
if (lean_obj_tag(v_a_2038_) == 1)
{
lean_object* v_val_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2078_; 
v_val_2042_ = lean_ctor_get(v_a_2038_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v_a_2038_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2044_ = v_a_2038_;
v_isShared_2045_ = v_isSharedCheck_2078_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_val_2042_);
lean_dec(v_a_2038_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2078_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
uint8_t v___x_2046_; 
v___x_2046_ = l_Int_Internal_Linear_Poly_isZero(v_p_1971_);
if (v___x_2046_ == 0)
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
lean_del_object(v___x_2044_);
lean_dec(v_val_2042_);
lean_del_object(v___x_2040_);
v___x_2047_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2);
lean_inc_ref(v_e_1970_);
v___x_2048_ = l_Lean_indentExpr(v_e_1970_);
v___x_2049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2047_);
lean_ctor_set(v___x_2049_, 1, v___x_2048_);
v___x_2050_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4);
v___x_2051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2049_);
lean_ctor_set(v___x_2051_, 1, v___x_2050_);
v___x_2052_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1976_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v_a_2053_; uint8_t v_verbose_2054_; 
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
lean_inc(v_a_2053_);
lean_dec_ref_known(v___x_2052_, 1);
v_verbose_2054_ = lean_ctor_get_uint8(v_a_2053_, 0);
lean_dec(v_a_2053_);
if (v_verbose_2054_ == 0)
{
lean_dec_ref_known(v___x_2051_, 2);
v___y_1984_ = v_a_1972_;
v___y_1985_ = v_a_1973_;
v___y_1986_ = v_a_1974_;
v___y_1987_ = v_a_1975_;
v___y_1988_ = v_a_1976_;
v___y_1989_ = v_a_1977_;
v___y_1990_ = v_a_1978_;
v___y_1991_ = v_a_1979_;
v___y_1992_ = v_a_1980_;
v___y_1993_ = v_a_1981_;
goto v___jp_1983_;
}
else
{
lean_object* v___x_2055_; 
v___x_2055_ = l_Lean_Meta_Sym_reportIssue(v___x_2051_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_dec_ref_known(v___x_2055_, 1);
v___y_1984_ = v_a_1972_;
v___y_1985_ = v_a_1973_;
v___y_1986_ = v_a_1974_;
v___y_1987_ = v_a_1975_;
v___y_1988_ = v_a_1976_;
v___y_1989_ = v_a_1977_;
v___y_1990_ = v_a_1978_;
v___y_1991_ = v_a_1979_;
v___y_1992_ = v_a_1980_;
v___y_1993_ = v_a_1981_;
goto v___jp_1983_;
}
else
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
lean_dec_ref(v_p_1971_);
lean_dec_ref(v_e_1970_);
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2058_ = v___x_2055_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2055_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2061_; 
if (v_isShared_2059_ == 0)
{
v___x_2061_ = v___x_2058_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2056_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
}
else
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2071_; 
lean_dec_ref_known(v___x_2051_, 2);
lean_dec_ref(v_p_1971_);
lean_dec_ref(v_e_1970_);
v_a_2064_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2066_ = v___x_2052_;
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_2052_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2069_; 
if (v_isShared_2067_ == 0)
{
v___x_2069_ = v___x_2066_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2064_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
else
{
lean_object* v___x_2073_; 
lean_dec_ref(v_p_1971_);
lean_dec_ref(v_e_1970_);
if (v_isShared_2045_ == 0)
{
lean_ctor_set_tag(v___x_2044_, 0);
v___x_2073_ = v___x_2044_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_val_2042_);
v___x_2073_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
lean_object* v___x_2075_; 
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 0, v___x_2073_);
v___x_2075_ = v___x_2040_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2073_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
}
}
else
{
lean_del_object(v___x_2040_);
lean_dec(v_a_2038_);
v___y_1984_ = v_a_1972_;
v___y_1985_ = v_a_1973_;
v___y_1986_ = v_a_1974_;
v___y_1987_ = v_a_1975_;
v___y_1988_ = v_a_1976_;
v___y_1989_ = v_a_1977_;
v___y_1990_ = v_a_1978_;
v___y_1991_ = v_a_1979_;
v___y_1992_ = v_a_1980_;
v___y_1993_ = v_a_1981_;
goto v___jp_1983_;
}
}
}
else
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2087_; 
lean_dec_ref(v_p_1971_);
lean_dec_ref(v_e_1970_);
v_a_2080_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2082_ = v___x_2037_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2037_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2085_; 
if (v_isShared_2083_ == 0)
{
v___x_2085_ = v___x_2082_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_a_2080_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
}
else
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2095_; 
lean_dec_ref(v_p_1971_);
lean_dec_ref(v_e_1970_);
v_a_2088_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2090_ = v___x_2014_;
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2014_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2093_; 
if (v_isShared_2091_ == 0)
{
v___x_2093_ = v___x_2090_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_a_2088_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
v___jp_1983_:
{
lean_object* v___x_1994_; 
lean_inc(v___y_1993_);
lean_inc_ref(v___y_1992_);
lean_inc(v___y_1991_);
lean_inc_ref(v___y_1990_);
lean_inc(v___y_1989_);
lean_inc_ref(v___y_1988_);
lean_inc(v___y_1987_);
lean_inc_ref(v___y_1986_);
lean_inc(v___y_1985_);
lean_inc(v___y_1984_);
v___x_1994_ = lean_grind_cutsat_mk_var(v_e_1970_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2004_; 
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1997_ = v___x_1994_;
v_isShared_1998_ = v_isSharedCheck_2004_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1994_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2004_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2002_; 
v___x_1999_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0);
v___x_2000_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2000_, 0, v___x_1999_);
lean_ctor_set(v___x_2000_, 1, v_a_1995_);
lean_ctor_set(v___x_2000_, 2, v_p_1971_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v___x_2000_);
v___x_2002_ = v___x_1997_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_2000_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
else
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2012_; 
lean_dec_ref(v_p_1971_);
v_a_2005_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2007_ = v___x_1994_;
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_1994_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2010_; 
if (v_isShared_2008_ == 0)
{
v___x_2010_ = v___x_2007_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_a_2005_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___boxed(lean_object* v_e_2096_, lean_object* v_p_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_e_2096_, v_p_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_);
lean_dec(v_a_2107_);
lean_dec_ref(v_a_2106_);
lean_dec(v_a_2105_);
lean_dec_ref(v_a_2104_);
lean_dec(v_a_2103_);
lean_dec_ref(v_a_2102_);
lean_dec(v_a_2101_);
lean_dec_ref(v_a_2100_);
lean_dec(v_a_2099_);
lean_dec(v_a_2098_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go(lean_object* v_e_2110_, lean_object* v_p_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_){
_start:
{
uint8_t v___x_2123_; lean_object* v___x_2124_; 
v___x_2123_ = 1;
lean_inc_ref(v_e_2110_);
v___x_2124_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_2110_, v___x_2123_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; 
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
lean_inc(v_a_2125_);
lean_dec_ref_known(v___x_2124_, 1);
if (lean_obj_tag(v_a_2125_) == 1)
{
lean_object* v_val_2126_; lean_object* v_fst_2127_; lean_object* v_snd_2128_; lean_object* v___x_2129_; 
lean_dec_ref(v_e_2110_);
v_val_2126_ = lean_ctor_get(v_a_2125_, 0);
lean_inc(v_val_2126_);
lean_dec_ref_known(v_a_2125_, 1);
v_fst_2127_ = lean_ctor_get(v_val_2126_, 0);
lean_inc(v_fst_2127_);
v_snd_2128_ = lean_ctor_get(v_val_2126_, 1);
lean_inc(v_snd_2128_);
lean_dec(v_val_2126_);
v___x_2129_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_snd_2128_, v_p_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2130_);
lean_dec_ref_known(v___x_2129_, 1);
v_e_2110_ = v_fst_2127_;
v_p_2111_ = v_a_2130_;
goto _start;
}
else
{
lean_dec(v_fst_2127_);
return v___x_2129_;
}
}
else
{
lean_object* v___x_2132_; 
lean_dec(v_a_2125_);
v___x_2132_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_e_2110_, v_p_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_);
return v___x_2132_;
}
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_dec_ref(v_p_2111_);
lean_dec_ref(v_e_2110_);
v_a_2133_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2124_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2124_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go___boxed(lean_object* v_e_2141_, lean_object* v_p_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_){
_start:
{
lean_object* v_res_2154_; 
v_res_2154_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go(v_e_2141_, v_p_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_);
lean_dec(v_a_2152_);
lean_dec_ref(v_a_2151_);
lean_dec(v_a_2150_);
lean_dec_ref(v_a_2149_);
lean_dec(v_a_2148_);
lean_dec_ref(v_a_2147_);
lean_dec(v_a_2146_);
lean_dec_ref(v_a_2145_);
lean_dec(v_a_2144_);
lean_dec(v_a_2143_);
return v_res_2154_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0(void){
_start:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2155_ = lean_unsigned_to_nat(0u);
v___x_2156_ = lean_nat_to_int(v___x_2155_);
return v___x_2156_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1(void){
_start:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2157_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0);
v___x_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2157_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly(lean_object* v_e_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_){
_start:
{
uint8_t v___x_2171_; lean_object* v___x_2172_; 
v___x_2171_ = 1;
lean_inc_ref(v_e_2159_);
v___x_2172_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_2159_, v___x_2171_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v_a_2173_; 
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
lean_inc(v_a_2173_);
lean_dec_ref_known(v___x_2172_, 1);
if (lean_obj_tag(v_a_2173_) == 1)
{
lean_object* v_val_2174_; lean_object* v_fst_2175_; lean_object* v_snd_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
lean_dec_ref(v_e_2159_);
v_val_2174_ = lean_ctor_get(v_a_2173_, 0);
lean_inc(v_val_2174_);
lean_dec_ref_known(v_a_2173_, 1);
v_fst_2175_ = lean_ctor_get(v_val_2174_, 0);
lean_inc(v_fst_2175_);
v_snd_2176_ = lean_ctor_get(v_val_2174_, 1);
lean_inc(v_snd_2176_);
lean_dec(v_val_2174_);
v___x_2177_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1);
v___x_2178_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_snd_2176_, v___x_2177_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_a_2179_; lean_object* v___x_2180_; 
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_a_2179_);
lean_dec_ref_known(v___x_2178_, 1);
v___x_2180_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go(v_fst_2175_, v_a_2179_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_);
return v___x_2180_;
}
else
{
lean_dec(v_fst_2175_);
return v___x_2178_;
}
}
else
{
lean_object* v___x_2181_; lean_object* v___x_2182_; 
lean_dec(v_a_2173_);
v___x_2181_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1);
v___x_2182_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_e_2159_, v___x_2181_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_);
return v___x_2182_;
}
}
else
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2190_; 
lean_dec_ref(v_e_2159_);
v_a_2183_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2185_ = v___x_2172_;
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2172_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2188_; 
if (v_isShared_2186_ == 0)
{
v___x_2188_ = v___x_2185_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_a_2183_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly___boxed(lean_object* v_e_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_e_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_);
lean_dec(v_a_2201_);
lean_dec_ref(v_a_2200_);
lean_dec(v_a_2199_);
lean_dec_ref(v_a_2198_);
lean_dec(v_a_2197_);
lean_dec_ref(v_a_2196_);
lean_dec(v_a_2195_);
lean_dec_ref(v_a_2194_);
lean_dec(v_a_2193_);
lean_dec(v_a_2192_);
return v_res_2203_;
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
