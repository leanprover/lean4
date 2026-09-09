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
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg___closed__0;
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
lean_object* v___x_54_; 
v___x_54_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_48_, v_a_50_);
if (lean_obj_tag(v___x_54_) == 0)
{
lean_object* v_a_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_176_; 
v_a_55_ = lean_ctor_get(v___x_54_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_54_);
if (v_isSharedCheck_176_ == 0)
{
v___x_57_ = v___x_54_;
v_isShared_58_ = v_isSharedCheck_176_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_a_55_);
lean_dec(v___x_54_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_176_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v___x_65_; uint8_t v___x_66_; 
v___x_65_ = l_Lean_Expr_cleanupAnnotations(v_a_55_);
v___x_66_ = l_Lean_Expr_isApp(v___x_65_);
if (v___x_66_ == 0)
{
lean_dec_ref(v___x_65_);
goto v___jp_59_;
}
else
{
lean_object* v_arg_67_; lean_object* v___x_68_; uint8_t v___x_69_; 
v_arg_67_ = lean_ctor_get(v___x_65_, 1);
lean_inc_ref(v_arg_67_);
v___x_68_ = l_Lean_Expr_appFnCleanup___redArg(v___x_65_);
v___x_69_ = l_Lean_Expr_isApp(v___x_68_);
if (v___x_69_ == 0)
{
lean_dec_ref(v___x_68_);
lean_dec_ref(v_arg_67_);
goto v___jp_59_;
}
else
{
lean_object* v_arg_70_; lean_object* v___x_71_; uint8_t v___x_72_; 
v_arg_70_ = lean_ctor_get(v___x_68_, 1);
lean_inc_ref(v_arg_70_);
v___x_71_ = l_Lean_Expr_appFnCleanup___redArg(v___x_68_);
v___x_72_ = l_Lean_Expr_isApp(v___x_71_);
if (v___x_72_ == 0)
{
lean_dec_ref(v___x_71_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_67_);
goto v___jp_59_;
}
else
{
lean_object* v_arg_73_; lean_object* v___x_74_; uint8_t v___x_75_; 
v_arg_73_ = lean_ctor_get(v___x_71_, 1);
lean_inc_ref(v_arg_73_);
v___x_74_ = l_Lean_Expr_appFnCleanup___redArg(v___x_71_);
v___x_75_ = l_Lean_Expr_isApp(v___x_74_);
if (v___x_75_ == 0)
{
lean_dec_ref(v___x_74_);
lean_dec_ref(v_arg_73_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_67_);
goto v___jp_59_;
}
else
{
lean_object* v___x_76_; uint8_t v___x_77_; 
v___x_76_ = l_Lean_Expr_appFnCleanup___redArg(v___x_74_);
v___x_77_ = l_Lean_Expr_isApp(v___x_76_);
if (v___x_77_ == 0)
{
lean_dec_ref(v___x_76_);
lean_dec_ref(v_arg_73_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_67_);
goto v___jp_59_;
}
else
{
lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_78_ = l_Lean_Expr_appFnCleanup___redArg(v___x_76_);
v___x_79_ = l_Lean_Expr_isApp(v___x_78_);
if (v___x_79_ == 0)
{
lean_dec_ref(v___x_78_);
lean_dec_ref(v_arg_73_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_67_);
goto v___jp_59_;
}
else
{
lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_80_ = l_Lean_Expr_appFnCleanup___redArg(v___x_78_);
v___x_81_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__2));
v___x_82_ = l_Lean_Expr_isConstOf(v___x_80_, v___x_81_);
if (v___x_82_ == 0)
{
lean_object* v___x_83_; uint8_t v___x_84_; 
lean_dec_ref(v_arg_70_);
v___x_83_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__5));
v___x_84_ = l_Lean_Expr_isConstOf(v___x_80_, v___x_83_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_85_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__8));
v___x_86_ = l_Lean_Expr_isConstOf(v___x_80_, v___x_85_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; uint8_t v___x_88_; 
lean_dec_ref(v_arg_67_);
v___x_87_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11));
v___x_88_ = l_Lean_Expr_isConstOf(v___x_80_, v___x_87_);
lean_dec_ref(v___x_80_);
if (v___x_88_ == 0)
{
lean_dec_ref(v_arg_73_);
goto v___jp_59_;
}
else
{
lean_object* v___x_89_; 
lean_del_object(v___x_57_);
v___x_89_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_73_, v_a_50_);
return v___x_89_;
}
}
else
{
lean_object* v___x_90_; 
lean_dec_ref(v___x_80_);
lean_del_object(v___x_57_);
v___x_90_ = l_Lean_Meta_getIntValue_x3f(v_arg_67_, v_a_49_, v_a_50_, v_a_51_, v_a_52_);
if (lean_obj_tag(v___x_90_) == 0)
{
lean_object* v_a_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_102_; 
v_a_91_ = lean_ctor_get(v___x_90_, 0);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_90_);
if (v_isSharedCheck_102_ == 0)
{
v___x_93_ = v___x_90_;
v_isShared_94_ = v_isSharedCheck_102_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_a_91_);
lean_dec(v___x_90_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_102_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
uint8_t v___y_96_; 
if (lean_obj_tag(v_a_91_) == 0)
{
v___y_96_ = v___x_86_;
goto v___jp_95_;
}
else
{
lean_dec_ref_known(v_a_91_, 1);
v___y_96_ = v___x_84_;
goto v___jp_95_;
}
v___jp_95_:
{
if (v___y_96_ == 0)
{
lean_object* v___x_97_; lean_object* v___x_99_; 
lean_dec_ref(v_arg_73_);
v___x_97_ = lean_box(v___y_96_);
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 0, v___x_97_);
v___x_99_ = v___x_93_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v___x_97_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
else
{
lean_object* v___x_101_; 
lean_del_object(v___x_93_);
v___x_101_ = l_Lean_Meta_Structural_isInstHDivInt___redArg(v_arg_73_, v_a_50_);
return v___x_101_;
}
}
}
}
else
{
lean_object* v_a_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_110_; 
lean_dec_ref(v_arg_73_);
v_a_103_ = lean_ctor_get(v___x_90_, 0);
v_isSharedCheck_110_ = !lean_is_exclusive(v___x_90_);
if (v_isSharedCheck_110_ == 0)
{
v___x_105_ = v___x_90_;
v_isShared_106_ = v_isSharedCheck_110_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_a_103_);
lean_dec(v___x_90_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_110_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_108_; 
if (v_isShared_106_ == 0)
{
v___x_108_ = v___x_105_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v_a_103_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
return v___x_108_;
}
}
}
}
}
else
{
lean_object* v___x_111_; 
lean_dec_ref(v___x_80_);
lean_del_object(v___x_57_);
v___x_111_ = l_Lean_Meta_getIntValue_x3f(v_arg_67_, v_a_49_, v_a_50_, v_a_51_, v_a_52_);
if (lean_obj_tag(v___x_111_) == 0)
{
lean_object* v_a_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_123_; 
v_a_112_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_123_ == 0)
{
v___x_114_ = v___x_111_;
v_isShared_115_ = v_isSharedCheck_123_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_a_112_);
lean_dec(v___x_111_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_123_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
uint8_t v___y_117_; 
if (lean_obj_tag(v_a_112_) == 0)
{
v___y_117_ = v___x_84_;
goto v___jp_116_;
}
else
{
lean_dec_ref_known(v_a_112_, 1);
v___y_117_ = v___x_82_;
goto v___jp_116_;
}
v___jp_116_:
{
if (v___y_117_ == 0)
{
lean_object* v___x_118_; lean_object* v___x_120_; 
lean_dec_ref(v_arg_73_);
v___x_118_ = lean_box(v___y_117_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 0, v___x_118_);
v___x_120_ = v___x_114_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v___x_118_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
else
{
lean_object* v___x_122_; 
lean_del_object(v___x_114_);
v___x_122_ = l_Lean_Meta_Structural_isInstHModInt___redArg(v_arg_73_, v_a_50_);
return v___x_122_;
}
}
}
}
else
{
lean_object* v_a_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_131_; 
lean_dec_ref(v_arg_73_);
v_a_124_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_131_ == 0)
{
v___x_126_ = v___x_111_;
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_a_124_);
lean_dec(v___x_111_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_129_; 
if (v_isShared_127_ == 0)
{
v___x_129_ = v___x_126_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_a_124_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
}
else
{
lean_object* v___x_132_; 
lean_dec_ref(v___x_80_);
lean_del_object(v___x_57_);
v___x_132_ = l_Lean_Meta_Structural_isInstHPowInt___redArg(v_arg_73_, v_a_50_);
if (lean_obj_tag(v___x_132_) == 0)
{
lean_object* v_a_133_; uint8_t v___x_134_; 
v_a_133_ = lean_ctor_get(v___x_132_, 0);
lean_inc(v_a_133_);
v___x_134_ = lean_unbox(v_a_133_);
if (v___x_134_ == 0)
{
lean_dec(v_a_133_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_67_);
return v___x_132_;
}
else
{
lean_object* v___x_135_; 
lean_dec_ref_known(v___x_132_, 1);
v___x_135_ = l_Lean_Meta_getIntValue_x3f(v_arg_70_, v_a_49_, v_a_50_, v_a_51_, v_a_52_);
if (lean_obj_tag(v___x_135_) == 0)
{
lean_object* v_a_136_; lean_object* v___x_137_; 
v_a_136_ = lean_ctor_get(v___x_135_, 0);
lean_inc(v_a_136_);
lean_dec_ref_known(v___x_135_, 1);
v___x_137_ = l_Lean_Meta_getIntValue_x3f(v_arg_67_, v_a_49_, v_a_50_, v_a_51_, v_a_52_);
if (lean_obj_tag(v___x_137_) == 0)
{
if (lean_obj_tag(v_a_136_) == 0)
{
lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_145_; 
lean_dec(v_a_133_);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_145_ == 0)
{
lean_object* v_unused_146_; 
v_unused_146_ = lean_ctor_get(v___x_137_, 0);
lean_dec(v_unused_146_);
v___x_139_ = v___x_137_;
v_isShared_140_ = v_isSharedCheck_145_;
goto v_resetjp_138_;
}
else
{
lean_dec(v___x_137_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_145_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_141_; lean_object* v___x_143_; 
v___x_141_ = lean_box(v___x_82_);
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 0, v___x_141_);
v___x_143_ = v___x_139_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v___x_141_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
else
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_159_; 
lean_dec_ref_known(v_a_136_, 1);
v_a_147_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_159_ == 0)
{
v___x_149_ = v___x_137_;
v_isShared_150_ = v_isSharedCheck_159_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_137_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_159_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
if (lean_obj_tag(v_a_147_) == 0)
{
lean_object* v___x_152_; 
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 0, v_a_133_);
v___x_152_ = v___x_149_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_a_133_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
else
{
uint8_t v___x_154_; lean_object* v___x_155_; lean_object* v___x_157_; 
lean_dec_ref_known(v_a_147_, 1);
lean_dec(v_a_133_);
v___x_154_ = 0;
v___x_155_ = lean_box(v___x_154_);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 0, v___x_155_);
v___x_157_ = v___x_149_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_155_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
}
else
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_167_; 
lean_dec(v_a_136_);
lean_dec(v_a_133_);
v_a_160_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_167_ == 0)
{
v___x_162_ = v___x_137_;
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v___x_137_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_165_; 
if (v_isShared_163_ == 0)
{
v___x_165_ = v___x_162_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_a_160_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
}
else
{
lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_175_; 
lean_dec(v_a_133_);
lean_dec_ref(v_arg_67_);
v_a_168_ = lean_ctor_get(v___x_135_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_175_ == 0)
{
v___x_170_ = v___x_135_;
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_dec(v___x_135_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_173_; 
if (v_isShared_171_ == 0)
{
v___x_173_ = v___x_170_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_a_168_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
}
else
{
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_67_);
return v___x_132_;
}
}
}
}
}
}
}
}
v___jp_59_:
{
uint8_t v___x_60_; lean_object* v___x_61_; lean_object* v___x_63_; 
v___x_60_ = 0;
v___x_61_ = lean_box(v___x_60_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 0, v___x_61_);
v___x_63_ = v___x_57_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v___x_61_);
v___x_63_ = v_reuseFailAlloc_64_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
return v___x_63_;
}
}
}
}
else
{
lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_184_; 
v_a_177_ = lean_ctor_get(v___x_54_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_54_);
if (v_isSharedCheck_184_ == 0)
{
v___x_179_ = v___x_54_;
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_dec(v___x_54_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_182_; 
if (v_isShared_180_ == 0)
{
v___x_182_ = v___x_179_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_a_177_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___boxed(lean_object* v_e_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm(v_e_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_);
lean_dec(v_a_189_);
lean_dec_ref(v_a_188_);
lean_dec(v_a_187_);
lean_dec_ref(v_a_186_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_x_192_, lean_object* v_x_193_, lean_object* v_x_194_, lean_object* v_x_195_){
_start:
{
lean_object* v_ks_196_; lean_object* v_vs_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_221_; 
v_ks_196_ = lean_ctor_get(v_x_192_, 0);
v_vs_197_ = lean_ctor_get(v_x_192_, 1);
v_isSharedCheck_221_ = !lean_is_exclusive(v_x_192_);
if (v_isSharedCheck_221_ == 0)
{
v___x_199_ = v_x_192_;
v_isShared_200_ = v_isSharedCheck_221_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_vs_197_);
lean_inc(v_ks_196_);
lean_dec(v_x_192_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_221_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_201_; uint8_t v___x_202_; 
v___x_201_ = lean_array_get_size(v_ks_196_);
v___x_202_ = lean_nat_dec_lt(v_x_193_, v___x_201_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_206_; 
lean_dec(v_x_193_);
v___x_203_ = lean_array_push(v_ks_196_, v_x_194_);
v___x_204_ = lean_array_push(v_vs_197_, v_x_195_);
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 1, v___x_204_);
lean_ctor_set(v___x_199_, 0, v___x_203_);
v___x_206_ = v___x_199_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v___x_203_);
lean_ctor_set(v_reuseFailAlloc_207_, 1, v___x_204_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
else
{
lean_object* v_k_x27_208_; uint8_t v___x_209_; 
v_k_x27_208_ = lean_array_fget_borrowed(v_ks_196_, v_x_193_);
v___x_209_ = lean_nat_dec_eq(v_x_194_, v_k_x27_208_);
if (v___x_209_ == 0)
{
lean_object* v___x_211_; 
if (v_isShared_200_ == 0)
{
v___x_211_ = v___x_199_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_ks_196_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v_vs_197_);
v___x_211_ = v_reuseFailAlloc_215_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = lean_unsigned_to_nat(1u);
v___x_213_ = lean_nat_add(v_x_193_, v___x_212_);
lean_dec(v_x_193_);
v_x_192_ = v___x_211_;
v_x_193_ = v___x_213_;
goto _start;
}
}
else
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_219_; 
v___x_216_ = lean_array_fset(v_ks_196_, v_x_193_, v_x_194_);
v___x_217_ = lean_array_fset(v_vs_197_, v_x_193_, v_x_195_);
lean_dec(v_x_193_);
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 1, v___x_217_);
lean_ctor_set(v___x_199_, 0, v___x_216_);
v___x_219_ = v___x_199_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v___x_216_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v___x_217_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1___redArg(lean_object* v_n_222_, lean_object* v_k_223_, lean_object* v_v_224_){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = lean_unsigned_to_nat(0u);
v___x_226_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__4___redArg(v_n_222_, v___x_225_, v_k_223_, v_v_224_);
return v___x_226_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(lean_object* v_x_228_, size_t v_x_229_, size_t v_x_230_, lean_object* v_x_231_, lean_object* v_x_232_){
_start:
{
if (lean_obj_tag(v_x_228_) == 0)
{
lean_object* v_es_233_; size_t v___x_234_; size_t v___x_235_; lean_object* v_j_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v_es_233_ = lean_ctor_get(v_x_228_, 0);
v___x_234_ = ((size_t)31ULL);
v___x_235_ = lean_usize_land(v_x_229_, v___x_234_);
v_j_236_ = lean_usize_to_nat(v___x_235_);
v___x_237_ = lean_array_get_size(v_es_233_);
v___x_238_ = lean_nat_dec_lt(v_j_236_, v___x_237_);
if (v___x_238_ == 0)
{
lean_dec(v_j_236_);
lean_dec(v_x_232_);
lean_dec(v_x_231_);
return v_x_228_;
}
else
{
lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_277_; 
lean_inc_ref(v_es_233_);
v_isSharedCheck_277_ = !lean_is_exclusive(v_x_228_);
if (v_isSharedCheck_277_ == 0)
{
lean_object* v_unused_278_; 
v_unused_278_ = lean_ctor_get(v_x_228_, 0);
lean_dec(v_unused_278_);
v___x_240_ = v_x_228_;
v_isShared_241_ = v_isSharedCheck_277_;
goto v_resetjp_239_;
}
else
{
lean_dec(v_x_228_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_277_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v_v_242_; lean_object* v___x_243_; lean_object* v_xs_x27_244_; lean_object* v___y_246_; 
v_v_242_ = lean_array_fget(v_es_233_, v_j_236_);
v___x_243_ = lean_box(0);
v_xs_x27_244_ = lean_array_fset(v_es_233_, v_j_236_, v___x_243_);
switch(lean_obj_tag(v_v_242_))
{
case 0:
{
lean_object* v_key_251_; lean_object* v_val_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_262_; 
v_key_251_ = lean_ctor_get(v_v_242_, 0);
v_val_252_ = lean_ctor_get(v_v_242_, 1);
v_isSharedCheck_262_ = !lean_is_exclusive(v_v_242_);
if (v_isSharedCheck_262_ == 0)
{
v___x_254_ = v_v_242_;
v_isShared_255_ = v_isSharedCheck_262_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_val_252_);
lean_inc(v_key_251_);
lean_dec(v_v_242_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_262_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
uint8_t v___x_256_; 
v___x_256_ = lean_nat_dec_eq(v_x_231_, v_key_251_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; 
lean_del_object(v___x_254_);
v___x_257_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_251_, v_val_252_, v_x_231_, v_x_232_);
v___x_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
v___y_246_ = v___x_258_;
goto v___jp_245_;
}
else
{
lean_object* v___x_260_; 
lean_dec(v_val_252_);
lean_dec(v_key_251_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 1, v_x_232_);
lean_ctor_set(v___x_254_, 0, v_x_231_);
v___x_260_ = v___x_254_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_x_231_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_x_232_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
v___y_246_ = v___x_260_;
goto v___jp_245_;
}
}
}
}
case 1:
{
lean_object* v_node_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_275_; 
v_node_263_ = lean_ctor_get(v_v_242_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v_v_242_);
if (v_isSharedCheck_275_ == 0)
{
v___x_265_ = v_v_242_;
v_isShared_266_ = v_isSharedCheck_275_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_node_263_);
lean_dec(v_v_242_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_275_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
size_t v___x_267_; size_t v___x_268_; size_t v___x_269_; size_t v___x_270_; lean_object* v___x_271_; lean_object* v___x_273_; 
v___x_267_ = ((size_t)5ULL);
v___x_268_ = lean_usize_shift_right(v_x_229_, v___x_267_);
v___x_269_ = ((size_t)1ULL);
v___x_270_ = lean_usize_add(v_x_230_, v___x_269_);
v___x_271_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_node_263_, v___x_268_, v___x_270_, v_x_231_, v_x_232_);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 0, v___x_271_);
v___x_273_ = v___x_265_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_271_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
v___y_246_ = v___x_273_;
goto v___jp_245_;
}
}
}
default: 
{
lean_object* v___x_276_; 
v___x_276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_276_, 0, v_x_231_);
lean_ctor_set(v___x_276_, 1, v_x_232_);
v___y_246_ = v___x_276_;
goto v___jp_245_;
}
}
v___jp_245_:
{
lean_object* v___x_247_; lean_object* v___x_249_; 
v___x_247_ = lean_array_fset(v_xs_x27_244_, v_j_236_, v___y_246_);
lean_dec(v_j_236_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v___x_247_);
v___x_249_ = v___x_240_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_247_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
}
else
{
lean_object* v_ks_279_; lean_object* v_vs_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_298_; 
v_ks_279_ = lean_ctor_get(v_x_228_, 0);
v_vs_280_ = lean_ctor_get(v_x_228_, 1);
v_isSharedCheck_298_ = !lean_is_exclusive(v_x_228_);
if (v_isSharedCheck_298_ == 0)
{
v___x_282_ = v_x_228_;
v_isShared_283_ = v_isSharedCheck_298_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_vs_280_);
lean_inc(v_ks_279_);
lean_dec(v_x_228_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_298_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_285_; 
if (v_isShared_283_ == 0)
{
v___x_285_ = v___x_282_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_ks_279_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v_vs_280_);
v___x_285_ = v_reuseFailAlloc_297_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
lean_object* v_newNode_286_; size_t v___x_287_; uint8_t v___x_288_; 
v_newNode_286_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1___redArg(v___x_285_, v_x_231_, v_x_232_);
v___x_287_ = ((size_t)7ULL);
v___x_288_ = lean_usize_dec_le(v___x_287_, v_x_230_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_289_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_286_);
v___x_290_ = lean_unsigned_to_nat(4u);
v___x_291_ = lean_nat_dec_lt(v___x_289_, v___x_290_);
lean_dec(v___x_289_);
if (v___x_291_ == 0)
{
lean_object* v_ks_292_; lean_object* v_vs_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v_ks_292_ = lean_ctor_get(v_newNode_286_, 0);
lean_inc_ref(v_ks_292_);
v_vs_293_ = lean_ctor_get(v_newNode_286_, 1);
lean_inc_ref(v_vs_293_);
lean_dec_ref(v_newNode_286_);
v___x_294_ = lean_unsigned_to_nat(0u);
v___x_295_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0);
v___x_296_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg(v_x_230_, v_ks_292_, v_vs_293_, v___x_294_, v___x_295_);
lean_dec_ref(v_vs_293_);
lean_dec_ref(v_ks_292_);
return v___x_296_;
}
else
{
return v_newNode_286_;
}
}
else
{
return v_newNode_286_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg(size_t v_depth_299_, lean_object* v_keys_300_, lean_object* v_vals_301_, lean_object* v_i_302_, lean_object* v_entries_303_){
_start:
{
lean_object* v___x_304_; uint8_t v___x_305_; 
v___x_304_ = lean_array_get_size(v_keys_300_);
v___x_305_ = lean_nat_dec_lt(v_i_302_, v___x_304_);
if (v___x_305_ == 0)
{
lean_dec(v_i_302_);
return v_entries_303_;
}
else
{
lean_object* v_k_306_; lean_object* v_v_307_; uint64_t v___x_308_; size_t v_h_309_; size_t v___x_310_; lean_object* v___x_311_; size_t v___x_312_; size_t v___x_313_; size_t v___x_314_; size_t v_h_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v_k_306_ = lean_array_fget_borrowed(v_keys_300_, v_i_302_);
v_v_307_ = lean_array_fget_borrowed(v_vals_301_, v_i_302_);
v___x_308_ = lean_uint64_of_nat(v_k_306_);
v_h_309_ = lean_uint64_to_usize(v___x_308_);
v___x_310_ = ((size_t)5ULL);
v___x_311_ = lean_unsigned_to_nat(1u);
v___x_312_ = ((size_t)1ULL);
v___x_313_ = lean_usize_sub(v_depth_299_, v___x_312_);
v___x_314_ = lean_usize_mul(v___x_310_, v___x_313_);
v_h_315_ = lean_usize_shift_right(v_h_309_, v___x_314_);
v___x_316_ = lean_nat_add(v_i_302_, v___x_311_);
lean_dec(v_i_302_);
lean_inc(v_v_307_);
lean_inc(v_k_306_);
v___x_317_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_entries_303_, v_h_315_, v_depth_299_, v_k_306_, v_v_307_);
v_i_302_ = v___x_316_;
v_entries_303_ = v___x_317_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_319_, lean_object* v_keys_320_, lean_object* v_vals_321_, lean_object* v_i_322_, lean_object* v_entries_323_){
_start:
{
size_t v_depth_boxed_324_; lean_object* v_res_325_; 
v_depth_boxed_324_ = lean_unbox_usize(v_depth_319_);
lean_dec(v_depth_319_);
v_res_325_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg(v_depth_boxed_324_, v_keys_320_, v_vals_321_, v_i_322_, v_entries_323_);
lean_dec_ref(v_vals_321_);
lean_dec_ref(v_keys_320_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___boxed(lean_object* v_x_326_, lean_object* v_x_327_, lean_object* v_x_328_, lean_object* v_x_329_, lean_object* v_x_330_){
_start:
{
size_t v_x_8001__boxed_331_; size_t v_x_8002__boxed_332_; lean_object* v_res_333_; 
v_x_8001__boxed_331_ = lean_unbox_usize(v_x_327_);
lean_dec(v_x_327_);
v_x_8002__boxed_332_ = lean_unbox_usize(v_x_328_);
lean_dec(v_x_328_);
v_res_333_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_x_326_, v_x_8001__boxed_331_, v_x_8002__boxed_332_, v_x_329_, v_x_330_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0___redArg(lean_object* v_x_334_, lean_object* v_x_335_, lean_object* v_x_336_){
_start:
{
uint64_t v___x_337_; size_t v___x_338_; size_t v___x_339_; lean_object* v___x_340_; 
v___x_337_ = lean_uint64_of_nat(v_x_335_);
v___x_338_ = lean_uint64_to_usize(v___x_337_);
v___x_339_ = ((size_t)1ULL);
v___x_340_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_x_334_, v___x_338_, v___x_339_, v_x_335_, v_x_336_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___lam__0(lean_object* v_x_341_, lean_object* v___y_342_, lean_object* v_a_343_, lean_object* v_s_344_){
_start:
{
lean_object* v_vars_345_; lean_object* v_varMap_346_; lean_object* v_vars_x27_347_; lean_object* v_varMap_x27_348_; lean_object* v_natToIntMap_349_; lean_object* v_natDef_350_; lean_object* v_dvds_351_; lean_object* v_lowers_352_; lean_object* v_uppers_353_; lean_object* v_diseqs_354_; lean_object* v_elimEqs_355_; lean_object* v_elimStack_356_; lean_object* v_occurs_357_; lean_object* v_assignment_358_; lean_object* v_nextCnstrId_359_; uint8_t v_caseSplits_360_; lean_object* v_steps_361_; lean_object* v_conflict_x3f_362_; lean_object* v_diseqSplits_363_; lean_object* v_divMod_364_; uint8_t v_usedCommRing_365_; lean_object* v_nonlinearOccs_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_375_; 
v_vars_345_ = lean_ctor_get(v_s_344_, 0);
v_varMap_346_ = lean_ctor_get(v_s_344_, 1);
v_vars_x27_347_ = lean_ctor_get(v_s_344_, 2);
v_varMap_x27_348_ = lean_ctor_get(v_s_344_, 3);
v_natToIntMap_349_ = lean_ctor_get(v_s_344_, 4);
v_natDef_350_ = lean_ctor_get(v_s_344_, 5);
v_dvds_351_ = lean_ctor_get(v_s_344_, 6);
v_lowers_352_ = lean_ctor_get(v_s_344_, 7);
v_uppers_353_ = lean_ctor_get(v_s_344_, 8);
v_diseqs_354_ = lean_ctor_get(v_s_344_, 9);
v_elimEqs_355_ = lean_ctor_get(v_s_344_, 10);
v_elimStack_356_ = lean_ctor_get(v_s_344_, 11);
v_occurs_357_ = lean_ctor_get(v_s_344_, 12);
v_assignment_358_ = lean_ctor_get(v_s_344_, 13);
v_nextCnstrId_359_ = lean_ctor_get(v_s_344_, 14);
v_caseSplits_360_ = lean_ctor_get_uint8(v_s_344_, sizeof(void*)*20);
v_steps_361_ = lean_ctor_get(v_s_344_, 15);
v_conflict_x3f_362_ = lean_ctor_get(v_s_344_, 16);
v_diseqSplits_363_ = lean_ctor_get(v_s_344_, 17);
v_divMod_364_ = lean_ctor_get(v_s_344_, 18);
v_usedCommRing_365_ = lean_ctor_get_uint8(v_s_344_, sizeof(void*)*20 + 1);
v_nonlinearOccs_366_ = lean_ctor_get(v_s_344_, 19);
v_isSharedCheck_375_ = !lean_is_exclusive(v_s_344_);
if (v_isSharedCheck_375_ == 0)
{
v___x_368_ = v_s_344_;
v_isShared_369_ = v_isSharedCheck_375_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_nonlinearOccs_366_);
lean_inc(v_divMod_364_);
lean_inc(v_diseqSplits_363_);
lean_inc(v_conflict_x3f_362_);
lean_inc(v_steps_361_);
lean_inc(v_nextCnstrId_359_);
lean_inc(v_assignment_358_);
lean_inc(v_occurs_357_);
lean_inc(v_elimStack_356_);
lean_inc(v_elimEqs_355_);
lean_inc(v_diseqs_354_);
lean_inc(v_uppers_353_);
lean_inc(v_lowers_352_);
lean_inc(v_dvds_351_);
lean_inc(v_natDef_350_);
lean_inc(v_natToIntMap_349_);
lean_inc(v_varMap_x27_348_);
lean_inc(v_vars_x27_347_);
lean_inc(v_varMap_346_);
lean_inc(v_vars_345_);
lean_dec(v_s_344_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_375_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_373_; 
v___x_370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_370_, 0, v_x_341_);
lean_ctor_set(v___x_370_, 1, v___y_342_);
v___x_371_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0___redArg(v_nonlinearOccs_366_, v_a_343_, v___x_370_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 19, v___x_371_);
v___x_373_ = v___x_368_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 20, 2);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_vars_345_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v_varMap_346_);
lean_ctor_set(v_reuseFailAlloc_374_, 2, v_vars_x27_347_);
lean_ctor_set(v_reuseFailAlloc_374_, 3, v_varMap_x27_348_);
lean_ctor_set(v_reuseFailAlloc_374_, 4, v_natToIntMap_349_);
lean_ctor_set(v_reuseFailAlloc_374_, 5, v_natDef_350_);
lean_ctor_set(v_reuseFailAlloc_374_, 6, v_dvds_351_);
lean_ctor_set(v_reuseFailAlloc_374_, 7, v_lowers_352_);
lean_ctor_set(v_reuseFailAlloc_374_, 8, v_uppers_353_);
lean_ctor_set(v_reuseFailAlloc_374_, 9, v_diseqs_354_);
lean_ctor_set(v_reuseFailAlloc_374_, 10, v_elimEqs_355_);
lean_ctor_set(v_reuseFailAlloc_374_, 11, v_elimStack_356_);
lean_ctor_set(v_reuseFailAlloc_374_, 12, v_occurs_357_);
lean_ctor_set(v_reuseFailAlloc_374_, 13, v_assignment_358_);
lean_ctor_set(v_reuseFailAlloc_374_, 14, v_nextCnstrId_359_);
lean_ctor_set(v_reuseFailAlloc_374_, 15, v_steps_361_);
lean_ctor_set(v_reuseFailAlloc_374_, 16, v_conflict_x3f_362_);
lean_ctor_set(v_reuseFailAlloc_374_, 17, v_diseqSplits_363_);
lean_ctor_set(v_reuseFailAlloc_374_, 18, v_divMod_364_);
lean_ctor_set(v_reuseFailAlloc_374_, 19, v___x_371_);
lean_ctor_set_uint8(v_reuseFailAlloc_374_, sizeof(void*)*20, v_caseSplits_360_);
lean_ctor_set_uint8(v_reuseFailAlloc_374_, sizeof(void*)*20 + 1, v_usedCommRing_365_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1(lean_object* v_a_376_, lean_object* v_x_377_){
_start:
{
if (lean_obj_tag(v_x_377_) == 0)
{
uint8_t v___x_378_; 
v___x_378_ = 0;
return v___x_378_;
}
else
{
lean_object* v_head_379_; lean_object* v_tail_380_; uint8_t v___x_381_; 
v_head_379_ = lean_ctor_get(v_x_377_, 0);
v_tail_380_ = lean_ctor_get(v_x_377_, 1);
v___x_381_ = lean_nat_dec_eq(v_a_376_, v_head_379_);
if (v___x_381_ == 0)
{
v_x_377_ = v_tail_380_;
goto _start;
}
else
{
return v___x_381_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___boxed(lean_object* v_a_383_, lean_object* v_x_384_){
_start:
{
uint8_t v_res_385_; lean_object* v_r_386_; 
v_res_385_ = l_List_elem___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1(v_a_383_, v_x_384_);
lean_dec(v_x_384_);
lean_dec(v_a_383_);
v_r_386_ = lean_box(v_res_385_);
return v_r_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6___redArg(lean_object* v_keys_387_, lean_object* v_vals_388_, lean_object* v_i_389_, lean_object* v_k_390_){
_start:
{
lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_391_ = lean_array_get_size(v_keys_387_);
v___x_392_ = lean_nat_dec_lt(v_i_389_, v___x_391_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; 
lean_dec(v_i_389_);
v___x_393_ = lean_box(0);
return v___x_393_;
}
else
{
lean_object* v_k_x27_394_; uint8_t v___x_395_; 
v_k_x27_394_ = lean_array_fget_borrowed(v_keys_387_, v_i_389_);
v___x_395_ = lean_nat_dec_eq(v_k_390_, v_k_x27_394_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = lean_unsigned_to_nat(1u);
v___x_397_ = lean_nat_add(v_i_389_, v___x_396_);
lean_dec(v_i_389_);
v_i_389_ = v___x_397_;
goto _start;
}
else
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = lean_array_fget_borrowed(v_vals_388_, v_i_389_);
lean_dec(v_i_389_);
lean_inc(v___x_399_);
v___x_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
return v___x_400_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_keys_401_, lean_object* v_vals_402_, lean_object* v_i_403_, lean_object* v_k_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6___redArg(v_keys_401_, v_vals_402_, v_i_403_, v_k_404_);
lean_dec(v_k_404_);
lean_dec_ref(v_vals_402_);
lean_dec_ref(v_keys_401_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___redArg(lean_object* v_x_406_, size_t v_x_407_, lean_object* v_x_408_){
_start:
{
if (lean_obj_tag(v_x_406_) == 0)
{
lean_object* v_es_409_; lean_object* v___x_410_; size_t v___x_411_; size_t v___x_412_; lean_object* v_j_413_; lean_object* v___x_414_; 
v_es_409_ = lean_ctor_get(v_x_406_, 0);
v___x_410_ = lean_box(2);
v___x_411_ = ((size_t)31ULL);
v___x_412_ = lean_usize_land(v_x_407_, v___x_411_);
v_j_413_ = lean_usize_to_nat(v___x_412_);
v___x_414_ = lean_array_get_borrowed(v___x_410_, v_es_409_, v_j_413_);
lean_dec(v_j_413_);
switch(lean_obj_tag(v___x_414_))
{
case 0:
{
lean_object* v_key_415_; lean_object* v_val_416_; uint8_t v___x_417_; 
v_key_415_ = lean_ctor_get(v___x_414_, 0);
v_val_416_ = lean_ctor_get(v___x_414_, 1);
v___x_417_ = lean_nat_dec_eq(v_x_408_, v_key_415_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; 
v___x_418_ = lean_box(0);
return v___x_418_;
}
else
{
lean_object* v___x_419_; 
lean_inc(v_val_416_);
v___x_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_419_, 0, v_val_416_);
return v___x_419_;
}
}
case 1:
{
lean_object* v_node_420_; size_t v___x_421_; size_t v___x_422_; 
v_node_420_ = lean_ctor_get(v___x_414_, 0);
v___x_421_ = ((size_t)5ULL);
v___x_422_ = lean_usize_shift_right(v_x_407_, v___x_421_);
v_x_406_ = v_node_420_;
v_x_407_ = v___x_422_;
goto _start;
}
default: 
{
lean_object* v___x_424_; 
v___x_424_ = lean_box(0);
return v___x_424_;
}
}
}
else
{
lean_object* v_ks_425_; lean_object* v_vs_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v_ks_425_ = lean_ctor_get(v_x_406_, 0);
v_vs_426_ = lean_ctor_get(v_x_406_, 1);
v___x_427_ = lean_unsigned_to_nat(0u);
v___x_428_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6___redArg(v_ks_425_, v_vs_426_, v___x_427_, v_x_408_);
return v___x_428_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___redArg___boxed(lean_object* v_x_429_, lean_object* v_x_430_, lean_object* v_x_431_){
_start:
{
size_t v_x_8220__boxed_432_; lean_object* v_res_433_; 
v_x_8220__boxed_432_ = lean_unbox_usize(v_x_430_);
lean_dec(v_x_430_);
v_res_433_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___redArg(v_x_429_, v_x_8220__boxed_432_, v_x_431_);
lean_dec(v_x_431_);
lean_dec_ref(v_x_429_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2___redArg(lean_object* v_x_434_, lean_object* v_x_435_){
_start:
{
uint64_t v___x_436_; size_t v___x_437_; lean_object* v___x_438_; 
v___x_436_ = lean_uint64_of_nat(v_x_435_);
v___x_437_ = lean_uint64_to_usize(v___x_436_);
v___x_438_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___redArg(v_x_434_, v___x_437_, v_x_435_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2___redArg___boxed(lean_object* v_x_439_, lean_object* v_x_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2___redArg(v_x_439_, v_x_440_);
lean_dec(v_x_440_);
lean_dec_ref(v_x_439_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(lean_object* v_arg_442_, lean_object* v_x_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_){
_start:
{
lean_object* v___x_455_; 
lean_inc(v_a_453_);
lean_inc_ref(v_a_452_);
lean_inc(v_a_451_);
lean_inc_ref(v_a_450_);
lean_inc(v_a_449_);
lean_inc_ref(v_a_448_);
lean_inc(v_a_447_);
lean_inc_ref(v_a_446_);
lean_inc(v_a_445_);
lean_inc(v_a_444_);
v___x_455_ = lean_grind_cutsat_mk_var(v_arg_442_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_525_; 
v_a_456_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_525_ == 0)
{
v___x_458_ = v___x_455_;
v_isShared_459_ = v_isSharedCheck_525_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_455_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_525_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___y_461_; lean_object* v___y_462_; lean_object* v___y_472_; lean_object* v___y_473_; lean_object* v___x_488_; 
v___x_488_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_444_, v_a_452_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; lean_object* v___y_491_; lean_object* v_elimEqs_511_; lean_object* v_size_512_; lean_object* v___x_513_; uint8_t v___x_514_; 
v_a_489_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_a_489_);
lean_dec_ref_known(v___x_488_, 1);
v_elimEqs_511_ = lean_ctor_get(v_a_489_, 10);
lean_inc_ref(v_elimEqs_511_);
lean_dec(v_a_489_);
v_size_512_ = lean_ctor_get(v_elimEqs_511_, 2);
v___x_513_ = lean_box(0);
v___x_514_ = lean_nat_dec_lt(v_a_456_, v_size_512_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; 
lean_dec_ref(v_elimEqs_511_);
v___x_515_ = l_outOfBounds___redArg(v___x_513_);
v___y_491_ = v___x_515_;
goto v___jp_490_;
}
else
{
lean_object* v___x_516_; 
v___x_516_ = l_Lean_PersistentArray_get_x21___redArg(v___x_513_, v_elimEqs_511_, v_a_456_);
lean_dec_ref(v_elimEqs_511_);
v___y_491_ = v___x_516_;
goto v___jp_490_;
}
v___jp_490_:
{
if (lean_obj_tag(v___y_491_) == 0)
{
v___y_472_ = v_a_444_;
v___y_473_ = v_a_452_;
goto v___jp_471_;
}
else
{
lean_object* v___x_492_; 
lean_dec_ref_known(v___y_491_, 1);
lean_inc(v_a_453_);
lean_inc_ref(v_a_452_);
lean_inc(v_a_451_);
lean_inc_ref(v_a_450_);
lean_inc(v_a_449_);
lean_inc_ref(v_a_448_);
lean_inc(v_a_447_);
lean_inc_ref(v_a_446_);
lean_inc(v_a_445_);
lean_inc(v_a_444_);
lean_inc(v_x_443_);
lean_inc(v_a_456_);
v___x_492_ = lean_cutsat_propagate_nonlinear(v_a_456_, v_x_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_);
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
v___y_472_ = v_a_444_;
v___y_473_ = v_a_452_;
goto v___jp_471_;
}
else
{
lean_object* v___x_498_; lean_object* v___x_500_; 
lean_del_object(v___x_458_);
lean_dec(v_a_456_);
lean_dec(v_x_443_);
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
lean_dec(v_x_443_);
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
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_524_; 
lean_del_object(v___x_458_);
lean_dec(v_a_456_);
lean_dec(v_x_443_);
v_a_517_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_524_ == 0)
{
v___x_519_ = v___x_488_;
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_488_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_a_517_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
v___jp_460_:
{
uint8_t v___x_463_; 
v___x_463_ = l_List_elem___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1(v_x_443_, v___y_462_);
if (v___x_463_ == 0)
{
lean_object* v___f_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
lean_del_object(v___x_458_);
v___f_464_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___lam__0), 4, 3);
lean_closure_set(v___f_464_, 0, v_x_443_);
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
lean_dec(v_x_443_);
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
v_nonlinearOccs_476_ = lean_ctor_get(v_a_475_, 19);
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
lean_dec(v_x_443_);
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
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_533_; 
lean_dec(v_x_443_);
v_a_526_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v___x_455_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_455_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_531_; 
if (v_isShared_529_ == 0)
{
v___x_531_ = v___x_528_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_a_526_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0(lean_object* v_00_u03b2_561_, lean_object* v_x_562_, size_t v_x_563_, size_t v_x_564_, lean_object* v_x_565_, lean_object* v_x_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_x_562_, v_x_563_, v_x_564_, v_x_565_, v_x_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___boxed(lean_object* v_00_u03b2_568_, lean_object* v_x_569_, lean_object* v_x_570_, lean_object* v_x_571_, lean_object* v_x_572_, lean_object* v_x_573_){
_start:
{
size_t v_x_8451__boxed_574_; size_t v_x_8452__boxed_575_; lean_object* v_res_576_; 
v_x_8451__boxed_574_ = lean_unbox_usize(v_x_570_);
lean_dec(v_x_570_);
v_x_8452__boxed_575_ = lean_unbox_usize(v_x_571_);
lean_dec(v_x_571_);
v_res_576_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0(v_00_u03b2_568_, v_x_569_, v_x_8451__boxed_574_, v_x_8452__boxed_575_, v_x_572_, v_x_573_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3(lean_object* v_00_u03b2_577_, lean_object* v_x_578_, size_t v_x_579_, lean_object* v_x_580_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___redArg(v_x_578_, v_x_579_, v_x_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___boxed(lean_object* v_00_u03b2_582_, lean_object* v_x_583_, lean_object* v_x_584_, lean_object* v_x_585_){
_start:
{
size_t v_x_8468__boxed_586_; lean_object* v_res_587_; 
v_x_8468__boxed_586_ = lean_unbox_usize(v_x_584_);
lean_dec(v_x_584_);
v_res_587_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3(v_00_u03b2_582_, v_x_583_, v_x_8468__boxed_586_, v_x_585_);
lean_dec(v_x_585_);
lean_dec_ref(v_x_583_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_588_, lean_object* v_n_589_, lean_object* v_k_590_, lean_object* v_v_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1___redArg(v_n_589_, v_k_590_, v_v_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_593_, size_t v_depth_594_, lean_object* v_keys_595_, lean_object* v_vals_596_, lean_object* v_heq_597_, lean_object* v_i_598_, lean_object* v_entries_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg(v_depth_594_, v_keys_595_, v_vals_596_, v_i_598_, v_entries_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_601_, lean_object* v_depth_602_, lean_object* v_keys_603_, lean_object* v_vals_604_, lean_object* v_heq_605_, lean_object* v_i_606_, lean_object* v_entries_607_){
_start:
{
size_t v_depth_boxed_608_; lean_object* v_res_609_; 
v_depth_boxed_608_ = lean_unbox_usize(v_depth_602_);
lean_dec(v_depth_602_);
v_res_609_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2(v_00_u03b2_601_, v_depth_boxed_608_, v_keys_603_, v_vals_604_, v_heq_605_, v_i_606_, v_entries_607_);
lean_dec_ref(v_vals_604_);
lean_dec_ref(v_keys_603_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_610_, lean_object* v_keys_611_, lean_object* v_vals_612_, lean_object* v_heq_613_, lean_object* v_i_614_, lean_object* v_k_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6___redArg(v_keys_611_, v_vals_612_, v_i_614_, v_k_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_617_, lean_object* v_keys_618_, lean_object* v_vals_619_, lean_object* v_heq_620_, lean_object* v_i_621_, lean_object* v_k_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6(v_00_u03b2_617_, v_keys_618_, v_vals_619_, v_heq_620_, v_i_621_, v_k_622_);
lean_dec(v_k_622_);
lean_dec_ref(v_vals_619_);
lean_dec_ref(v_keys_618_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_624_, lean_object* v_x_625_, lean_object* v_x_626_, lean_object* v_x_627_, lean_object* v_x_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__4___redArg(v_x_625_, v_x_626_, v_x_627_, v_x_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(lean_object* v_x_630_, lean_object* v_e_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_){
_start:
{
lean_object* v___x_643_; 
lean_inc_ref(v_e_631_);
v___x_643_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_631_, v_a_639_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v_a_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
v_a_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_a_644_);
lean_dec_ref_known(v___x_643_, 1);
v___x_645_ = l_Lean_Expr_cleanupAnnotations(v_a_644_);
v___x_646_ = l_Lean_Expr_isApp(v___x_645_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; 
lean_dec_ref(v___x_645_);
v___x_647_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_631_, v_x_630_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_);
return v___x_647_;
}
else
{
lean_object* v_arg_648_; lean_object* v___x_649_; uint8_t v___x_650_; 
v_arg_648_ = lean_ctor_get(v___x_645_, 1);
lean_inc_ref(v_arg_648_);
v___x_649_ = l_Lean_Expr_appFnCleanup___redArg(v___x_645_);
v___x_650_ = l_Lean_Expr_isApp(v___x_649_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; 
lean_dec_ref(v___x_649_);
lean_dec_ref(v_arg_648_);
v___x_651_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_631_, v_x_630_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_);
return v___x_651_;
}
else
{
lean_object* v_arg_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v_arg_652_ = lean_ctor_get(v___x_649_, 1);
lean_inc_ref(v_arg_652_);
v___x_653_ = l_Lean_Expr_appFnCleanup___redArg(v___x_649_);
v___x_654_ = l_Lean_Expr_isApp(v___x_653_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; 
lean_dec_ref(v___x_653_);
lean_dec_ref(v_arg_652_);
lean_dec_ref(v_arg_648_);
v___x_655_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_631_, v_x_630_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_);
return v___x_655_;
}
else
{
lean_object* v_arg_656_; lean_object* v___x_657_; uint8_t v___x_658_; 
v_arg_656_ = lean_ctor_get(v___x_653_, 1);
lean_inc_ref(v_arg_656_);
v___x_657_ = l_Lean_Expr_appFnCleanup___redArg(v___x_653_);
v___x_658_ = l_Lean_Expr_isApp(v___x_657_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; 
lean_dec_ref(v___x_657_);
lean_dec_ref(v_arg_656_);
lean_dec_ref(v_arg_652_);
lean_dec_ref(v_arg_648_);
v___x_659_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_631_, v_x_630_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_);
return v___x_659_;
}
else
{
lean_object* v___x_660_; uint8_t v___x_661_; 
v___x_660_ = l_Lean_Expr_appFnCleanup___redArg(v___x_657_);
v___x_661_ = l_Lean_Expr_isApp(v___x_660_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; 
lean_dec_ref(v___x_660_);
lean_dec_ref(v_arg_656_);
lean_dec_ref(v_arg_652_);
lean_dec_ref(v_arg_648_);
v___x_662_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_631_, v_x_630_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_);
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
lean_dec_ref(v_arg_656_);
lean_dec_ref(v_arg_652_);
lean_dec_ref(v_arg_648_);
v___x_665_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_631_, v_x_630_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_);
return v___x_665_;
}
else
{
lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v___x_666_ = l_Lean_Expr_appFnCleanup___redArg(v___x_663_);
v___x_667_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11));
v___x_668_ = l_Lean_Expr_isConstOf(v___x_666_, v___x_667_);
lean_dec_ref(v___x_666_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; 
lean_dec_ref(v_arg_656_);
lean_dec_ref(v_arg_652_);
lean_dec_ref(v_arg_648_);
v___x_669_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_631_, v_x_630_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_);
return v___x_669_;
}
else
{
lean_object* v___x_670_; 
v___x_670_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_656_, v_a_639_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; uint8_t v___x_672_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_a_671_);
lean_dec_ref_known(v___x_670_, 1);
v___x_672_ = lean_unbox(v_a_671_);
lean_dec(v_a_671_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; 
lean_dec_ref(v_arg_652_);
lean_dec_ref(v_arg_648_);
v___x_673_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_631_, v_x_630_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_);
return v___x_673_;
}
else
{
lean_object* v___x_674_; 
lean_dec_ref(v_e_631_);
lean_inc(v_x_630_);
v___x_674_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(v_x_630_, v_arg_652_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_dec_ref_known(v___x_674_, 1);
v_e_631_ = v_arg_648_;
goto _start;
}
else
{
lean_dec_ref(v_arg_648_);
lean_dec(v_x_630_);
return v___x_674_;
}
}
}
else
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_683_; 
lean_dec_ref(v_arg_652_);
lean_dec_ref(v_arg_648_);
lean_dec_ref(v_e_631_);
lean_dec(v_x_630_);
v_a_676_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_683_ == 0)
{
v___x_678_ = v___x_670_;
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_670_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_a_676_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
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
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_691_; 
lean_dec_ref(v_e_631_);
lean_dec(v_x_630_);
v_a_684_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_691_ == 0)
{
v___x_686_ = v___x_643_;
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_643_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_689_; 
if (v_isShared_687_ == 0)
{
v___x_689_ = v___x_686_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_684_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go___boxed(lean_object* v_x_692_, lean_object* v_e_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(v_x_692_, v_e_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_);
lean_dec(v_a_703_);
lean_dec_ref(v_a_702_);
lean_dec(v_a_701_);
lean_dec_ref(v_a_700_);
lean_dec(v_a_699_);
lean_dec_ref(v_a_698_);
lean_dec(v_a_697_);
lean_dec_ref(v_a_696_);
lean_dec(v_a_695_);
lean_dec(v_a_694_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt(lean_object* v_e_706_, lean_object* v_x_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_706_, v_a_715_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_825_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_825_ == 0)
{
v___x_725_ = v___x_722_;
v_isShared_726_ = v_isSharedCheck_825_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_722_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_825_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_732_ = l_Lean_Expr_cleanupAnnotations(v_a_723_);
v___x_733_ = l_Lean_Expr_isApp(v___x_732_);
if (v___x_733_ == 0)
{
lean_dec_ref(v___x_732_);
lean_dec(v_x_707_);
goto v___jp_727_;
}
else
{
lean_object* v_arg_734_; lean_object* v___x_735_; uint8_t v___x_736_; 
v_arg_734_ = lean_ctor_get(v___x_732_, 1);
lean_inc_ref(v_arg_734_);
v___x_735_ = l_Lean_Expr_appFnCleanup___redArg(v___x_732_);
v___x_736_ = l_Lean_Expr_isApp(v___x_735_);
if (v___x_736_ == 0)
{
lean_dec_ref(v___x_735_);
lean_dec_ref(v_arg_734_);
lean_dec(v_x_707_);
goto v___jp_727_;
}
else
{
lean_object* v_arg_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v_arg_737_ = lean_ctor_get(v___x_735_, 1);
lean_inc_ref(v_arg_737_);
v___x_738_ = l_Lean_Expr_appFnCleanup___redArg(v___x_735_);
v___x_739_ = l_Lean_Expr_isApp(v___x_738_);
if (v___x_739_ == 0)
{
lean_dec_ref(v___x_738_);
lean_dec_ref(v_arg_737_);
lean_dec_ref(v_arg_734_);
lean_dec(v_x_707_);
goto v___jp_727_;
}
else
{
lean_object* v___x_740_; uint8_t v___x_741_; 
v___x_740_ = l_Lean_Expr_appFnCleanup___redArg(v___x_738_);
v___x_741_ = l_Lean_Expr_isApp(v___x_740_);
if (v___x_741_ == 0)
{
lean_dec_ref(v___x_740_);
lean_dec_ref(v_arg_737_);
lean_dec_ref(v_arg_734_);
lean_dec(v_x_707_);
goto v___jp_727_;
}
else
{
lean_object* v___x_742_; uint8_t v___x_743_; 
v___x_742_ = l_Lean_Expr_appFnCleanup___redArg(v___x_740_);
v___x_743_ = l_Lean_Expr_isApp(v___x_742_);
if (v___x_743_ == 0)
{
lean_dec_ref(v___x_742_);
lean_dec_ref(v_arg_737_);
lean_dec_ref(v_arg_734_);
lean_dec(v_x_707_);
goto v___jp_727_;
}
else
{
lean_object* v___x_744_; uint8_t v___x_745_; 
v___x_744_ = l_Lean_Expr_appFnCleanup___redArg(v___x_742_);
v___x_745_ = l_Lean_Expr_isApp(v___x_744_);
if (v___x_745_ == 0)
{
lean_dec_ref(v___x_744_);
lean_dec_ref(v_arg_737_);
lean_dec_ref(v_arg_734_);
lean_dec(v_x_707_);
goto v___jp_727_;
}
else
{
lean_object* v___x_746_; lean_object* v___x_747_; uint8_t v___x_748_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; 
v___x_746_ = l_Lean_Expr_appFnCleanup___redArg(v___x_744_);
v___x_747_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__2));
v___x_748_ = l_Lean_Expr_isConstOf(v___x_746_, v___x_747_);
if (v___x_748_ == 0)
{
lean_object* v___x_804_; uint8_t v___x_805_; 
v___x_804_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__5));
v___x_805_ = l_Lean_Expr_isConstOf(v___x_746_, v___x_804_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; uint8_t v___x_807_; 
v___x_806_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__8));
v___x_807_ = l_Lean_Expr_isConstOf(v___x_746_, v___x_806_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; uint8_t v___x_809_; 
v___x_808_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11));
v___x_809_ = l_Lean_Expr_isConstOf(v___x_746_, v___x_808_);
lean_dec_ref(v___x_746_);
if (v___x_809_ == 0)
{
lean_dec_ref(v_arg_737_);
lean_dec_ref(v_arg_734_);
lean_dec(v_x_707_);
goto v___jp_727_;
}
else
{
lean_object* v___x_810_; 
lean_del_object(v___x_725_);
lean_inc(v_x_707_);
v___x_810_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(v_x_707_, v_arg_737_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v___x_811_; 
lean_dec_ref_known(v___x_810_, 1);
v___x_811_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(v_x_707_, v_arg_734_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
return v___x_811_;
}
else
{
lean_dec_ref(v_arg_734_);
lean_dec(v_x_707_);
return v___x_810_;
}
}
}
else
{
lean_object* v___x_812_; 
lean_dec_ref(v___x_746_);
lean_dec_ref(v_arg_737_);
lean_del_object(v___x_725_);
v___x_812_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_arg_734_, v_x_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
return v___x_812_;
}
}
else
{
lean_object* v___x_813_; 
lean_dec_ref(v___x_746_);
lean_dec_ref(v_arg_737_);
lean_del_object(v___x_725_);
v___x_813_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_arg_734_, v_x_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
return v___x_813_;
}
}
else
{
lean_object* v___x_814_; 
lean_dec_ref(v___x_746_);
lean_del_object(v___x_725_);
lean_inc_ref(v_arg_737_);
v___x_814_ = l_Lean_Meta_getIntValue_x3f(v_arg_737_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v_a_815_; 
v_a_815_ = lean_ctor_get(v___x_814_, 0);
lean_inc(v_a_815_);
lean_dec_ref_known(v___x_814_, 1);
if (lean_obj_tag(v_a_815_) == 0)
{
if (v___x_748_ == 0)
{
lean_dec_ref(v_arg_737_);
v___y_750_ = v_a_708_;
v___y_751_ = v_a_709_;
v___y_752_ = v_a_710_;
v___y_753_ = v_a_711_;
v___y_754_ = v_a_712_;
v___y_755_ = v_a_713_;
v___y_756_ = v_a_714_;
v___y_757_ = v_a_715_;
v___y_758_ = v_a_716_;
v___y_759_ = v_a_717_;
goto v___jp_749_;
}
else
{
lean_object* v___x_816_; 
lean_inc(v_x_707_);
v___x_816_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_arg_737_, v_x_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_dec_ref_known(v___x_816_, 1);
v___y_750_ = v_a_708_;
v___y_751_ = v_a_709_;
v___y_752_ = v_a_710_;
v___y_753_ = v_a_711_;
v___y_754_ = v_a_712_;
v___y_755_ = v_a_713_;
v___y_756_ = v_a_714_;
v___y_757_ = v_a_715_;
v___y_758_ = v_a_716_;
v___y_759_ = v_a_717_;
goto v___jp_749_;
}
else
{
lean_dec_ref(v_arg_734_);
lean_dec(v_x_707_);
return v___x_816_;
}
}
}
else
{
lean_dec_ref_known(v_a_815_, 1);
lean_dec_ref(v_arg_737_);
v___y_750_ = v_a_708_;
v___y_751_ = v_a_709_;
v___y_752_ = v_a_710_;
v___y_753_ = v_a_711_;
v___y_754_ = v_a_712_;
v___y_755_ = v_a_713_;
v___y_756_ = v_a_714_;
v___y_757_ = v_a_715_;
v___y_758_ = v_a_716_;
v___y_759_ = v_a_717_;
goto v___jp_749_;
}
}
else
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_824_; 
lean_dec_ref(v_arg_737_);
lean_dec_ref(v_arg_734_);
lean_dec(v_x_707_);
v_a_817_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_824_ == 0)
{
v___x_819_ = v___x_814_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_814_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_820_ == 0)
{
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_a_817_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
v___jp_749_:
{
lean_object* v___x_760_; 
lean_inc_ref(v_arg_734_);
v___x_760_ = l_Lean_Meta_getIntValue_x3f(v_arg_734_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v_a_761_; lean_object* v___x_762_; 
v_a_761_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_a_761_);
lean_dec_ref_known(v___x_760_, 1);
v___x_762_ = l_Lean_Meta_getNatValue_x3f(v_arg_734_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
if (lean_obj_tag(v___x_762_) == 0)
{
if (lean_obj_tag(v_a_761_) == 0)
{
if (v___x_748_ == 0)
{
lean_dec_ref_known(v___x_762_, 1);
lean_dec_ref(v_arg_734_);
lean_dec(v_x_707_);
goto v___jp_719_;
}
else
{
lean_object* v_a_763_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_a_763_);
lean_dec_ref_known(v___x_762_, 1);
if (lean_obj_tag(v_a_763_) == 0)
{
lean_object* v___x_764_; 
lean_inc_ref(v_arg_734_);
v___x_764_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_arg_734_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v_a_765_; lean_object* v_fst_766_; lean_object* v___x_767_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_a_765_);
lean_dec_ref_known(v___x_764_, 1);
v_fst_766_ = lean_ctor_get(v_a_765_, 0);
lean_inc(v_fst_766_);
lean_dec(v_a_765_);
v___x_767_ = l_Lean_Meta_Grind_getGeneration___redArg(v_arg_734_, v___y_750_);
lean_dec_ref(v_arg_734_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v_a_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_a_768_);
lean_dec_ref_known(v___x_767_, 1);
v___x_769_ = lean_box(0);
lean_inc(v___y_759_);
lean_inc_ref(v___y_758_);
lean_inc(v___y_757_);
lean_inc_ref(v___y_756_);
lean_inc(v___y_755_);
lean_inc_ref(v___y_754_);
lean_inc(v___y_753_);
lean_inc_ref(v___y_752_);
lean_inc(v___y_751_);
lean_inc(v___y_750_);
lean_inc(v_fst_766_);
v___x_770_ = lean_grind_internalize(v_fst_766_, v_a_768_, v___x_769_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v___x_771_; 
lean_dec_ref_known(v___x_770_, 1);
v___x_771_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_fst_766_, v_x_707_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
return v___x_771_;
}
else
{
lean_dec(v_fst_766_);
lean_dec(v_x_707_);
return v___x_770_;
}
}
else
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
lean_dec(v_fst_766_);
lean_dec(v_x_707_);
v_a_772_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_779_ == 0)
{
v___x_774_ = v___x_767_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_767_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_772_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
else
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_787_; 
lean_dec_ref(v_arg_734_);
lean_dec(v_x_707_);
v_a_780_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_787_ == 0)
{
v___x_782_ = v___x_764_;
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_764_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_a_780_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_763_, 1);
lean_dec_ref(v_arg_734_);
lean_dec(v_x_707_);
goto v___jp_719_;
}
}
}
else
{
lean_dec_ref_known(v_a_761_, 1);
lean_dec_ref_known(v___x_762_, 1);
lean_dec_ref(v_arg_734_);
lean_dec(v_x_707_);
goto v___jp_719_;
}
}
else
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_795_; 
lean_dec(v_a_761_);
lean_dec_ref(v_arg_734_);
lean_dec(v_x_707_);
v_a_788_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_795_ == 0)
{
v___x_790_ = v___x_762_;
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_762_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_795_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_791_ == 0)
{
v___x_793_ = v___x_790_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v_a_788_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
lean_dec_ref(v_arg_734_);
lean_dec(v_x_707_);
v_a_796_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_760_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_760_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
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
v___jp_727_:
{
lean_object* v___x_728_; lean_object* v___x_730_; 
v___x_728_ = lean_box(0);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 0, v___x_728_);
v___x_730_ = v___x_725_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_728_);
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
else
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
lean_dec(v_x_707_);
v_a_826_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___x_722_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_722_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_826_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
v___jp_719_:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = lean_box(0);
v___x_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
return v___x_721_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt___boxed(lean_object* v_e_834_, lean_object* v_x_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt(v_e_834_, v_x_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_);
lean_dec(v_a_845_);
lean_dec_ref(v_a_844_);
lean_dec(v_a_843_);
lean_dec_ref(v_a_842_);
lean_dec(v_a_841_);
lean_dec_ref(v_a_840_);
lean_dec(v_a_839_);
lean_dec_ref(v_a_838_);
lean_dec(v_a_837_);
lean_dec(v_a_836_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_x_848_, lean_object* v_x_849_, lean_object* v_x_850_, lean_object* v_x_851_){
_start:
{
lean_object* v_ks_852_; lean_object* v_vs_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_879_; 
v_ks_852_ = lean_ctor_get(v_x_848_, 0);
v_vs_853_ = lean_ctor_get(v_x_848_, 1);
v_isSharedCheck_879_ = !lean_is_exclusive(v_x_848_);
if (v_isSharedCheck_879_ == 0)
{
v___x_855_ = v_x_848_;
v_isShared_856_ = v_isSharedCheck_879_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_vs_853_);
lean_inc(v_ks_852_);
lean_dec(v_x_848_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_879_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_857_; uint8_t v___x_858_; 
v___x_857_ = lean_array_get_size(v_ks_852_);
v___x_858_ = lean_nat_dec_lt(v_x_849_, v___x_857_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_862_; 
lean_dec(v_x_849_);
v___x_859_ = lean_array_push(v_ks_852_, v_x_850_);
v___x_860_ = lean_array_push(v_vs_853_, v_x_851_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 1, v___x_860_);
lean_ctor_set(v___x_855_, 0, v___x_859_);
v___x_862_ = v___x_855_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_859_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v___x_860_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
else
{
lean_object* v_k_x27_864_; size_t v___x_865_; size_t v___x_866_; uint8_t v___x_867_; 
v_k_x27_864_ = lean_array_fget_borrowed(v_ks_852_, v_x_849_);
v___x_865_ = lean_ptr_addr(v_x_850_);
v___x_866_ = lean_ptr_addr(v_k_x27_864_);
v___x_867_ = lean_usize_dec_eq(v___x_865_, v___x_866_);
if (v___x_867_ == 0)
{
lean_object* v___x_869_; 
if (v_isShared_856_ == 0)
{
v___x_869_ = v___x_855_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_ks_852_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v_vs_853_);
v___x_869_ = v_reuseFailAlloc_873_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = lean_unsigned_to_nat(1u);
v___x_871_ = lean_nat_add(v_x_849_, v___x_870_);
lean_dec(v_x_849_);
v_x_848_ = v___x_869_;
v_x_849_ = v___x_871_;
goto _start;
}
}
else
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_877_; 
v___x_874_ = lean_array_fset(v_ks_852_, v_x_849_, v_x_850_);
v___x_875_ = lean_array_fset(v_vs_853_, v_x_849_, v_x_851_);
lean_dec(v_x_849_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 1, v___x_875_);
lean_ctor_set(v___x_855_, 0, v___x_874_);
v___x_877_ = v___x_855_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_874_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v___x_875_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4___redArg(lean_object* v_n_880_, lean_object* v_k_881_, lean_object* v_v_882_){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = lean_unsigned_to_nat(0u);
v___x_884_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7___redArg(v_n_880_, v___x_883_, v_k_881_, v_v_882_);
return v___x_884_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(lean_object* v_x_886_, size_t v_x_887_, size_t v_x_888_, lean_object* v_x_889_, lean_object* v_x_890_){
_start:
{
if (lean_obj_tag(v_x_886_) == 0)
{
lean_object* v_es_891_; size_t v___x_892_; size_t v___x_893_; lean_object* v_j_894_; lean_object* v___x_895_; uint8_t v___x_896_; 
v_es_891_ = lean_ctor_get(v_x_886_, 0);
v___x_892_ = ((size_t)31ULL);
v___x_893_ = lean_usize_land(v_x_887_, v___x_892_);
v_j_894_ = lean_usize_to_nat(v___x_893_);
v___x_895_ = lean_array_get_size(v_es_891_);
v___x_896_ = lean_nat_dec_lt(v_j_894_, v___x_895_);
if (v___x_896_ == 0)
{
lean_dec(v_j_894_);
lean_dec(v_x_890_);
lean_dec_ref(v_x_889_);
return v_x_886_;
}
else
{
lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_937_; 
lean_inc_ref(v_es_891_);
v_isSharedCheck_937_ = !lean_is_exclusive(v_x_886_);
if (v_isSharedCheck_937_ == 0)
{
lean_object* v_unused_938_; 
v_unused_938_ = lean_ctor_get(v_x_886_, 0);
lean_dec(v_unused_938_);
v___x_898_ = v_x_886_;
v_isShared_899_ = v_isSharedCheck_937_;
goto v_resetjp_897_;
}
else
{
lean_dec(v_x_886_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_937_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v_v_900_; lean_object* v___x_901_; lean_object* v_xs_x27_902_; lean_object* v___y_904_; 
v_v_900_ = lean_array_fget(v_es_891_, v_j_894_);
v___x_901_ = lean_box(0);
v_xs_x27_902_ = lean_array_fset(v_es_891_, v_j_894_, v___x_901_);
switch(lean_obj_tag(v_v_900_))
{
case 0:
{
lean_object* v_key_909_; lean_object* v_val_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_922_; 
v_key_909_ = lean_ctor_get(v_v_900_, 0);
v_val_910_ = lean_ctor_get(v_v_900_, 1);
v_isSharedCheck_922_ = !lean_is_exclusive(v_v_900_);
if (v_isSharedCheck_922_ == 0)
{
v___x_912_ = v_v_900_;
v_isShared_913_ = v_isSharedCheck_922_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_val_910_);
lean_inc(v_key_909_);
lean_dec(v_v_900_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_922_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
size_t v___x_914_; size_t v___x_915_; uint8_t v___x_916_; 
v___x_914_ = lean_ptr_addr(v_x_889_);
v___x_915_ = lean_ptr_addr(v_key_909_);
v___x_916_ = lean_usize_dec_eq(v___x_914_, v___x_915_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; lean_object* v___x_918_; 
lean_del_object(v___x_912_);
v___x_917_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_909_, v_val_910_, v_x_889_, v_x_890_);
v___x_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
v___y_904_ = v___x_918_;
goto v___jp_903_;
}
else
{
lean_object* v___x_920_; 
lean_dec(v_val_910_);
lean_dec(v_key_909_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 1, v_x_890_);
lean_ctor_set(v___x_912_, 0, v_x_889_);
v___x_920_ = v___x_912_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_x_889_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_x_890_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
v___y_904_ = v___x_920_;
goto v___jp_903_;
}
}
}
}
case 1:
{
lean_object* v_node_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_935_; 
v_node_923_ = lean_ctor_get(v_v_900_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v_v_900_);
if (v_isSharedCheck_935_ == 0)
{
v___x_925_ = v_v_900_;
v_isShared_926_ = v_isSharedCheck_935_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_node_923_);
lean_dec(v_v_900_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_935_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
size_t v___x_927_; size_t v___x_928_; size_t v___x_929_; size_t v___x_930_; lean_object* v___x_931_; lean_object* v___x_933_; 
v___x_927_ = ((size_t)5ULL);
v___x_928_ = lean_usize_shift_right(v_x_887_, v___x_927_);
v___x_929_ = ((size_t)1ULL);
v___x_930_ = lean_usize_add(v_x_888_, v___x_929_);
v___x_931_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_node_923_, v___x_928_, v___x_930_, v_x_889_, v_x_890_);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 0, v___x_931_);
v___x_933_ = v___x_925_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_931_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
v___y_904_ = v___x_933_;
goto v___jp_903_;
}
}
}
default: 
{
lean_object* v___x_936_; 
v___x_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_936_, 0, v_x_889_);
lean_ctor_set(v___x_936_, 1, v_x_890_);
v___y_904_ = v___x_936_;
goto v___jp_903_;
}
}
v___jp_903_:
{
lean_object* v___x_905_; lean_object* v___x_907_; 
v___x_905_ = lean_array_fset(v_xs_x27_902_, v_j_894_, v___y_904_);
lean_dec(v_j_894_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 0, v___x_905_);
v___x_907_ = v___x_898_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_905_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
}
else
{
lean_object* v_ks_939_; lean_object* v_vs_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_958_; 
v_ks_939_ = lean_ctor_get(v_x_886_, 0);
v_vs_940_ = lean_ctor_get(v_x_886_, 1);
v_isSharedCheck_958_ = !lean_is_exclusive(v_x_886_);
if (v_isSharedCheck_958_ == 0)
{
v___x_942_ = v_x_886_;
v_isShared_943_ = v_isSharedCheck_958_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_vs_940_);
lean_inc(v_ks_939_);
lean_dec(v_x_886_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_958_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_ks_939_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v_vs_940_);
v___x_945_ = v_reuseFailAlloc_957_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
lean_object* v_newNode_946_; size_t v___x_947_; uint8_t v___x_948_; 
v_newNode_946_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4___redArg(v___x_945_, v_x_889_, v_x_890_);
v___x_947_ = ((size_t)7ULL);
v___x_948_ = lean_usize_dec_le(v___x_947_, v_x_888_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; lean_object* v___x_950_; uint8_t v___x_951_; 
v___x_949_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_946_);
v___x_950_ = lean_unsigned_to_nat(4u);
v___x_951_ = lean_nat_dec_lt(v___x_949_, v___x_950_);
lean_dec(v___x_949_);
if (v___x_951_ == 0)
{
lean_object* v_ks_952_; lean_object* v_vs_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v_ks_952_ = lean_ctor_get(v_newNode_946_, 0);
lean_inc_ref(v_ks_952_);
v_vs_953_ = lean_ctor_get(v_newNode_946_, 1);
lean_inc_ref(v_vs_953_);
lean_dec_ref(v_newNode_946_);
v___x_954_ = lean_unsigned_to_nat(0u);
v___x_955_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg___closed__0);
v___x_956_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(v_x_888_, v_ks_952_, v_vs_953_, v___x_954_, v___x_955_);
lean_dec_ref(v_vs_953_);
lean_dec_ref(v_ks_952_);
return v___x_956_;
}
else
{
return v_newNode_946_;
}
}
else
{
return v_newNode_946_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(size_t v_depth_959_, lean_object* v_keys_960_, lean_object* v_vals_961_, lean_object* v_i_962_, lean_object* v_entries_963_){
_start:
{
lean_object* v___x_964_; uint8_t v___x_965_; 
v___x_964_ = lean_array_get_size(v_keys_960_);
v___x_965_ = lean_nat_dec_lt(v_i_962_, v___x_964_);
if (v___x_965_ == 0)
{
lean_dec(v_i_962_);
return v_entries_963_;
}
else
{
lean_object* v_k_966_; lean_object* v_v_967_; size_t v___x_968_; size_t v___x_969_; size_t v___x_970_; uint64_t v___x_971_; size_t v_h_972_; size_t v___x_973_; lean_object* v___x_974_; size_t v___x_975_; size_t v___x_976_; size_t v___x_977_; size_t v_h_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v_k_966_ = lean_array_fget_borrowed(v_keys_960_, v_i_962_);
v_v_967_ = lean_array_fget_borrowed(v_vals_961_, v_i_962_);
v___x_968_ = lean_ptr_addr(v_k_966_);
v___x_969_ = ((size_t)3ULL);
v___x_970_ = lean_usize_shift_right(v___x_968_, v___x_969_);
v___x_971_ = lean_usize_to_uint64(v___x_970_);
v_h_972_ = lean_uint64_to_usize(v___x_971_);
v___x_973_ = ((size_t)5ULL);
v___x_974_ = lean_unsigned_to_nat(1u);
v___x_975_ = ((size_t)1ULL);
v___x_976_ = lean_usize_sub(v_depth_959_, v___x_975_);
v___x_977_ = lean_usize_mul(v___x_973_, v___x_976_);
v_h_978_ = lean_usize_shift_right(v_h_972_, v___x_977_);
v___x_979_ = lean_nat_add(v_i_962_, v___x_974_);
lean_dec(v_i_962_);
lean_inc(v_v_967_);
lean_inc(v_k_966_);
v___x_980_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_entries_963_, v_h_978_, v_depth_959_, v_k_966_, v_v_967_);
v_i_962_ = v___x_979_;
v_entries_963_ = v___x_980_;
goto _start;
}
}
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
size_t v_x_27413__boxed_994_; size_t v_x_27414__boxed_995_; lean_object* v_res_996_; 
v_x_27413__boxed_994_ = lean_unbox_usize(v_x_990_);
lean_dec(v_x_990_);
v_x_27414__boxed_995_ = lean_unbox_usize(v_x_991_);
lean_dec(v_x_991_);
v_res_996_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_x_989_, v_x_27413__boxed_994_, v_x_27414__boxed_995_, v_x_992_, v_x_993_);
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
lean_object* v_vars_1019_; lean_object* v_varMap_1020_; lean_object* v_vars_x27_1021_; lean_object* v_varMap_x27_1022_; lean_object* v_natToIntMap_1023_; lean_object* v_natDef_1024_; lean_object* v_dvds_1025_; lean_object* v_lowers_1026_; lean_object* v_uppers_1027_; lean_object* v_diseqs_1028_; lean_object* v_elimEqs_1029_; lean_object* v_elimStack_1030_; lean_object* v_occurs_1031_; lean_object* v_assignment_1032_; lean_object* v_nextCnstrId_1033_; uint8_t v_caseSplits_1034_; lean_object* v_steps_1035_; lean_object* v_conflict_x3f_1036_; lean_object* v_diseqSplits_1037_; lean_object* v_divMod_1038_; uint8_t v_usedCommRing_1039_; lean_object* v_nonlinearOccs_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1058_; 
v_vars_1019_ = lean_ctor_get(v_s_1018_, 0);
v_varMap_1020_ = lean_ctor_get(v_s_1018_, 1);
v_vars_x27_1021_ = lean_ctor_get(v_s_1018_, 2);
v_varMap_x27_1022_ = lean_ctor_get(v_s_1018_, 3);
v_natToIntMap_1023_ = lean_ctor_get(v_s_1018_, 4);
v_natDef_1024_ = lean_ctor_get(v_s_1018_, 5);
v_dvds_1025_ = lean_ctor_get(v_s_1018_, 6);
v_lowers_1026_ = lean_ctor_get(v_s_1018_, 7);
v_uppers_1027_ = lean_ctor_get(v_s_1018_, 8);
v_diseqs_1028_ = lean_ctor_get(v_s_1018_, 9);
v_elimEqs_1029_ = lean_ctor_get(v_s_1018_, 10);
v_elimStack_1030_ = lean_ctor_get(v_s_1018_, 11);
v_occurs_1031_ = lean_ctor_get(v_s_1018_, 12);
v_assignment_1032_ = lean_ctor_get(v_s_1018_, 13);
v_nextCnstrId_1033_ = lean_ctor_get(v_s_1018_, 14);
v_caseSplits_1034_ = lean_ctor_get_uint8(v_s_1018_, sizeof(void*)*20);
v_steps_1035_ = lean_ctor_get(v_s_1018_, 15);
v_conflict_x3f_1036_ = lean_ctor_get(v_s_1018_, 16);
v_diseqSplits_1037_ = lean_ctor_get(v_s_1018_, 17);
v_divMod_1038_ = lean_ctor_get(v_s_1018_, 18);
v_usedCommRing_1039_ = lean_ctor_get_uint8(v_s_1018_, sizeof(void*)*20 + 1);
v_nonlinearOccs_1040_ = lean_ctor_get(v_s_1018_, 19);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_s_1018_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1042_ = v_s_1018_;
v_isShared_1043_ = v_isSharedCheck_1058_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_nonlinearOccs_1040_);
lean_inc(v_divMod_1038_);
lean_inc(v_diseqSplits_1037_);
lean_inc(v_conflict_x3f_1036_);
lean_inc(v_steps_1035_);
lean_inc(v_nextCnstrId_1033_);
lean_inc(v_assignment_1032_);
lean_inc(v_occurs_1031_);
lean_inc(v_elimStack_1030_);
lean_inc(v_elimEqs_1029_);
lean_inc(v_diseqs_1028_);
lean_inc(v_uppers_1027_);
lean_inc(v_lowers_1026_);
lean_inc(v_dvds_1025_);
lean_inc(v_natDef_1024_);
lean_inc(v_natToIntMap_1023_);
lean_inc(v_varMap_x27_1022_);
lean_inc(v_vars_x27_1021_);
lean_inc(v_varMap_1020_);
lean_inc(v_vars_1019_);
lean_dec(v_s_1018_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1058_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1056_; 
lean_inc_ref(v_expr_1016_);
v___x_1044_ = l_Lean_PersistentArray_push___redArg(v_vars_1019_, v_expr_1016_);
v___x_1045_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg(v_varMap_1020_, v_expr_1016_, v_size_1017_);
v___x_1046_ = lean_box(0);
v___x_1047_ = l_Lean_PersistentArray_push___redArg(v_dvds_1025_, v___x_1046_);
v___x_1048_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1);
v___x_1049_ = l_Lean_PersistentArray_push___redArg(v_lowers_1026_, v___x_1048_);
v___x_1050_ = l_Lean_PersistentArray_push___redArg(v_uppers_1027_, v___x_1048_);
v___x_1051_ = l_Lean_PersistentArray_push___redArg(v_diseqs_1028_, v___x_1048_);
v___x_1052_ = l_Lean_PersistentArray_push___redArg(v_elimEqs_1029_, v___x_1046_);
v___x_1053_ = lean_box(1);
v___x_1054_ = l_Lean_PersistentArray_push___redArg(v_occurs_1031_, v___x_1053_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 12, v___x_1054_);
lean_ctor_set(v___x_1042_, 10, v___x_1052_);
lean_ctor_set(v___x_1042_, 9, v___x_1051_);
lean_ctor_set(v___x_1042_, 8, v___x_1050_);
lean_ctor_set(v___x_1042_, 7, v___x_1049_);
lean_ctor_set(v___x_1042_, 6, v___x_1047_);
lean_ctor_set(v___x_1042_, 1, v___x_1045_);
lean_ctor_set(v___x_1042_, 0, v___x_1044_);
v___x_1056_ = v___x_1042_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 20, 2);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1044_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1057_, 2, v_vars_x27_1021_);
lean_ctor_set(v_reuseFailAlloc_1057_, 3, v_varMap_x27_1022_);
lean_ctor_set(v_reuseFailAlloc_1057_, 4, v_natToIntMap_1023_);
lean_ctor_set(v_reuseFailAlloc_1057_, 5, v_natDef_1024_);
lean_ctor_set(v_reuseFailAlloc_1057_, 6, v___x_1047_);
lean_ctor_set(v_reuseFailAlloc_1057_, 7, v___x_1049_);
lean_ctor_set(v_reuseFailAlloc_1057_, 8, v___x_1050_);
lean_ctor_set(v_reuseFailAlloc_1057_, 9, v___x_1051_);
lean_ctor_set(v_reuseFailAlloc_1057_, 10, v___x_1052_);
lean_ctor_set(v_reuseFailAlloc_1057_, 11, v_elimStack_1030_);
lean_ctor_set(v_reuseFailAlloc_1057_, 12, v___x_1054_);
lean_ctor_set(v_reuseFailAlloc_1057_, 13, v_assignment_1032_);
lean_ctor_set(v_reuseFailAlloc_1057_, 14, v_nextCnstrId_1033_);
lean_ctor_set(v_reuseFailAlloc_1057_, 15, v_steps_1035_);
lean_ctor_set(v_reuseFailAlloc_1057_, 16, v_conflict_x3f_1036_);
lean_ctor_set(v_reuseFailAlloc_1057_, 17, v_diseqSplits_1037_);
lean_ctor_set(v_reuseFailAlloc_1057_, 18, v_divMod_1038_);
lean_ctor_set(v_reuseFailAlloc_1057_, 19, v_nonlinearOccs_1040_);
lean_ctor_set_uint8(v_reuseFailAlloc_1057_, sizeof(void*)*20, v_caseSplits_1034_);
lean_ctor_set_uint8(v_reuseFailAlloc_1057_, sizeof(void*)*20 + 1, v_usedCommRing_1039_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1059_, lean_object* v_vals_1060_, lean_object* v_i_1061_, lean_object* v_k_1062_){
_start:
{
lean_object* v___x_1063_; uint8_t v___x_1064_; 
v___x_1063_ = lean_array_get_size(v_keys_1059_);
v___x_1064_ = lean_nat_dec_lt(v_i_1061_, v___x_1063_);
if (v___x_1064_ == 0)
{
lean_object* v___x_1065_; 
lean_dec(v_i_1061_);
v___x_1065_ = lean_box(0);
return v___x_1065_;
}
else
{
lean_object* v_k_x27_1066_; size_t v___x_1067_; size_t v___x_1068_; uint8_t v___x_1069_; 
v_k_x27_1066_ = lean_array_fget_borrowed(v_keys_1059_, v_i_1061_);
v___x_1067_ = lean_ptr_addr(v_k_1062_);
v___x_1068_ = lean_ptr_addr(v_k_x27_1066_);
v___x_1069_ = lean_usize_dec_eq(v___x_1067_, v___x_1068_);
if (v___x_1069_ == 0)
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = lean_unsigned_to_nat(1u);
v___x_1071_ = lean_nat_add(v_i_1061_, v___x_1070_);
lean_dec(v_i_1061_);
v_i_1061_ = v___x_1071_;
goto _start;
}
else
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = lean_array_fget_borrowed(v_vals_1060_, v_i_1061_);
lean_dec(v_i_1061_);
lean_inc(v___x_1073_);
v___x_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
return v___x_1074_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1075_, lean_object* v_vals_1076_, lean_object* v_i_1077_, lean_object* v_k_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(v_keys_1075_, v_vals_1076_, v_i_1077_, v_k_1078_);
lean_dec_ref(v_k_1078_);
lean_dec_ref(v_vals_1076_);
lean_dec_ref(v_keys_1075_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(lean_object* v_x_1080_, size_t v_x_1081_, lean_object* v_x_1082_){
_start:
{
if (lean_obj_tag(v_x_1080_) == 0)
{
lean_object* v_es_1083_; lean_object* v___x_1084_; size_t v___x_1085_; size_t v___x_1086_; lean_object* v_j_1087_; lean_object* v___x_1088_; 
v_es_1083_ = lean_ctor_get(v_x_1080_, 0);
v___x_1084_ = lean_box(2);
v___x_1085_ = ((size_t)31ULL);
v___x_1086_ = lean_usize_land(v_x_1081_, v___x_1085_);
v_j_1087_ = lean_usize_to_nat(v___x_1086_);
v___x_1088_ = lean_array_get_borrowed(v___x_1084_, v_es_1083_, v_j_1087_);
lean_dec(v_j_1087_);
switch(lean_obj_tag(v___x_1088_))
{
case 0:
{
lean_object* v_key_1089_; lean_object* v_val_1090_; size_t v___x_1091_; size_t v___x_1092_; uint8_t v___x_1093_; 
v_key_1089_ = lean_ctor_get(v___x_1088_, 0);
v_val_1090_ = lean_ctor_get(v___x_1088_, 1);
v___x_1091_ = lean_ptr_addr(v_x_1082_);
v___x_1092_ = lean_ptr_addr(v_key_1089_);
v___x_1093_ = lean_usize_dec_eq(v___x_1091_, v___x_1092_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1094_; 
v___x_1094_ = lean_box(0);
return v___x_1094_;
}
else
{
lean_object* v___x_1095_; 
lean_inc(v_val_1090_);
v___x_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1095_, 0, v_val_1090_);
return v___x_1095_;
}
}
case 1:
{
lean_object* v_node_1096_; size_t v___x_1097_; size_t v___x_1098_; 
v_node_1096_ = lean_ctor_get(v___x_1088_, 0);
v___x_1097_ = ((size_t)5ULL);
v___x_1098_ = lean_usize_shift_right(v_x_1081_, v___x_1097_);
v_x_1080_ = v_node_1096_;
v_x_1081_ = v___x_1098_;
goto _start;
}
default: 
{
lean_object* v___x_1100_; 
v___x_1100_ = lean_box(0);
return v___x_1100_;
}
}
}
else
{
lean_object* v_ks_1101_; lean_object* v_vs_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v_ks_1101_ = lean_ctor_get(v_x_1080_, 0);
v_vs_1102_ = lean_ctor_get(v_x_1080_, 1);
v___x_1103_ = lean_unsigned_to_nat(0u);
v___x_1104_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(v_ks_1101_, v_vs_1102_, v___x_1103_, v_x_1082_);
return v___x_1104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg___boxed(lean_object* v_x_1105_, lean_object* v_x_1106_, lean_object* v_x_1107_){
_start:
{
size_t v_x_27679__boxed_1108_; lean_object* v_res_1109_; 
v_x_27679__boxed_1108_ = lean_unbox_usize(v_x_1106_);
lean_dec(v_x_1106_);
v_res_1109_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(v_x_1105_, v_x_27679__boxed_1108_, v_x_1107_);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4(lean_object* v_msgData_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v___x_1127_; lean_object* v_env_1128_; lean_object* v___x_1129_; lean_object* v_toCold_1130_; lean_object* v_mctx_1131_; lean_object* v_lctx_1132_; lean_object* v_options_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1127_ = lean_st_ref_get(v___y_1125_);
v_env_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc_ref(v_env_1128_);
lean_dec(v___x_1127_);
v___x_1129_ = lean_st_ref_get(v___y_1123_);
v_toCold_1130_ = lean_ctor_get(v___y_1124_, 0);
v_mctx_1131_ = lean_ctor_get(v___x_1129_, 0);
lean_inc_ref(v_mctx_1131_);
lean_dec(v___x_1129_);
v_lctx_1132_ = lean_ctor_get(v___y_1122_, 2);
v_options_1133_ = lean_ctor_get(v_toCold_1130_, 2);
lean_inc_ref(v_options_1133_);
lean_inc_ref(v_lctx_1132_);
v___x_1134_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1134_, 0, v_env_1128_);
lean_ctor_set(v___x_1134_, 1, v_mctx_1131_);
lean_ctor_set(v___x_1134_, 2, v_lctx_1132_);
lean_ctor_set(v___x_1134_, 3, v_options_1133_);
v___x_1135_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1134_);
lean_ctor_set(v___x_1135_, 1, v_msgData_1121_);
v___x_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4___boxed(lean_object* v_msgData_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4(v_msgData_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
return v_res_1143_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1144_; double v___x_1145_; 
v___x_1144_ = lean_unsigned_to_nat(0u);
v___x_1145_ = lean_float_of_nat(v___x_1144_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(lean_object* v_cls_1149_, lean_object* v_msg_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v_ref_1156_; lean_object* v___x_1157_; lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1202_; 
v_ref_1156_ = lean_ctor_get(v___y_1153_, 2);
v___x_1157_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4(v_msg_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1160_ = v___x_1157_;
v_isShared_1161_ = v_isSharedCheck_1202_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1157_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1202_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1162_; lean_object* v_traceState_1163_; lean_object* v_env_1164_; lean_object* v_nextMacroScope_1165_; lean_object* v_ngen_1166_; lean_object* v_auxDeclNGen_1167_; lean_object* v_cache_1168_; lean_object* v_messages_1169_; lean_object* v_infoState_1170_; lean_object* v_snapshotTasks_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1201_; 
v___x_1162_ = lean_st_ref_take(v___y_1154_);
v_traceState_1163_ = lean_ctor_get(v___x_1162_, 4);
v_env_1164_ = lean_ctor_get(v___x_1162_, 0);
v_nextMacroScope_1165_ = lean_ctor_get(v___x_1162_, 1);
v_ngen_1166_ = lean_ctor_get(v___x_1162_, 2);
v_auxDeclNGen_1167_ = lean_ctor_get(v___x_1162_, 3);
v_cache_1168_ = lean_ctor_get(v___x_1162_, 5);
v_messages_1169_ = lean_ctor_get(v___x_1162_, 6);
v_infoState_1170_ = lean_ctor_get(v___x_1162_, 7);
v_snapshotTasks_1171_ = lean_ctor_get(v___x_1162_, 8);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1173_ = v___x_1162_;
v_isShared_1174_ = v_isSharedCheck_1201_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_snapshotTasks_1171_);
lean_inc(v_infoState_1170_);
lean_inc(v_messages_1169_);
lean_inc(v_cache_1168_);
lean_inc(v_traceState_1163_);
lean_inc(v_auxDeclNGen_1167_);
lean_inc(v_ngen_1166_);
lean_inc(v_nextMacroScope_1165_);
lean_inc(v_env_1164_);
lean_dec(v___x_1162_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1201_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
uint64_t v_tid_1175_; lean_object* v_traces_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1200_; 
v_tid_1175_ = lean_ctor_get_uint64(v_traceState_1163_, sizeof(void*)*1);
v_traces_1176_ = lean_ctor_get(v_traceState_1163_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v_traceState_1163_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1178_ = v_traceState_1163_;
v_isShared_1179_ = v_isSharedCheck_1200_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_traces_1176_);
lean_dec(v_traceState_1163_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1200_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1180_; double v___x_1181_; uint8_t v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1190_; 
v___x_1180_ = lean_box(0);
v___x_1181_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0);
v___x_1182_ = 0;
v___x_1183_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__1));
v___x_1184_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1184_, 0, v_cls_1149_);
lean_ctor_set(v___x_1184_, 1, v___x_1180_);
lean_ctor_set(v___x_1184_, 2, v___x_1183_);
lean_ctor_set_float(v___x_1184_, sizeof(void*)*3, v___x_1181_);
lean_ctor_set_float(v___x_1184_, sizeof(void*)*3 + 8, v___x_1181_);
lean_ctor_set_uint8(v___x_1184_, sizeof(void*)*3 + 16, v___x_1182_);
v___x_1185_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__2));
v___x_1186_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1184_);
lean_ctor_set(v___x_1186_, 1, v_a_1158_);
lean_ctor_set(v___x_1186_, 2, v___x_1185_);
lean_inc(v_ref_1156_);
v___x_1187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1187_, 0, v_ref_1156_);
lean_ctor_set(v___x_1187_, 1, v___x_1186_);
v___x_1188_ = l_Lean_PersistentArray_push___redArg(v_traces_1176_, v___x_1187_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v___x_1188_);
v___x_1190_ = v___x_1178_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1188_);
lean_ctor_set_uint64(v_reuseFailAlloc_1199_, sizeof(void*)*1, v_tid_1175_);
v___x_1190_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
lean_object* v___x_1192_; 
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 4, v___x_1190_);
v___x_1192_ = v___x_1173_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_env_1164_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v_nextMacroScope_1165_);
lean_ctor_set(v_reuseFailAlloc_1198_, 2, v_ngen_1166_);
lean_ctor_set(v_reuseFailAlloc_1198_, 3, v_auxDeclNGen_1167_);
lean_ctor_set(v_reuseFailAlloc_1198_, 4, v___x_1190_);
lean_ctor_set(v_reuseFailAlloc_1198_, 5, v_cache_1168_);
lean_ctor_set(v_reuseFailAlloc_1198_, 6, v_messages_1169_);
lean_ctor_set(v_reuseFailAlloc_1198_, 7, v_infoState_1170_);
lean_ctor_set(v_reuseFailAlloc_1198_, 8, v_snapshotTasks_1171_);
v___x_1192_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1196_; 
v___x_1193_ = lean_st_ref_put(v___y_1154_, v___x_1192_);
v___x_1194_ = lean_box(0);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 0, v___x_1194_);
v___x_1196_ = v___x_1160_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1194_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___boxed(lean_object* v_cls_1203_, lean_object* v_msg_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(v_cls_1203_, v_msg_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
return v_res_1210_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7(void){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1223_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4));
v___x_1224_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__6));
v___x_1225_ = l_Lean_Name_append(v___x_1224_, v___x_1223_);
return v___x_1225_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9(void){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__8));
v___x_1228_ = l_Lean_stringToMessageData(v___x_1227_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* lean_grind_cutsat_mk_var(lean_object* v_expr_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_){
_start:
{
lean_object* v___x_1241_; 
v___x_1241_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1230_, v_a_1238_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1371_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1244_ = v___x_1241_;
v_isShared_1245_ = v_isSharedCheck_1371_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1241_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1371_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v_varMap_1246_; lean_object* v___x_1247_; 
v_varMap_1246_ = lean_ctor_get(v_a_1242_, 1);
lean_inc_ref(v_varMap_1246_);
lean_dec(v_a_1242_);
v___x_1247_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(v_varMap_1246_, v_expr_1229_);
lean_dec_ref(v_varMap_1246_);
if (lean_obj_tag(v___x_1247_) == 1)
{
lean_object* v_val_1248_; lean_object* v___x_1250_; 
lean_dec(v_a_1239_);
lean_dec_ref(v_a_1238_);
lean_dec(v_a_1237_);
lean_dec_ref(v_a_1236_);
lean_dec(v_a_1235_);
lean_dec_ref(v_a_1234_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec(v_a_1231_);
lean_dec(v_a_1230_);
lean_dec_ref(v_expr_1229_);
v_val_1248_ = lean_ctor_get(v___x_1247_, 0);
lean_inc(v_val_1248_);
lean_dec_ref_known(v___x_1247_, 1);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 0, v_val_1248_);
v___x_1250_ = v___x_1244_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_val_1248_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
else
{
lean_object* v___x_1252_; 
lean_dec(v___x_1247_);
lean_del_object(v___x_1244_);
v___x_1252_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1230_, v_a_1238_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v_a_1253_; lean_object* v_vars_1254_; lean_object* v_toCold_1255_; lean_object* v_options_1256_; lean_object* v_size_1257_; lean_object* v_inheritedTraceOptions_1258_; uint8_t v_hasTrace_1259_; lean_object* v___f_1260_; lean_object* v___y_1262_; lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v___y_1265_; lean_object* v___y_1266_; lean_object* v___y_1267_; lean_object* v___y_1268_; lean_object* v___y_1269_; lean_object* v___y_1270_; lean_object* v___y_1271_; 
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
lean_inc(v_a_1253_);
lean_dec_ref_known(v___x_1252_, 1);
v_vars_1254_ = lean_ctor_get(v_a_1253_, 0);
lean_inc_ref(v_vars_1254_);
lean_dec(v_a_1253_);
v_toCold_1255_ = lean_ctor_get(v_a_1238_, 0);
v_options_1256_ = lean_ctor_get(v_toCold_1255_, 2);
v_size_1257_ = lean_ctor_get(v_vars_1254_, 2);
lean_inc_n(v_size_1257_, 2);
lean_dec_ref(v_vars_1254_);
v_inheritedTraceOptions_1258_ = lean_ctor_get(v_toCold_1255_, 11);
v_hasTrace_1259_ = lean_ctor_get_uint8(v_options_1256_, sizeof(void*)*1);
lean_inc_ref(v_expr_1229_);
v___f_1260_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0), 3, 2);
lean_closure_set(v___f_1260_, 0, v_expr_1229_);
lean_closure_set(v___f_1260_, 1, v_size_1257_);
if (v_hasTrace_1259_ == 0)
{
v___y_1262_ = v_a_1230_;
v___y_1263_ = v_a_1231_;
v___y_1264_ = v_a_1232_;
v___y_1265_ = v_a_1233_;
v___y_1266_ = v_a_1234_;
v___y_1267_ = v_a_1235_;
v___y_1268_ = v_a_1236_;
v___y_1269_ = v_a_1237_;
v___y_1270_ = v_a_1238_;
v___y_1271_ = v_a_1239_;
goto v___jp_1261_;
}
else
{
lean_object* v___x_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; 
v___x_1344_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4));
v___x_1345_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7);
v___x_1346_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1258_, v_options_1256_, v___x_1345_);
if (v___x_1346_ == 0)
{
v___y_1262_ = v_a_1230_;
v___y_1263_ = v_a_1231_;
v___y_1264_ = v_a_1232_;
v___y_1265_ = v_a_1233_;
v___y_1266_ = v_a_1234_;
v___y_1267_ = v_a_1235_;
v___y_1268_ = v_a_1236_;
v___y_1269_ = v_a_1237_;
v___y_1270_ = v_a_1238_;
v___y_1271_ = v_a_1239_;
goto v___jp_1261_;
}
else
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
lean_inc_ref(v_expr_1229_);
v___x_1347_ = l_Lean_MessageData_ofExpr(v_expr_1229_);
v___x_1348_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9);
v___x_1349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1347_);
lean_ctor_set(v___x_1349_, 1, v___x_1348_);
lean_inc(v_size_1257_);
v___x_1350_ = l_Nat_reprFast(v_size_1257_);
v___x_1351_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1350_);
v___x_1352_ = l_Lean_MessageData_ofFormat(v___x_1351_);
v___x_1353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1349_);
lean_ctor_set(v___x_1353_, 1, v___x_1352_);
v___x_1354_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(v___x_1344_, v___x_1353_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_dec_ref_known(v___x_1354_, 1);
v___y_1262_ = v_a_1230_;
v___y_1263_ = v_a_1231_;
v___y_1264_ = v_a_1232_;
v___y_1265_ = v_a_1233_;
v___y_1266_ = v_a_1234_;
v___y_1267_ = v_a_1235_;
v___y_1268_ = v_a_1236_;
v___y_1269_ = v_a_1237_;
v___y_1270_ = v_a_1238_;
v___y_1271_ = v_a_1239_;
goto v___jp_1261_;
}
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
lean_dec_ref(v___f_1260_);
lean_dec(v_size_1257_);
lean_dec(v_a_1239_);
lean_dec_ref(v_a_1238_);
lean_dec(v_a_1237_);
lean_dec_ref(v_a_1236_);
lean_dec(v_a_1235_);
lean_dec_ref(v_a_1234_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec(v_a_1231_);
lean_dec(v_a_1230_);
lean_dec_ref(v_expr_1229_);
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___x_1354_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1354_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
}
v___jp_1261_:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_1273_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1272_, v___f_1260_, v___y_1262_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v___x_1274_; 
lean_dec_ref_known(v___x_1273_, 1);
lean_inc_ref(v_expr_1229_);
v___x_1274_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_1272_, v_expr_1229_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v___x_1275_; 
lean_dec_ref_known(v___x_1274_, 1);
lean_inc(v_size_1257_);
lean_inc_ref(v_expr_1229_);
v___x_1275_ = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(v_expr_1229_, v_size_1257_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v___x_1276_; 
lean_dec_ref_known(v___x_1275_, 1);
lean_inc(v_size_1257_);
lean_inc_ref(v_expr_1229_);
v___x_1276_ = l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg(v_expr_1229_, v_size_1257_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v___x_1277_; 
lean_dec_ref_known(v___x_1276_, 1);
lean_inc_ref(v_expr_1229_);
v___x_1277_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm(v_expr_1229_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1303_; 
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1280_ = v___x_1277_;
v_isShared_1281_ = v_isSharedCheck_1303_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1277_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1303_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
uint8_t v___x_1282_; 
v___x_1282_ = lean_unbox(v_a_1278_);
lean_dec(v_a_1278_);
if (v___x_1282_ == 0)
{
lean_object* v___x_1284_; 
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec(v___y_1262_);
lean_dec_ref(v_expr_1229_);
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 0, v_size_1257_);
v___x_1284_ = v___x_1280_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_size_1257_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
else
{
lean_object* v___x_1286_; 
lean_del_object(v___x_1280_);
lean_inc(v_size_1257_);
v___x_1286_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt(v_expr_1229_, v_size_1257_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec(v___y_1262_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1293_ == 0)
{
lean_object* v_unused_1294_; 
v_unused_1294_ = lean_ctor_get(v___x_1286_, 0);
lean_dec(v_unused_1294_);
v___x_1288_ = v___x_1286_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_dec(v___x_1286_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 0, v_size_1257_);
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_size_1257_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
lean_dec(v_size_1257_);
v_a_1295_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1286_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1286_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
}
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec(v___y_1262_);
lean_dec(v_size_1257_);
lean_dec_ref(v_expr_1229_);
v_a_1304_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1277_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1277_);
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
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec(v___y_1262_);
lean_dec(v_size_1257_);
lean_dec_ref(v_expr_1229_);
v_a_1312_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1314_ = v___x_1276_;
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1276_);
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
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec(v___y_1262_);
lean_dec(v_size_1257_);
lean_dec_ref(v_expr_1229_);
v_a_1320_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1322_ = v___x_1275_;
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1275_);
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
else
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec(v___y_1262_);
lean_dec(v_size_1257_);
lean_dec_ref(v_expr_1229_);
v_a_1328_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1274_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1274_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
else
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1343_; 
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec(v___y_1262_);
lean_dec(v_size_1257_);
lean_dec_ref(v_expr_1229_);
v_a_1336_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1338_ = v___x_1273_;
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1273_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1341_; 
if (v_isShared_1339_ == 0)
{
v___x_1341_ = v___x_1338_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_a_1336_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
}
else
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
lean_dec(v_a_1239_);
lean_dec_ref(v_a_1238_);
lean_dec(v_a_1237_);
lean_dec_ref(v_a_1236_);
lean_dec(v_a_1235_);
lean_dec_ref(v_a_1234_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec(v_a_1231_);
lean_dec(v_a_1230_);
lean_dec_ref(v_expr_1229_);
v_a_1363_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1252_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1252_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1363_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
}
}
else
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
lean_dec(v_a_1239_);
lean_dec_ref(v_a_1238_);
lean_dec(v_a_1237_);
lean_dec_ref(v_a_1236_);
lean_dec(v_a_1235_);
lean_dec_ref(v_a_1234_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec(v_a_1231_);
lean_dec(v_a_1230_);
lean_dec_ref(v_expr_1229_);
v_a_1372_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1374_ = v___x_1241_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1241_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1377_; 
if (v_isShared_1375_ == 0)
{
v___x_1377_ = v___x_1374_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1372_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___boxed(lean_object* v_expr_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = lean_grind_cutsat_mk_var(v_expr_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0(lean_object* v_00_u03b2_1393_, lean_object* v_x_1394_, lean_object* v_x_1395_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(v_x_1394_, v_x_1395_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___boxed(lean_object* v_00_u03b2_1397_, lean_object* v_x_1398_, lean_object* v_x_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0(v_00_u03b2_1397_, v_x_1398_, v_x_1399_);
lean_dec_ref(v_x_1399_);
lean_dec_ref(v_x_1398_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1(lean_object* v_00_u03b2_1401_, lean_object* v_x_1402_, lean_object* v_x_1403_, lean_object* v_x_1404_){
_start:
{
lean_object* v___x_1405_; 
v___x_1405_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg(v_x_1402_, v_x_1403_, v_x_1404_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2(lean_object* v_cls_1406_, lean_object* v_msg_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v___x_1419_; 
v___x_1419_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(v_cls_1406_, v_msg_1407_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___boxed(lean_object* v_cls_1420_, lean_object* v_msg_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2(v_cls_1420_, v_msg_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v___y_1423_);
lean_dec(v___y_1422_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0(lean_object* v_00_u03b2_1434_, lean_object* v_x_1435_, size_t v_x_1436_, lean_object* v_x_1437_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(v_x_1435_, v_x_1436_, v_x_1437_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1439_, lean_object* v_x_1440_, lean_object* v_x_1441_, lean_object* v_x_1442_){
_start:
{
size_t v_x_28252__boxed_1443_; lean_object* v_res_1444_; 
v_x_28252__boxed_1443_ = lean_unbox_usize(v_x_1441_);
lean_dec(v_x_1441_);
v_res_1444_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0(v_00_u03b2_1439_, v_x_1440_, v_x_28252__boxed_1443_, v_x_1442_);
lean_dec_ref(v_x_1442_);
lean_dec_ref(v_x_1440_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2(lean_object* v_00_u03b2_1445_, lean_object* v_x_1446_, size_t v_x_1447_, size_t v_x_1448_, lean_object* v_x_1449_, lean_object* v_x_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_x_1446_, v_x_1447_, v_x_1448_, v_x_1449_, v_x_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1452_, lean_object* v_x_1453_, lean_object* v_x_1454_, lean_object* v_x_1455_, lean_object* v_x_1456_, lean_object* v_x_1457_){
_start:
{
size_t v_x_28263__boxed_1458_; size_t v_x_28264__boxed_1459_; lean_object* v_res_1460_; 
v_x_28263__boxed_1458_ = lean_unbox_usize(v_x_1454_);
lean_dec(v_x_1454_);
v_x_28264__boxed_1459_ = lean_unbox_usize(v_x_1455_);
lean_dec(v_x_1455_);
v_res_1460_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2(v_00_u03b2_1452_, v_x_1453_, v_x_28263__boxed_1458_, v_x_28264__boxed_1459_, v_x_1456_, v_x_1457_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1461_, lean_object* v_keys_1462_, lean_object* v_vals_1463_, lean_object* v_heq_1464_, lean_object* v_i_1465_, lean_object* v_k_1466_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(v_keys_1462_, v_vals_1463_, v_i_1465_, v_k_1466_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1468_, lean_object* v_keys_1469_, lean_object* v_vals_1470_, lean_object* v_heq_1471_, lean_object* v_i_1472_, lean_object* v_k_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1(v_00_u03b2_1468_, v_keys_1469_, v_vals_1470_, v_heq_1471_, v_i_1472_, v_k_1473_);
lean_dec_ref(v_k_1473_);
lean_dec_ref(v_vals_1470_);
lean_dec_ref(v_keys_1469_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1475_, lean_object* v_n_1476_, lean_object* v_k_1477_, lean_object* v_v_1478_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4___redArg(v_n_1476_, v_k_1477_, v_v_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1480_, size_t v_depth_1481_, lean_object* v_keys_1482_, lean_object* v_vals_1483_, lean_object* v_heq_1484_, lean_object* v_i_1485_, lean_object* v_entries_1486_){
_start:
{
lean_object* v___x_1487_; 
v___x_1487_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(v_depth_1481_, v_keys_1482_, v_vals_1483_, v_i_1485_, v_entries_1486_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1488_, lean_object* v_depth_1489_, lean_object* v_keys_1490_, lean_object* v_vals_1491_, lean_object* v_heq_1492_, lean_object* v_i_1493_, lean_object* v_entries_1494_){
_start:
{
size_t v_depth_boxed_1495_; lean_object* v_res_1496_; 
v_depth_boxed_1495_ = lean_unbox_usize(v_depth_1489_);
lean_dec(v_depth_1489_);
v_res_1496_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5(v_00_u03b2_1488_, v_depth_boxed_1495_, v_keys_1490_, v_vals_1491_, v_heq_1492_, v_i_1493_, v_entries_1494_);
lean_dec_ref(v_vals_1491_);
lean_dec_ref(v_keys_1490_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_1497_, lean_object* v_x_1498_, lean_object* v_x_1499_, lean_object* v_x_1500_, lean_object* v_x_1501_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7___redArg(v_x_1498_, v_x_1499_, v_x_1500_, v_x_1501_);
return v___x_1502_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2(void){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1506_ = lean_box(0);
v___x_1507_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__1));
v___x_1508_ = l_Lean_mkConst(v___x_1507_, v___x_1506_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(lean_object* v_e_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_){
_start:
{
lean_object* v___x_1515_; 
lean_inc(v_a_1513_);
lean_inc_ref(v_a_1512_);
lean_inc(v_a_1511_);
lean_inc_ref(v_a_1510_);
v___x_1515_ = lean_infer_type(v_e_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v_a_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_a_1516_);
lean_dec_ref_known(v___x_1515_, 1);
v___x_1517_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2);
v___x_1518_ = l_Lean_Meta_isExprDefEq(v_a_1516_, v___x_1517_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
return v___x_1518_;
}
else
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1526_; 
v_a_1519_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1521_ = v___x_1515_;
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v___x_1515_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
if (v_isShared_1522_ == 0)
{
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1519_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___boxed(lean_object* v_e_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(v_e_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_);
lean_dec(v_a_1531_);
lean_dec_ref(v_a_1530_);
lean_dec(v_a_1529_);
lean_dec_ref(v_a_1528_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt(lean_object* v_e_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_){
_start:
{
lean_object* v___x_1546_; 
v___x_1546_ = l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(v_e_1534_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___boxed(lean_object* v_e_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l_Lean_Meta_Grind_Arith_Cutsat_isInt(v_e_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_);
lean_dec(v_a_1557_);
lean_dec_ref(v_a_1556_);
lean_dec(v_a_1555_);
lean_dec_ref(v_a_1554_);
lean_dec(v_a_1553_);
lean_dec_ref(v_a_1552_);
lean_dec(v_a_1551_);
lean_dec_ref(v_a_1550_);
lean_dec(v_a_1549_);
lean_dec(v_a_1548_);
return v_res_1559_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4(void){
_start:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1566_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__3));
v___x_1567_ = l_Lean_stringToMessageData(v___x_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(lean_object* v_e_1568_, uint8_t v_report_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_){
_start:
{
lean_object* v___x_1580_; 
lean_inc_ref(v_e_1568_);
v___x_1580_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1568_, v_a_1573_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1651_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1583_ = v___x_1580_;
v_isShared_1584_ = v_isSharedCheck_1651_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1580_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1651_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1590_; uint8_t v___x_1591_; 
v___x_1590_ = l_Lean_Expr_cleanupAnnotations(v_a_1581_);
v___x_1591_ = l_Lean_Expr_isApp(v___x_1590_);
if (v___x_1591_ == 0)
{
lean_dec_ref(v___x_1590_);
lean_dec_ref(v_e_1568_);
goto v___jp_1585_;
}
else
{
lean_object* v_arg_1592_; lean_object* v___x_1593_; uint8_t v___x_1594_; 
v_arg_1592_ = lean_ctor_get(v___x_1590_, 1);
lean_inc_ref(v_arg_1592_);
v___x_1593_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1590_);
v___x_1594_ = l_Lean_Expr_isApp(v___x_1593_);
if (v___x_1594_ == 0)
{
lean_dec_ref(v___x_1593_);
lean_dec_ref(v_arg_1592_);
lean_dec_ref(v_e_1568_);
goto v___jp_1585_;
}
else
{
lean_object* v_arg_1595_; lean_object* v___x_1596_; uint8_t v___x_1597_; 
v_arg_1595_ = lean_ctor_get(v___x_1593_, 1);
lean_inc_ref(v_arg_1595_);
v___x_1596_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1593_);
v___x_1597_ = l_Lean_Expr_isApp(v___x_1596_);
if (v___x_1597_ == 0)
{
lean_dec_ref(v___x_1596_);
lean_dec_ref(v_arg_1595_);
lean_dec_ref(v_arg_1592_);
lean_dec_ref(v_e_1568_);
goto v___jp_1585_;
}
else
{
lean_object* v_arg_1598_; lean_object* v___x_1599_; uint8_t v___x_1600_; 
v_arg_1598_ = lean_ctor_get(v___x_1596_, 1);
lean_inc_ref(v_arg_1598_);
v___x_1599_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1596_);
v___x_1600_ = l_Lean_Expr_isApp(v___x_1599_);
if (v___x_1600_ == 0)
{
lean_dec_ref(v___x_1599_);
lean_dec_ref(v_arg_1598_);
lean_dec_ref(v_arg_1595_);
lean_dec_ref(v_arg_1592_);
lean_dec_ref(v_e_1568_);
goto v___jp_1585_;
}
else
{
lean_object* v___x_1601_; uint8_t v___x_1602_; 
v___x_1601_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1599_);
v___x_1602_ = l_Lean_Expr_isApp(v___x_1601_);
if (v___x_1602_ == 0)
{
lean_dec_ref(v___x_1601_);
lean_dec_ref(v_arg_1598_);
lean_dec_ref(v_arg_1595_);
lean_dec_ref(v_arg_1592_);
lean_dec_ref(v_e_1568_);
goto v___jp_1585_;
}
else
{
lean_object* v___x_1603_; uint8_t v___x_1604_; 
v___x_1603_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1601_);
v___x_1604_ = l_Lean_Expr_isApp(v___x_1603_);
if (v___x_1604_ == 0)
{
lean_dec_ref(v___x_1603_);
lean_dec_ref(v_arg_1598_);
lean_dec_ref(v_arg_1595_);
lean_dec_ref(v_arg_1592_);
lean_dec_ref(v_e_1568_);
goto v___jp_1585_;
}
else
{
lean_object* v___x_1605_; lean_object* v___x_1606_; uint8_t v___x_1607_; 
v___x_1605_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1603_);
v___x_1606_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__2));
v___x_1607_ = l_Lean_Expr_isConstOf(v___x_1605_, v___x_1606_);
lean_dec_ref(v___x_1605_);
if (v___x_1607_ == 0)
{
lean_dec_ref(v_arg_1598_);
lean_dec_ref(v_arg_1595_);
lean_dec_ref(v_arg_1592_);
lean_dec_ref(v_e_1568_);
goto v___jp_1585_;
}
else
{
lean_object* v___x_1608_; 
lean_del_object(v___x_1583_);
v___x_1608_ = l_Lean_Meta_Structural_isInstHAddInt___redArg(v_arg_1598_, v_a_1573_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1642_; 
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1611_ = v___x_1608_;
v_isShared_1612_ = v_isSharedCheck_1642_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1608_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1642_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
uint8_t v___x_1613_; 
v___x_1613_ = lean_unbox(v_a_1609_);
lean_dec(v_a_1609_);
if (v___x_1613_ == 0)
{
lean_del_object(v___x_1611_);
lean_dec_ref(v_arg_1595_);
lean_dec_ref(v_arg_1592_);
if (v_report_1569_ == 0)
{
lean_dec_ref(v_e_1568_);
goto v___jp_1577_;
}
else
{
lean_object* v___x_1614_; 
v___x_1614_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1570_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_a_1615_; uint8_t v_verbose_1616_; 
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_a_1615_);
lean_dec_ref_known(v___x_1614_, 1);
v_verbose_1616_ = lean_ctor_get_uint8(v_a_1615_, 0);
lean_dec(v_a_1615_);
if (v_verbose_1616_ == 0)
{
lean_dec_ref(v_e_1568_);
goto v___jp_1577_;
}
else
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1617_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4);
v___x_1618_ = l_Lean_indentExpr(v_e_1568_);
v___x_1619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1617_);
lean_ctor_set(v___x_1619_, 1, v___x_1618_);
v___x_1620_ = l_Lean_Meta_Sym_reportIssue(v___x_1619_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_dec_ref_known(v___x_1620_, 1);
goto v___jp_1577_;
}
else
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1623_ = v___x_1620_;
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1620_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1626_; 
if (v_isShared_1624_ == 0)
{
v___x_1626_ = v___x_1623_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
}
else
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1636_; 
lean_dec_ref(v_e_1568_);
v_a_1629_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1631_ = v___x_1614_;
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1614_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1634_; 
if (v_isShared_1632_ == 0)
{
v___x_1634_ = v___x_1631_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_a_1629_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
}
}
else
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1640_; 
lean_dec_ref(v_e_1568_);
v___x_1637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1637_, 0, v_arg_1595_);
lean_ctor_set(v___x_1637_, 1, v_arg_1592_);
v___x_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1637_);
if (v_isShared_1612_ == 0)
{
lean_ctor_set(v___x_1611_, 0, v___x_1638_);
v___x_1640_ = v___x_1611_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v___x_1638_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
}
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
lean_dec_ref(v_arg_1595_);
lean_dec_ref(v_arg_1592_);
lean_dec_ref(v_e_1568_);
v_a_1643_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1608_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1608_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
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
v___jp_1585_:
{
lean_object* v___x_1586_; lean_object* v___x_1588_; 
v___x_1586_ = lean_box(0);
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 0, v___x_1586_);
v___x_1588_ = v___x_1583_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1586_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
else
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
lean_dec_ref(v_e_1568_);
v_a_1652_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1580_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1580_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
v___jp_1577_:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1578_ = lean_box(0);
v___x_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1578_);
return v___x_1579_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___boxed(lean_object* v_e_1660_, lean_object* v_report_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_){
_start:
{
uint8_t v_report_boxed_1669_; lean_object* v_res_1670_; 
v_report_boxed_1669_ = lean_unbox(v_report_1661_);
v_res_1670_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_1660_, v_report_boxed_1669_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_);
lean_dec(v_a_1667_);
lean_dec_ref(v_a_1666_);
lean_dec(v_a_1665_);
lean_dec_ref(v_a_1664_);
lean_dec(v_a_1663_);
lean_dec_ref(v_a_1662_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f(lean_object* v_e_1671_, uint8_t v_report_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_){
_start:
{
lean_object* v___x_1684_; 
v___x_1684_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_1671_, v_report_1672_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___boxed(lean_object* v_e_1685_, lean_object* v_report_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_){
_start:
{
uint8_t v_report_boxed_1698_; lean_object* v_res_1699_; 
v_report_boxed_1698_ = lean_unbox(v_report_1686_);
v_res_1699_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f(v_e_1685_, v_report_boxed_1698_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_);
lean_dec(v_a_1696_);
lean_dec_ref(v_a_1695_);
lean_dec(v_a_1694_);
lean_dec_ref(v_a_1693_);
lean_dec(v_a_1692_);
lean_dec_ref(v_a_1691_);
lean_dec(v_a_1690_);
lean_dec_ref(v_a_1689_);
lean_dec(v_a_1688_);
lean_dec(v_a_1687_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(lean_object* v_e_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_){
_start:
{
uint8_t v___x_1708_; lean_object* v___x_1709_; 
v___x_1708_ = 0;
v___x_1709_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_1700_, v___x_1708_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_);
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1723_; 
v_a_1710_ = lean_ctor_get(v___x_1709_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1712_ = v___x_1709_;
v_isShared_1713_ = v_isSharedCheck_1723_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1709_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1723_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
if (lean_obj_tag(v_a_1710_) == 0)
{
lean_object* v___x_1714_; lean_object* v___x_1716_; 
v___x_1714_ = lean_box(v___x_1708_);
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 0, v___x_1714_);
v___x_1716_ = v___x_1712_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v___x_1714_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
else
{
uint8_t v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1721_; 
lean_dec_ref_known(v_a_1710_, 1);
v___x_1718_ = 1;
v___x_1719_ = lean_box(v___x_1718_);
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 0, v___x_1719_);
v___x_1721_ = v___x_1712_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1719_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
}
else
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
v_a_1724_ = lean_ctor_get(v___x_1709_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1726_ = v___x_1709_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1709_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg___boxed(lean_object* v_e_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(v_e_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_);
lean_dec(v_a_1738_);
lean_dec_ref(v_a_1737_);
lean_dec(v_a_1736_);
lean_dec_ref(v_a_1735_);
lean_dec(v_a_1734_);
lean_dec_ref(v_a_1733_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd(lean_object* v_e_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_){
_start:
{
lean_object* v___x_1753_; 
v___x_1753_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(v_e_1741_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___boxed(lean_object* v_e_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd(v_e_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_);
lean_dec(v_a_1764_);
lean_dec_ref(v_a_1763_);
lean_dec(v_a_1762_);
lean_dec_ref(v_a_1761_);
lean_dec(v_a_1760_);
lean_dec_ref(v_a_1759_);
lean_dec(v_a_1758_);
lean_dec_ref(v_a_1757_);
lean_dec(v_a_1756_);
lean_dec(v_a_1755_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(lean_object* v_e_1767_, uint8_t v_report_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_){
_start:
{
lean_object* v___x_1779_; 
lean_inc_ref(v_e_1767_);
v___x_1779_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1767_, v_a_1772_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1871_; 
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1782_ = v___x_1779_;
v_isShared_1783_ = v_isSharedCheck_1871_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1779_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1871_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1789_; uint8_t v___x_1790_; 
v___x_1789_ = l_Lean_Expr_cleanupAnnotations(v_a_1780_);
v___x_1790_ = l_Lean_Expr_isApp(v___x_1789_);
if (v___x_1790_ == 0)
{
lean_dec_ref(v___x_1789_);
lean_dec_ref(v_e_1767_);
goto v___jp_1784_;
}
else
{
lean_object* v_arg_1791_; lean_object* v___x_1792_; uint8_t v___x_1793_; 
v_arg_1791_ = lean_ctor_get(v___x_1789_, 1);
lean_inc_ref(v_arg_1791_);
v___x_1792_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1789_);
v___x_1793_ = l_Lean_Expr_isApp(v___x_1792_);
if (v___x_1793_ == 0)
{
lean_dec_ref(v___x_1792_);
lean_dec_ref(v_arg_1791_);
lean_dec_ref(v_e_1767_);
goto v___jp_1784_;
}
else
{
lean_object* v_arg_1794_; lean_object* v___x_1795_; uint8_t v___x_1796_; 
v_arg_1794_ = lean_ctor_get(v___x_1792_, 1);
lean_inc_ref(v_arg_1794_);
v___x_1795_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1792_);
v___x_1796_ = l_Lean_Expr_isApp(v___x_1795_);
if (v___x_1796_ == 0)
{
lean_dec_ref(v___x_1795_);
lean_dec_ref(v_arg_1794_);
lean_dec_ref(v_arg_1791_);
lean_dec_ref(v_e_1767_);
goto v___jp_1784_;
}
else
{
lean_object* v_arg_1797_; lean_object* v___x_1798_; uint8_t v___x_1799_; 
v_arg_1797_ = lean_ctor_get(v___x_1795_, 1);
lean_inc_ref(v_arg_1797_);
v___x_1798_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1795_);
v___x_1799_ = l_Lean_Expr_isApp(v___x_1798_);
if (v___x_1799_ == 0)
{
lean_dec_ref(v___x_1798_);
lean_dec_ref(v_arg_1797_);
lean_dec_ref(v_arg_1794_);
lean_dec_ref(v_arg_1791_);
lean_dec_ref(v_e_1767_);
goto v___jp_1784_;
}
else
{
lean_object* v___x_1800_; uint8_t v___x_1801_; 
v___x_1800_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1798_);
v___x_1801_ = l_Lean_Expr_isApp(v___x_1800_);
if (v___x_1801_ == 0)
{
lean_dec_ref(v___x_1800_);
lean_dec_ref(v_arg_1797_);
lean_dec_ref(v_arg_1794_);
lean_dec_ref(v_arg_1791_);
lean_dec_ref(v_e_1767_);
goto v___jp_1784_;
}
else
{
lean_object* v___x_1802_; uint8_t v___x_1803_; 
v___x_1802_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1800_);
v___x_1803_ = l_Lean_Expr_isApp(v___x_1802_);
if (v___x_1803_ == 0)
{
lean_dec_ref(v___x_1802_);
lean_dec_ref(v_arg_1797_);
lean_dec_ref(v_arg_1794_);
lean_dec_ref(v_arg_1791_);
lean_dec_ref(v_e_1767_);
goto v___jp_1784_;
}
else
{
lean_object* v___x_1804_; lean_object* v___x_1805_; uint8_t v___x_1806_; 
v___x_1804_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1802_);
v___x_1805_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11));
v___x_1806_ = l_Lean_Expr_isConstOf(v___x_1804_, v___x_1805_);
lean_dec_ref(v___x_1804_);
if (v___x_1806_ == 0)
{
lean_dec_ref(v_arg_1797_);
lean_dec_ref(v_arg_1794_);
lean_dec_ref(v_arg_1791_);
lean_dec_ref(v_e_1767_);
goto v___jp_1784_;
}
else
{
lean_object* v___x_1807_; 
lean_del_object(v___x_1782_);
v___x_1807_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_1797_, v_a_1772_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_a_1808_; uint8_t v___x_1809_; 
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
lean_inc(v_a_1808_);
lean_dec_ref_known(v___x_1807_, 1);
v___x_1809_ = lean_unbox(v_a_1808_);
lean_dec(v_a_1808_);
if (v___x_1809_ == 0)
{
lean_dec_ref(v_arg_1794_);
lean_dec_ref(v_arg_1791_);
if (v_report_1768_ == 0)
{
lean_dec_ref(v_e_1767_);
goto v___jp_1776_;
}
else
{
lean_object* v___x_1810_; 
v___x_1810_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1769_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; uint8_t v_verbose_1812_; 
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
lean_inc(v_a_1811_);
lean_dec_ref_known(v___x_1810_, 1);
v_verbose_1812_ = lean_ctor_get_uint8(v_a_1811_, 0);
lean_dec(v_a_1811_);
if (v_verbose_1812_ == 0)
{
lean_dec_ref(v_e_1767_);
goto v___jp_1776_;
}
else
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1813_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4);
v___x_1814_ = l_Lean_indentExpr(v_e_1767_);
v___x_1815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1813_);
lean_ctor_set(v___x_1815_, 1, v___x_1814_);
v___x_1816_ = l_Lean_Meta_Sym_reportIssue(v___x_1815_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_, v_a_1773_, v_a_1774_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_dec_ref_known(v___x_1816_, 1);
goto v___jp_1776_;
}
else
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1824_; 
v_a_1817_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1819_ = v___x_1816_;
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1816_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1822_; 
if (v_isShared_1820_ == 0)
{
v___x_1822_ = v___x_1819_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_a_1817_);
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
}
else
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1832_; 
lean_dec_ref(v_e_1767_);
v_a_1825_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1827_ = v___x_1810_;
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1810_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1830_; 
if (v_isShared_1828_ == 0)
{
v___x_1830_ = v___x_1827_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1825_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
}
}
else
{
lean_object* v___x_1833_; 
lean_dec_ref(v_e_1767_);
v___x_1833_ = l_Lean_Meta_getIntValue_x3f(v_arg_1794_, v_a_1771_, v_a_1772_, v_a_1773_, v_a_1774_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1854_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1836_ = v___x_1833_;
v_isShared_1837_ = v_isSharedCheck_1854_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1833_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1854_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
if (lean_obj_tag(v_a_1834_) == 1)
{
lean_object* v_val_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1849_; 
v_val_1838_ = lean_ctor_get(v_a_1834_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v_a_1834_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1840_ = v_a_1834_;
v_isShared_1841_ = v_isSharedCheck_1849_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_val_1838_);
lean_dec(v_a_1834_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1849_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1842_; lean_object* v___x_1844_; 
v___x_1842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1842_, 0, v_val_1838_);
lean_ctor_set(v___x_1842_, 1, v_arg_1791_);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v___x_1842_);
v___x_1844_ = v___x_1840_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
lean_object* v___x_1846_; 
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 0, v___x_1844_);
v___x_1846_ = v___x_1836_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v___x_1844_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
}
else
{
lean_object* v___x_1850_; lean_object* v___x_1852_; 
lean_dec(v_a_1834_);
lean_dec_ref(v_arg_1791_);
v___x_1850_ = lean_box(0);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 0, v___x_1850_);
v___x_1852_ = v___x_1836_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1850_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
else
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1862_; 
lean_dec_ref(v_arg_1791_);
v_a_1855_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1857_ = v___x_1833_;
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1833_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1855_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
}
}
else
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1870_; 
lean_dec_ref(v_arg_1794_);
lean_dec_ref(v_arg_1791_);
lean_dec_ref(v_e_1767_);
v_a_1863_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1865_ = v___x_1807_;
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1807_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1868_; 
if (v_isShared_1866_ == 0)
{
v___x_1868_ = v___x_1865_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1863_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
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
v___jp_1784_:
{
lean_object* v___x_1785_; lean_object* v___x_1787_; 
v___x_1785_ = lean_box(0);
if (v_isShared_1783_ == 0)
{
lean_ctor_set(v___x_1782_, 0, v___x_1785_);
v___x_1787_ = v___x_1782_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1785_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
}
else
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1879_; 
lean_dec_ref(v_e_1767_);
v_a_1872_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1874_ = v___x_1779_;
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1779_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1877_; 
if (v_isShared_1875_ == 0)
{
v___x_1877_ = v___x_1874_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_a_1872_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
v___jp_1776_:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1777_ = lean_box(0);
v___x_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1777_);
return v___x_1778_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg___boxed(lean_object* v_e_1880_, lean_object* v_report_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_){
_start:
{
uint8_t v_report_boxed_1889_; lean_object* v_res_1890_; 
v_report_boxed_1889_ = lean_unbox(v_report_1881_);
v_res_1890_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1880_, v_report_boxed_1889_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_);
lean_dec(v_a_1887_);
lean_dec_ref(v_a_1886_);
lean_dec(v_a_1885_);
lean_dec_ref(v_a_1884_);
lean_dec(v_a_1883_);
lean_dec_ref(v_a_1882_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f(lean_object* v_e_1891_, uint8_t v_report_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_){
_start:
{
lean_object* v___x_1904_; 
v___x_1904_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1891_, v_report_1892_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___boxed(lean_object* v_e_1905_, lean_object* v_report_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_){
_start:
{
uint8_t v_report_boxed_1918_; lean_object* v_res_1919_; 
v_report_boxed_1918_ = lean_unbox(v_report_1906_);
v_res_1919_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f(v_e_1905_, v_report_boxed_1918_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_);
lean_dec(v_a_1916_);
lean_dec_ref(v_a_1915_);
lean_dec(v_a_1914_);
lean_dec_ref(v_a_1913_);
lean_dec(v_a_1912_);
lean_dec_ref(v_a_1911_);
lean_dec(v_a_1910_);
lean_dec_ref(v_a_1909_);
lean_dec(v_a_1908_);
lean_dec(v_a_1907_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(lean_object* v_e_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_){
_start:
{
uint8_t v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = 0;
v___x_1929_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1920_, v___x_1928_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1943_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1932_ = v___x_1929_;
v_isShared_1933_ = v_isSharedCheck_1943_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1929_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1943_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
if (lean_obj_tag(v_a_1930_) == 0)
{
lean_object* v___x_1934_; lean_object* v___x_1936_; 
v___x_1934_ = lean_box(v___x_1928_);
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 0, v___x_1934_);
v___x_1936_ = v___x_1932_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1934_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
else
{
uint8_t v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1941_; 
lean_dec_ref_known(v_a_1930_, 1);
v___x_1938_ = 1;
v___x_1939_ = lean_box(v___x_1938_);
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 0, v___x_1939_);
v___x_1941_ = v___x_1932_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v___x_1939_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
}
else
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
v_a_1944_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v___x_1929_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1929_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg___boxed(lean_object* v_e_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(v_e_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_);
lean_dec(v_a_1958_);
lean_dec_ref(v_a_1957_);
lean_dec(v_a_1956_);
lean_dec_ref(v_a_1955_);
lean_dec(v_a_1954_);
lean_dec_ref(v_a_1953_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul(lean_object* v_e_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_){
_start:
{
lean_object* v___x_1973_; 
v___x_1973_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(v_e_1961_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___boxed(lean_object* v_e_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul(v_e_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_);
lean_dec(v_a_1984_);
lean_dec_ref(v_a_1983_);
lean_dec(v_a_1982_);
lean_dec_ref(v_a_1981_);
lean_dec(v_a_1980_);
lean_dec_ref(v_a_1979_);
lean_dec(v_a_1978_);
lean_dec_ref(v_a_1977_);
lean_dec(v_a_1976_);
lean_dec(v_a_1975_);
return v_res_1986_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0(void){
_start:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1987_ = lean_unsigned_to_nat(1u);
v___x_1988_ = lean_nat_to_int(v___x_1987_);
return v___x_1988_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2(void){
_start:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1990_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__1));
v___x_1991_ = l_Lean_stringToMessageData(v___x_1990_);
return v___x_1991_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4(void){
_start:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1993_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__3));
v___x_1994_ = l_Lean_stringToMessageData(v___x_1993_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(lean_object* v_e_1995_, lean_object* v_p_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_){
_start:
{
lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; uint8_t v___x_2038_; lean_object* v___x_2039_; 
v___x_2038_ = 1;
lean_inc_ref(v_e_1995_);
v___x_2039_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1995_, v___x_2038_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_a_2040_);
lean_dec_ref_known(v___x_2039_, 1);
if (lean_obj_tag(v_a_2040_) == 1)
{
lean_object* v_val_2041_; lean_object* v_fst_2042_; lean_object* v_snd_2043_; lean_object* v___x_2044_; 
lean_dec_ref(v_e_1995_);
v_val_2041_ = lean_ctor_get(v_a_2040_, 0);
lean_inc(v_val_2041_);
lean_dec_ref_known(v_a_2040_, 1);
v_fst_2042_ = lean_ctor_get(v_val_2041_, 0);
lean_inc(v_fst_2042_);
v_snd_2043_ = lean_ctor_get(v_val_2041_, 1);
lean_inc(v_snd_2043_);
lean_dec(v_val_2041_);
lean_inc(v_a_2006_);
lean_inc_ref(v_a_2005_);
lean_inc(v_a_2004_);
lean_inc_ref(v_a_2003_);
lean_inc(v_a_2002_);
lean_inc_ref(v_a_2001_);
lean_inc(v_a_2000_);
lean_inc_ref(v_a_1999_);
lean_inc(v_a_1998_);
lean_inc(v_a_1997_);
v___x_2044_ = lean_grind_cutsat_mk_var(v_snd_2043_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2053_; 
v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2047_ = v___x_2044_;
v_isShared_2048_ = v_isSharedCheck_2053_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_2044_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2053_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2049_; lean_object* v___x_2051_; 
v___x_2049_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2049_, 0, v_fst_2042_);
lean_ctor_set(v___x_2049_, 1, v_a_2045_);
lean_ctor_set(v___x_2049_, 2, v_p_1996_);
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 0, v___x_2049_);
v___x_2051_ = v___x_2047_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v___x_2049_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
else
{
lean_object* v_a_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2061_; 
lean_dec(v_fst_2042_);
lean_dec_ref(v_p_1996_);
v_a_2054_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2056_ = v___x_2044_;
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_a_2054_);
lean_dec(v___x_2044_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2059_; 
if (v_isShared_2057_ == 0)
{
v___x_2059_ = v___x_2056_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_a_2054_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
}
else
{
lean_object* v___x_2062_; 
lean_dec(v_a_2040_);
lean_inc_ref(v_e_1995_);
v___x_2062_ = l_Lean_Meta_getIntValue_x3f(v_e_1995_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2104_; 
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2065_ = v___x_2062_;
v_isShared_2066_ = v_isSharedCheck_2104_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2062_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2104_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
if (lean_obj_tag(v_a_2063_) == 1)
{
lean_object* v_val_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2103_; 
v_val_2067_ = lean_ctor_get(v_a_2063_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v_a_2063_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2069_ = v_a_2063_;
v_isShared_2070_ = v_isSharedCheck_2103_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_val_2067_);
lean_dec(v_a_2063_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2103_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
uint8_t v___x_2071_; 
v___x_2071_ = l_Int_Internal_Linear_Poly_isZero(v_p_1996_);
if (v___x_2071_ == 0)
{
lean_object* v___x_2072_; 
lean_del_object(v___x_2069_);
lean_dec(v_val_2067_);
lean_del_object(v___x_2065_);
v___x_2072_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_2001_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v_a_2073_; uint8_t v_verbose_2074_; 
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
lean_inc(v_a_2073_);
lean_dec_ref_known(v___x_2072_, 1);
v_verbose_2074_ = lean_ctor_get_uint8(v_a_2073_, 0);
lean_dec(v_a_2073_);
if (v_verbose_2074_ == 0)
{
v___y_2009_ = v_a_1997_;
v___y_2010_ = v_a_1998_;
v___y_2011_ = v_a_1999_;
v___y_2012_ = v_a_2000_;
v___y_2013_ = v_a_2001_;
v___y_2014_ = v_a_2002_;
v___y_2015_ = v_a_2003_;
v___y_2016_ = v_a_2004_;
v___y_2017_ = v_a_2005_;
v___y_2018_ = v_a_2006_;
goto v___jp_2008_;
}
else
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2075_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2);
lean_inc_ref(v_e_1995_);
v___x_2076_ = l_Lean_indentExpr(v_e_1995_);
v___x_2077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2075_);
lean_ctor_set(v___x_2077_, 1, v___x_2076_);
v___x_2078_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4);
v___x_2079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2077_);
lean_ctor_set(v___x_2079_, 1, v___x_2078_);
v___x_2080_ = l_Lean_Meta_Sym_reportIssue(v___x_2079_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_dec_ref_known(v___x_2080_, 1);
v___y_2009_ = v_a_1997_;
v___y_2010_ = v_a_1998_;
v___y_2011_ = v_a_1999_;
v___y_2012_ = v_a_2000_;
v___y_2013_ = v_a_2001_;
v___y_2014_ = v_a_2002_;
v___y_2015_ = v_a_2003_;
v___y_2016_ = v_a_2004_;
v___y_2017_ = v_a_2005_;
v___y_2018_ = v_a_2006_;
goto v___jp_2008_;
}
else
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2088_; 
lean_dec_ref(v_p_1996_);
lean_dec_ref(v_e_1995_);
v_a_2081_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2083_ = v___x_2080_;
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_2080_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2084_ == 0)
{
v___x_2086_ = v___x_2083_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2081_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
}
else
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
lean_dec_ref(v_p_1996_);
lean_dec_ref(v_e_1995_);
v_a_2089_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2072_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2072_);
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
else
{
lean_object* v___x_2098_; 
lean_dec_ref(v_p_1996_);
lean_dec_ref(v_e_1995_);
if (v_isShared_2070_ == 0)
{
lean_ctor_set_tag(v___x_2069_, 0);
v___x_2098_ = v___x_2069_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_val_2067_);
v___x_2098_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
lean_object* v___x_2100_; 
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 0, v___x_2098_);
v___x_2100_ = v___x_2065_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v___x_2098_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
}
else
{
lean_del_object(v___x_2065_);
lean_dec(v_a_2063_);
v___y_2009_ = v_a_1997_;
v___y_2010_ = v_a_1998_;
v___y_2011_ = v_a_1999_;
v___y_2012_ = v_a_2000_;
v___y_2013_ = v_a_2001_;
v___y_2014_ = v_a_2002_;
v___y_2015_ = v_a_2003_;
v___y_2016_ = v_a_2004_;
v___y_2017_ = v_a_2005_;
v___y_2018_ = v_a_2006_;
goto v___jp_2008_;
}
}
}
else
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
lean_dec_ref(v_p_1996_);
lean_dec_ref(v_e_1995_);
v_a_2105_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2107_ = v___x_2062_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_2062_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2105_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
}
else
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2120_; 
lean_dec_ref(v_p_1996_);
lean_dec_ref(v_e_1995_);
v_a_2113_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2115_ = v___x_2039_;
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2039_);
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
v___jp_2008_:
{
lean_object* v___x_2019_; 
lean_inc(v___y_2018_);
lean_inc_ref(v___y_2017_);
lean_inc(v___y_2016_);
lean_inc_ref(v___y_2015_);
lean_inc(v___y_2014_);
lean_inc_ref(v___y_2013_);
lean_inc(v___y_2012_);
lean_inc_ref(v___y_2011_);
lean_inc(v___y_2010_);
lean_inc(v___y_2009_);
v___x_2019_ = lean_grind_cutsat_mk_var(v_e_1995_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2029_; 
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2022_ = v___x_2019_;
v_isShared_2023_ = v_isSharedCheck_2029_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_2019_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2029_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2027_; 
v___x_2024_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0);
v___x_2025_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2024_);
lean_ctor_set(v___x_2025_, 1, v_a_2020_);
lean_ctor_set(v___x_2025_, 2, v_p_1996_);
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 0, v___x_2025_);
v___x_2027_ = v___x_2022_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2025_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
else
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2037_; 
lean_dec_ref(v_p_1996_);
v_a_2030_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2032_ = v___x_2019_;
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_2019_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2033_ == 0)
{
v___x_2035_ = v___x_2032_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_a_2030_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___boxed(lean_object* v_e_2121_, lean_object* v_p_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_){
_start:
{
lean_object* v_res_2134_; 
v_res_2134_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_e_2121_, v_p_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_);
lean_dec(v_a_2132_);
lean_dec_ref(v_a_2131_);
lean_dec(v_a_2130_);
lean_dec_ref(v_a_2129_);
lean_dec(v_a_2128_);
lean_dec_ref(v_a_2127_);
lean_dec(v_a_2126_);
lean_dec_ref(v_a_2125_);
lean_dec(v_a_2124_);
lean_dec(v_a_2123_);
return v_res_2134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go(lean_object* v_e_2135_, lean_object* v_p_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_){
_start:
{
uint8_t v___x_2148_; lean_object* v___x_2149_; 
v___x_2148_ = 1;
lean_inc_ref(v_e_2135_);
v___x_2149_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_2135_, v___x_2148_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_a_2150_);
lean_dec_ref_known(v___x_2149_, 1);
if (lean_obj_tag(v_a_2150_) == 1)
{
lean_object* v_val_2151_; lean_object* v_fst_2152_; lean_object* v_snd_2153_; lean_object* v___x_2154_; 
lean_dec_ref(v_e_2135_);
v_val_2151_ = lean_ctor_get(v_a_2150_, 0);
lean_inc(v_val_2151_);
lean_dec_ref_known(v_a_2150_, 1);
v_fst_2152_ = lean_ctor_get(v_val_2151_, 0);
lean_inc(v_fst_2152_);
v_snd_2153_ = lean_ctor_get(v_val_2151_, 1);
lean_inc(v_snd_2153_);
lean_dec(v_val_2151_);
v___x_2154_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_snd_2153_, v_p_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v_a_2155_; 
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_a_2155_);
lean_dec_ref_known(v___x_2154_, 1);
v_e_2135_ = v_fst_2152_;
v_p_2136_ = v_a_2155_;
goto _start;
}
else
{
lean_dec(v_fst_2152_);
return v___x_2154_;
}
}
else
{
lean_object* v___x_2157_; 
lean_dec(v_a_2150_);
v___x_2157_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_e_2135_, v_p_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_);
return v___x_2157_;
}
}
else
{
lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2165_; 
lean_dec_ref(v_p_2136_);
lean_dec_ref(v_e_2135_);
v_a_2158_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2160_ = v___x_2149_;
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v___x_2149_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2163_; 
if (v_isShared_2161_ == 0)
{
v___x_2163_ = v___x_2160_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_a_2158_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go___boxed(lean_object* v_e_2166_, lean_object* v_p_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_){
_start:
{
lean_object* v_res_2179_; 
v_res_2179_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go(v_e_2166_, v_p_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_);
lean_dec(v_a_2177_);
lean_dec_ref(v_a_2176_);
lean_dec(v_a_2175_);
lean_dec_ref(v_a_2174_);
lean_dec(v_a_2173_);
lean_dec_ref(v_a_2172_);
lean_dec(v_a_2171_);
lean_dec_ref(v_a_2170_);
lean_dec(v_a_2169_);
lean_dec(v_a_2168_);
return v_res_2179_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0(void){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2180_ = lean_unsigned_to_nat(0u);
v___x_2181_ = lean_nat_to_int(v___x_2180_);
return v___x_2181_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1(void){
_start:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2182_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0);
v___x_2183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2182_);
return v___x_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly(lean_object* v_e_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_){
_start:
{
uint8_t v___x_2196_; lean_object* v___x_2197_; 
v___x_2196_ = 1;
lean_inc_ref(v_e_2184_);
v___x_2197_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_2184_, v___x_2196_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v_a_2198_; 
v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
lean_inc(v_a_2198_);
lean_dec_ref_known(v___x_2197_, 1);
if (lean_obj_tag(v_a_2198_) == 1)
{
lean_object* v_val_2199_; lean_object* v_fst_2200_; lean_object* v_snd_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
lean_dec_ref(v_e_2184_);
v_val_2199_ = lean_ctor_get(v_a_2198_, 0);
lean_inc(v_val_2199_);
lean_dec_ref_known(v_a_2198_, 1);
v_fst_2200_ = lean_ctor_get(v_val_2199_, 0);
lean_inc(v_fst_2200_);
v_snd_2201_ = lean_ctor_get(v_val_2199_, 1);
lean_inc(v_snd_2201_);
lean_dec(v_val_2199_);
v___x_2202_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1);
v___x_2203_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_snd_2201_, v___x_2202_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2204_; lean_object* v___x_2205_; 
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
lean_inc(v_a_2204_);
lean_dec_ref_known(v___x_2203_, 1);
v___x_2205_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go(v_fst_2200_, v_a_2204_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_);
return v___x_2205_;
}
else
{
lean_dec(v_fst_2200_);
return v___x_2203_;
}
}
else
{
lean_object* v___x_2206_; lean_object* v___x_2207_; 
lean_dec(v_a_2198_);
v___x_2206_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1);
v___x_2207_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_e_2184_, v___x_2206_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_);
return v___x_2207_;
}
}
else
{
lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2215_; 
lean_dec_ref(v_e_2184_);
v_a_2208_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2210_ = v___x_2197_;
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___x_2197_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2213_; 
if (v_isShared_2211_ == 0)
{
v___x_2213_ = v___x_2210_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_a_2208_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly___boxed(lean_object* v_e_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_e_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_);
lean_dec(v_a_2226_);
lean_dec_ref(v_a_2225_);
lean_dec(v_a_2224_);
lean_dec_ref(v_a_2223_);
lean_dec(v_a_2222_);
lean_dec_ref(v_a_2221_);
lean_dec(v_a_2220_);
lean_dec_ref(v_a_2219_);
lean_dec(v_a_2218_);
lean_dec(v_a_2217_);
return v_res_2228_;
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
