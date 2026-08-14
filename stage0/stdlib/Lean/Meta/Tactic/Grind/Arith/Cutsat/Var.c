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
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHAddInt___redArg(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
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
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_a_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_172_; 
v_a_55_ = lean_ctor_get(v___x_54_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_54_);
if (v_isSharedCheck_172_ == 0)
{
v___x_57_ = v___x_54_;
v_isShared_58_ = v_isSharedCheck_172_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_a_55_);
lean_dec(v___x_54_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_172_;
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
lean_object* v_a_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_100_; 
v_a_91_ = lean_ctor_get(v___x_90_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_90_);
if (v_isSharedCheck_100_ == 0)
{
v___x_93_ = v___x_90_;
v_isShared_94_ = v_isSharedCheck_100_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_a_91_);
lean_dec(v___x_90_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_100_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
if (lean_obj_tag(v_a_91_) == 0)
{
lean_object* v___x_95_; 
lean_del_object(v___x_93_);
v___x_95_ = l_Lean_Meta_Structural_isInstHDivInt___redArg(v_arg_73_, v_a_50_);
return v___x_95_;
}
else
{
lean_object* v___x_96_; lean_object* v___x_98_; 
lean_dec_ref_known(v_a_91_, 1);
lean_dec_ref(v_arg_73_);
v___x_96_ = lean_box(v___x_84_);
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 0, v___x_96_);
v___x_98_ = v___x_93_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_96_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
else
{
lean_object* v_a_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_108_; 
lean_dec_ref(v_arg_73_);
v_a_101_ = lean_ctor_get(v___x_90_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_90_);
if (v_isSharedCheck_108_ == 0)
{
v___x_103_ = v___x_90_;
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_a_101_);
lean_dec(v___x_90_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_106_; 
if (v_isShared_104_ == 0)
{
v___x_106_ = v___x_103_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_a_101_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
}
}
else
{
lean_object* v___x_109_; 
lean_dec_ref(v___x_80_);
lean_del_object(v___x_57_);
v___x_109_ = l_Lean_Meta_getIntValue_x3f(v_arg_67_, v_a_49_, v_a_50_, v_a_51_, v_a_52_);
if (lean_obj_tag(v___x_109_) == 0)
{
lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_119_; 
v_a_110_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_119_ == 0)
{
v___x_112_ = v___x_109_;
v_isShared_113_ = v_isSharedCheck_119_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v___x_109_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_119_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
if (lean_obj_tag(v_a_110_) == 0)
{
lean_object* v___x_114_; 
lean_del_object(v___x_112_);
v___x_114_ = l_Lean_Meta_Structural_isInstHModInt___redArg(v_arg_73_, v_a_50_);
return v___x_114_;
}
else
{
lean_object* v___x_115_; lean_object* v___x_117_; 
lean_dec_ref_known(v_a_110_, 1);
lean_dec_ref(v_arg_73_);
v___x_115_ = lean_box(v___x_82_);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 0, v___x_115_);
v___x_117_ = v___x_112_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v___x_115_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
}
else
{
lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_127_; 
lean_dec_ref(v_arg_73_);
v_a_120_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_127_ == 0)
{
v___x_122_ = v___x_109_;
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v___x_109_);
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
lean_dec_ref(v___x_80_);
lean_del_object(v___x_57_);
v___x_128_ = l_Lean_Meta_Structural_isInstHPowInt___redArg(v_arg_73_, v_a_50_);
if (lean_obj_tag(v___x_128_) == 0)
{
lean_object* v_a_129_; uint8_t v___x_130_; 
v_a_129_ = lean_ctor_get(v___x_128_, 0);
lean_inc(v_a_129_);
v___x_130_ = lean_unbox(v_a_129_);
if (v___x_130_ == 0)
{
lean_dec(v_a_129_);
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_67_);
return v___x_128_;
}
else
{
lean_object* v___x_131_; 
lean_dec_ref_known(v___x_128_, 1);
v___x_131_ = l_Lean_Meta_getIntValue_x3f(v_arg_70_, v_a_49_, v_a_50_, v_a_51_, v_a_52_);
if (lean_obj_tag(v___x_131_) == 0)
{
lean_object* v_a_132_; lean_object* v___x_133_; 
v_a_132_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_a_132_);
lean_dec_ref_known(v___x_131_, 1);
v___x_133_ = l_Lean_Meta_getIntValue_x3f(v_arg_67_, v_a_49_, v_a_50_, v_a_51_, v_a_52_);
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
v___x_137_ = lean_box(v___x_82_);
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
lean_dec_ref(v_arg_67_);
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
lean_dec_ref(v_arg_70_);
lean_dec_ref(v_arg_67_);
return v___x_128_;
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
lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_180_; 
v_a_173_ = lean_ctor_get(v___x_54_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_54_);
if (v_isSharedCheck_180_ == 0)
{
v___x_175_ = v___x_54_;
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_54_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_178_; 
if (v_isShared_176_ == 0)
{
v___x_178_ = v___x_175_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_a_173_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_188_, lean_object* v_x_189_, lean_object* v_x_190_, lean_object* v_x_191_){
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
v___x_222_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__3___redArg(v_n_218_, v___x_221_, v_k_219_, v_v_220_);
return v___x_222_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(lean_object* v_x_224_, size_t v_x_225_, size_t v_x_226_, lean_object* v_x_227_, lean_object* v_x_228_){
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
lean_object* v_ks_275_; lean_object* v_vs_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_296_; 
v_ks_275_ = lean_ctor_get(v_x_224_, 0);
v_vs_276_ = lean_ctor_get(v_x_224_, 1);
v_isSharedCheck_296_ = !lean_is_exclusive(v_x_224_);
if (v_isSharedCheck_296_ == 0)
{
v___x_278_ = v_x_224_;
v_isShared_279_ = v_isSharedCheck_296_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_vs_276_);
lean_inc(v_ks_275_);
lean_dec(v_x_224_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_296_;
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
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_ks_275_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v_vs_276_);
v___x_281_ = v_reuseFailAlloc_295_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
lean_object* v_newNode_282_; uint8_t v___y_284_; size_t v___x_290_; uint8_t v___x_291_; 
v_newNode_282_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1___redArg(v___x_281_, v_x_227_, v_x_228_);
v___x_290_ = ((size_t)7ULL);
v___x_291_ = lean_usize_dec_le(v___x_290_, v_x_226_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_292_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_282_);
v___x_293_ = lean_unsigned_to_nat(4u);
v___x_294_ = lean_nat_dec_lt(v___x_292_, v___x_293_);
lean_dec(v___x_292_);
v___y_284_ = v___x_294_;
goto v___jp_283_;
}
else
{
v___y_284_ = v___x_291_;
goto v___jp_283_;
}
v___jp_283_:
{
if (v___y_284_ == 0)
{
lean_object* v_ks_285_; lean_object* v_vs_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v_ks_285_ = lean_ctor_get(v_newNode_282_, 0);
lean_inc_ref(v_ks_285_);
v_vs_286_ = lean_ctor_get(v_newNode_282_, 1);
lean_inc_ref(v_vs_286_);
lean_dec_ref(v_newNode_282_);
v___x_287_ = lean_unsigned_to_nat(0u);
v___x_288_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0);
v___x_289_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg(v_x_226_, v_ks_285_, v_vs_286_, v___x_287_, v___x_288_);
lean_dec_ref(v_vs_286_);
lean_dec_ref(v_ks_285_);
return v___x_289_;
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
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg(size_t v_depth_297_, lean_object* v_keys_298_, lean_object* v_vals_299_, lean_object* v_i_300_, lean_object* v_entries_301_){
_start:
{
lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_302_ = lean_array_get_size(v_keys_298_);
v___x_303_ = lean_nat_dec_lt(v_i_300_, v___x_302_);
if (v___x_303_ == 0)
{
lean_dec(v_i_300_);
return v_entries_301_;
}
else
{
lean_object* v_k_304_; lean_object* v_v_305_; uint64_t v___x_306_; size_t v_h_307_; size_t v___x_308_; lean_object* v___x_309_; size_t v___x_310_; size_t v___x_311_; size_t v___x_312_; size_t v_h_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v_k_304_ = lean_array_fget_borrowed(v_keys_298_, v_i_300_);
v_v_305_ = lean_array_fget_borrowed(v_vals_299_, v_i_300_);
v___x_306_ = lean_uint64_of_nat(v_k_304_);
v_h_307_ = lean_uint64_to_usize(v___x_306_);
v___x_308_ = ((size_t)5ULL);
v___x_309_ = lean_unsigned_to_nat(1u);
v___x_310_ = ((size_t)1ULL);
v___x_311_ = lean_usize_sub(v_depth_297_, v___x_310_);
v___x_312_ = lean_usize_mul(v___x_308_, v___x_311_);
v_h_313_ = lean_usize_shift_right(v_h_307_, v___x_312_);
v___x_314_ = lean_nat_add(v_i_300_, v___x_309_);
lean_dec(v_i_300_);
lean_inc(v_v_305_);
lean_inc(v_k_304_);
v___x_315_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_entries_301_, v_h_313_, v_depth_297_, v_k_304_, v_v_305_);
v_i_300_ = v___x_314_;
v_entries_301_ = v___x_315_;
goto _start;
}
}
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
size_t v_x_8860__boxed_329_; size_t v_x_8861__boxed_330_; lean_object* v_res_331_; 
v_x_8860__boxed_329_ = lean_unbox_usize(v_x_325_);
lean_dec(v_x_325_);
v_x_8861__boxed_330_ = lean_unbox_usize(v_x_326_);
lean_dec(v_x_326_);
v_res_331_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_x_324_, v_x_8860__boxed_329_, v_x_8861__boxed_330_, v_x_327_, v_x_328_);
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
lean_object* v_vars_343_; lean_object* v_varMap_344_; lean_object* v_vars_x27_345_; lean_object* v_varMap_x27_346_; lean_object* v_natToIntMap_347_; lean_object* v_natDef_348_; lean_object* v_dvds_349_; lean_object* v_lowers_350_; lean_object* v_uppers_351_; lean_object* v_diseqs_352_; lean_object* v_elimEqs_353_; lean_object* v_elimStack_354_; lean_object* v_occurs_355_; lean_object* v_assignment_356_; lean_object* v_nextCnstrId_357_; uint8_t v_caseSplits_358_; lean_object* v_steps_359_; lean_object* v_conflict_x3f_360_; lean_object* v_diseqSplits_361_; lean_object* v_divMod_362_; uint8_t v_usedCommRing_363_; lean_object* v_nonlinearOccs_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_373_; 
v_vars_343_ = lean_ctor_get(v_s_342_, 0);
v_varMap_344_ = lean_ctor_get(v_s_342_, 1);
v_vars_x27_345_ = lean_ctor_get(v_s_342_, 2);
v_varMap_x27_346_ = lean_ctor_get(v_s_342_, 3);
v_natToIntMap_347_ = lean_ctor_get(v_s_342_, 4);
v_natDef_348_ = lean_ctor_get(v_s_342_, 5);
v_dvds_349_ = lean_ctor_get(v_s_342_, 6);
v_lowers_350_ = lean_ctor_get(v_s_342_, 7);
v_uppers_351_ = lean_ctor_get(v_s_342_, 8);
v_diseqs_352_ = lean_ctor_get(v_s_342_, 9);
v_elimEqs_353_ = lean_ctor_get(v_s_342_, 10);
v_elimStack_354_ = lean_ctor_get(v_s_342_, 11);
v_occurs_355_ = lean_ctor_get(v_s_342_, 12);
v_assignment_356_ = lean_ctor_get(v_s_342_, 13);
v_nextCnstrId_357_ = lean_ctor_get(v_s_342_, 14);
v_caseSplits_358_ = lean_ctor_get_uint8(v_s_342_, sizeof(void*)*20);
v_steps_359_ = lean_ctor_get(v_s_342_, 15);
v_conflict_x3f_360_ = lean_ctor_get(v_s_342_, 16);
v_diseqSplits_361_ = lean_ctor_get(v_s_342_, 17);
v_divMod_362_ = lean_ctor_get(v_s_342_, 18);
v_usedCommRing_363_ = lean_ctor_get_uint8(v_s_342_, sizeof(void*)*20 + 1);
v_nonlinearOccs_364_ = lean_ctor_get(v_s_342_, 19);
v_isSharedCheck_373_ = !lean_is_exclusive(v_s_342_);
if (v_isSharedCheck_373_ == 0)
{
v___x_366_ = v_s_342_;
v_isShared_367_ = v_isSharedCheck_373_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_nonlinearOccs_364_);
lean_inc(v_divMod_362_);
lean_inc(v_diseqSplits_361_);
lean_inc(v_conflict_x3f_360_);
lean_inc(v_steps_359_);
lean_inc(v_nextCnstrId_357_);
lean_inc(v_assignment_356_);
lean_inc(v_occurs_355_);
lean_inc(v_elimStack_354_);
lean_inc(v_elimEqs_353_);
lean_inc(v_diseqs_352_);
lean_inc(v_uppers_351_);
lean_inc(v_lowers_350_);
lean_inc(v_dvds_349_);
lean_inc(v_natDef_348_);
lean_inc(v_natToIntMap_347_);
lean_inc(v_varMap_x27_346_);
lean_inc(v_vars_x27_345_);
lean_inc(v_varMap_344_);
lean_inc(v_vars_343_);
lean_dec(v_s_342_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_373_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_371_; 
v___x_368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_368_, 0, v_x_339_);
lean_ctor_set(v___x_368_, 1, v___y_340_);
v___x_369_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0___redArg(v_nonlinearOccs_364_, v_a_341_, v___x_368_);
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 19, v___x_369_);
v___x_371_ = v___x_366_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 20, 2);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_vars_343_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v_varMap_344_);
lean_ctor_set(v_reuseFailAlloc_372_, 2, v_vars_x27_345_);
lean_ctor_set(v_reuseFailAlloc_372_, 3, v_varMap_x27_346_);
lean_ctor_set(v_reuseFailAlloc_372_, 4, v_natToIntMap_347_);
lean_ctor_set(v_reuseFailAlloc_372_, 5, v_natDef_348_);
lean_ctor_set(v_reuseFailAlloc_372_, 6, v_dvds_349_);
lean_ctor_set(v_reuseFailAlloc_372_, 7, v_lowers_350_);
lean_ctor_set(v_reuseFailAlloc_372_, 8, v_uppers_351_);
lean_ctor_set(v_reuseFailAlloc_372_, 9, v_diseqs_352_);
lean_ctor_set(v_reuseFailAlloc_372_, 10, v_elimEqs_353_);
lean_ctor_set(v_reuseFailAlloc_372_, 11, v_elimStack_354_);
lean_ctor_set(v_reuseFailAlloc_372_, 12, v_occurs_355_);
lean_ctor_set(v_reuseFailAlloc_372_, 13, v_assignment_356_);
lean_ctor_set(v_reuseFailAlloc_372_, 14, v_nextCnstrId_357_);
lean_ctor_set(v_reuseFailAlloc_372_, 15, v_steps_359_);
lean_ctor_set(v_reuseFailAlloc_372_, 16, v_conflict_x3f_360_);
lean_ctor_set(v_reuseFailAlloc_372_, 17, v_diseqSplits_361_);
lean_ctor_set(v_reuseFailAlloc_372_, 18, v_divMod_362_);
lean_ctor_set(v_reuseFailAlloc_372_, 19, v___x_369_);
lean_ctor_set_uint8(v_reuseFailAlloc_372_, sizeof(void*)*20, v_caseSplits_358_);
lean_ctor_set_uint8(v_reuseFailAlloc_372_, sizeof(void*)*20 + 1, v_usedCommRing_363_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5___redArg(lean_object* v_keys_374_, lean_object* v_vals_375_, lean_object* v_i_376_, lean_object* v_k_377_){
_start:
{
lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_378_ = lean_array_get_size(v_keys_374_);
v___x_379_ = lean_nat_dec_lt(v_i_376_, v___x_378_);
if (v___x_379_ == 0)
{
lean_object* v___x_380_; 
lean_dec(v_i_376_);
v___x_380_ = lean_box(0);
return v___x_380_;
}
else
{
lean_object* v_k_x27_381_; uint8_t v___x_382_; 
v_k_x27_381_ = lean_array_fget_borrowed(v_keys_374_, v_i_376_);
v___x_382_ = lean_nat_dec_eq(v_k_377_, v_k_x27_381_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = lean_unsigned_to_nat(1u);
v___x_384_ = lean_nat_add(v_i_376_, v___x_383_);
lean_dec(v_i_376_);
v_i_376_ = v___x_384_;
goto _start;
}
else
{
lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_386_ = lean_array_fget_borrowed(v_vals_375_, v_i_376_);
lean_dec(v_i_376_);
lean_inc(v___x_386_);
v___x_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
return v___x_387_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_keys_388_, lean_object* v_vals_389_, lean_object* v_i_390_, lean_object* v_k_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5___redArg(v_keys_388_, v_vals_389_, v_i_390_, v_k_391_);
lean_dec(v_k_391_);
lean_dec_ref(v_vals_389_);
lean_dec_ref(v_keys_388_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2___redArg(lean_object* v_x_393_, size_t v_x_394_, lean_object* v_x_395_){
_start:
{
if (lean_obj_tag(v_x_393_) == 0)
{
lean_object* v_es_396_; lean_object* v___x_397_; size_t v___x_398_; size_t v___x_399_; lean_object* v_j_400_; lean_object* v___x_401_; 
v_es_396_ = lean_ctor_get(v_x_393_, 0);
v___x_397_ = lean_box(2);
v___x_398_ = ((size_t)31ULL);
v___x_399_ = lean_usize_land(v_x_394_, v___x_398_);
v_j_400_ = lean_usize_to_nat(v___x_399_);
v___x_401_ = lean_array_get_borrowed(v___x_397_, v_es_396_, v_j_400_);
lean_dec(v_j_400_);
switch(lean_obj_tag(v___x_401_))
{
case 0:
{
lean_object* v_key_402_; lean_object* v_val_403_; uint8_t v___x_404_; 
v_key_402_ = lean_ctor_get(v___x_401_, 0);
v_val_403_ = lean_ctor_get(v___x_401_, 1);
v___x_404_ = lean_nat_dec_eq(v_x_395_, v_key_402_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; 
v___x_405_ = lean_box(0);
return v___x_405_;
}
else
{
lean_object* v___x_406_; 
lean_inc(v_val_403_);
v___x_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_406_, 0, v_val_403_);
return v___x_406_;
}
}
case 1:
{
lean_object* v_node_407_; size_t v___x_408_; size_t v___x_409_; 
v_node_407_ = lean_ctor_get(v___x_401_, 0);
v___x_408_ = ((size_t)5ULL);
v___x_409_ = lean_usize_shift_right(v_x_394_, v___x_408_);
v_x_393_ = v_node_407_;
v_x_394_ = v___x_409_;
goto _start;
}
default: 
{
lean_object* v___x_411_; 
v___x_411_ = lean_box(0);
return v___x_411_;
}
}
}
else
{
lean_object* v_ks_412_; lean_object* v_vs_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v_ks_412_ = lean_ctor_get(v_x_393_, 0);
v_vs_413_ = lean_ctor_get(v_x_393_, 1);
v___x_414_ = lean_unsigned_to_nat(0u);
v___x_415_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5___redArg(v_ks_412_, v_vs_413_, v___x_414_, v_x_395_);
return v___x_415_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2___redArg___boxed(lean_object* v_x_416_, lean_object* v_x_417_, lean_object* v_x_418_){
_start:
{
size_t v_x_9070__boxed_419_; lean_object* v_res_420_; 
v_x_9070__boxed_419_ = lean_unbox_usize(v_x_417_);
lean_dec(v_x_417_);
v_res_420_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2___redArg(v_x_416_, v_x_9070__boxed_419_, v_x_418_);
lean_dec(v_x_418_);
lean_dec_ref(v_x_416_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___redArg(lean_object* v_x_421_, lean_object* v_x_422_){
_start:
{
uint64_t v___x_423_; size_t v___x_424_; lean_object* v___x_425_; 
v___x_423_ = lean_uint64_of_nat(v_x_422_);
v___x_424_ = lean_uint64_to_usize(v___x_423_);
v___x_425_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2___redArg(v_x_421_, v___x_424_, v_x_422_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___redArg___boxed(lean_object* v_x_426_, lean_object* v_x_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___redArg(v_x_426_, v_x_427_);
lean_dec(v_x_427_);
lean_dec_ref(v_x_426_);
return v_res_428_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___closed__0(void){
_start:
{
lean_object* v___x_429_; lean_object* v___f_430_; 
v___x_429_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_430_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_430_, 0, v___x_429_);
return v___f_430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(lean_object* v_arg_431_, lean_object* v_x_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_){
_start:
{
lean_object* v___x_444_; 
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
v___x_444_ = lean_grind_cutsat_mk_var(v_arg_431_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_516_; 
v_a_445_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_516_ == 0)
{
v___x_447_ = v___x_444_;
v_isShared_448_ = v_isSharedCheck_516_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_444_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_516_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___y_450_; lean_object* v___y_451_; lean_object* v___y_452_; lean_object* v___y_462_; lean_object* v___y_463_; lean_object* v___x_479_; 
v___x_479_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_433_, v_a_441_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_480_; lean_object* v___y_482_; lean_object* v_elimEqs_502_; lean_object* v_size_503_; lean_object* v___x_504_; uint8_t v___x_505_; 
v_a_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_a_480_);
lean_dec_ref_known(v___x_479_, 1);
v_elimEqs_502_ = lean_ctor_get(v_a_480_, 10);
lean_inc_ref(v_elimEqs_502_);
lean_dec(v_a_480_);
v_size_503_ = lean_ctor_get(v_elimEqs_502_, 2);
v___x_504_ = lean_box(0);
v___x_505_ = lean_nat_dec_lt(v_a_445_, v_size_503_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; 
lean_dec_ref(v_elimEqs_502_);
v___x_506_ = l_outOfBounds___redArg(v___x_504_);
v___y_482_ = v___x_506_;
goto v___jp_481_;
}
else
{
lean_object* v___x_507_; 
v___x_507_ = l_Lean_PersistentArray_get_x21___redArg(v___x_504_, v_elimEqs_502_, v_a_445_);
lean_dec_ref(v_elimEqs_502_);
v___y_482_ = v___x_507_;
goto v___jp_481_;
}
v___jp_481_:
{
if (lean_obj_tag(v___y_482_) == 0)
{
v___y_462_ = v_a_433_;
v___y_463_ = v_a_441_;
goto v___jp_461_;
}
else
{
lean_object* v___x_483_; 
lean_dec_ref_known(v___y_482_, 1);
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
lean_inc(v_a_445_);
v___x_483_ = lean_cutsat_propagate_nonlinear(v_a_445_, v_x_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_493_; 
v_a_484_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_493_ == 0)
{
v___x_486_ = v___x_483_;
v_isShared_487_ = v_isSharedCheck_493_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_483_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_493_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
uint8_t v___x_488_; 
v___x_488_ = lean_unbox(v_a_484_);
lean_dec(v_a_484_);
if (v___x_488_ == 0)
{
lean_del_object(v___x_486_);
v___y_462_ = v_a_433_;
v___y_463_ = v_a_441_;
goto v___jp_461_;
}
else
{
lean_object* v___x_489_; lean_object* v___x_491_; 
lean_del_object(v___x_447_);
lean_dec(v_a_445_);
lean_dec(v_x_432_);
v___x_489_ = lean_box(0);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 0, v___x_489_);
v___x_491_ = v___x_486_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_489_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
else
{
lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
lean_del_object(v___x_447_);
lean_dec(v_a_445_);
lean_dec(v_x_432_);
v_a_494_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v___x_483_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_483_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_494_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
}
}
else
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
lean_del_object(v___x_447_);
lean_dec(v_a_445_);
lean_dec(v_x_432_);
v_a_508_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_515_ == 0)
{
v___x_510_ = v___x_479_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_479_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_511_ == 0)
{
v___x_513_ = v___x_510_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_508_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
v___jp_449_:
{
uint8_t v___x_453_; 
lean_inc(v___y_452_);
lean_inc(v_x_432_);
lean_inc_ref(v___y_451_);
v___x_453_ = l_List_elem___redArg(v___y_451_, v_x_432_, v___y_452_);
if (v___x_453_ == 0)
{
lean_object* v___f_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
lean_del_object(v___x_447_);
v___f_454_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___lam__0), 4, 3);
lean_closure_set(v___f_454_, 0, v_x_432_);
lean_closure_set(v___f_454_, 1, v___y_452_);
lean_closure_set(v___f_454_, 2, v_a_445_);
v___x_455_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_456_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_455_, v___f_454_, v___y_450_);
return v___x_456_;
}
else
{
lean_object* v___x_457_; lean_object* v___x_459_; 
lean_dec(v___y_452_);
lean_dec(v_a_445_);
lean_dec(v_x_432_);
v___x_457_ = lean_box(0);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v___x_457_);
v___x_459_ = v___x_447_;
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
lean_object* v_a_465_; lean_object* v_nonlinearOccs_466_; lean_object* v___f_467_; lean_object* v___x_468_; 
v_a_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_a_465_);
lean_dec_ref_known(v___x_464_, 1);
v_nonlinearOccs_466_ = lean_ctor_get(v_a_465_, 19);
lean_inc_ref(v_nonlinearOccs_466_);
lean_dec(v_a_465_);
v___f_467_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___closed__0);
v___x_468_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___redArg(v_nonlinearOccs_466_, v_a_445_);
lean_dec_ref(v_nonlinearOccs_466_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v___x_469_; 
v___x_469_ = lean_box(0);
v___y_450_ = v___y_462_;
v___y_451_ = v___f_467_;
v___y_452_ = v___x_469_;
goto v___jp_449_;
}
else
{
lean_object* v_val_470_; 
v_val_470_ = lean_ctor_get(v___x_468_, 0);
lean_inc(v_val_470_);
lean_dec_ref_known(v___x_468_, 1);
v___y_450_ = v___y_462_;
v___y_451_ = v___f_467_;
v___y_452_ = v_val_470_;
goto v___jp_449_;
}
}
else
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
lean_del_object(v___x_447_);
lean_dec(v_a_445_);
lean_dec(v_x_432_);
v_a_471_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___x_464_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_464_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
}
}
else
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_524_; 
lean_dec(v_x_432_);
v_a_517_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_524_ == 0)
{
v___x_519_ = v___x_444_;
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_444_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___boxed(lean_object* v_arg_525_, lean_object* v_x_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_arg_525_, v_x_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_);
lean_dec(v_a_536_);
lean_dec_ref(v_a_535_);
lean_dec(v_a_534_);
lean_dec_ref(v_a_533_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
lean_dec(v_a_530_);
lean_dec_ref(v_a_529_);
lean_dec(v_a_528_);
lean_dec(v_a_527_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0(lean_object* v_00_u03b2_539_, lean_object* v_x_540_, lean_object* v_x_541_, lean_object* v_x_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0___redArg(v_x_540_, v_x_541_, v_x_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1(lean_object* v_00_u03b2_544_, lean_object* v_x_545_, lean_object* v_x_546_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___redArg(v_x_545_, v_x_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___boxed(lean_object* v_00_u03b2_548_, lean_object* v_x_549_, lean_object* v_x_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1(v_00_u03b2_548_, v_x_549_, v_x_550_);
lean_dec(v_x_550_);
lean_dec_ref(v_x_549_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0(lean_object* v_00_u03b2_552_, lean_object* v_x_553_, size_t v_x_554_, size_t v_x_555_, lean_object* v_x_556_, lean_object* v_x_557_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_x_553_, v_x_554_, v_x_555_, v_x_556_, v_x_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___boxed(lean_object* v_00_u03b2_559_, lean_object* v_x_560_, lean_object* v_x_561_, lean_object* v_x_562_, lean_object* v_x_563_, lean_object* v_x_564_){
_start:
{
size_t v_x_9311__boxed_565_; size_t v_x_9312__boxed_566_; lean_object* v_res_567_; 
v_x_9311__boxed_565_ = lean_unbox_usize(v_x_561_);
lean_dec(v_x_561_);
v_x_9312__boxed_566_ = lean_unbox_usize(v_x_562_);
lean_dec(v_x_562_);
v_res_567_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0(v_00_u03b2_559_, v_x_560_, v_x_9311__boxed_565_, v_x_9312__boxed_566_, v_x_563_, v_x_564_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2(lean_object* v_00_u03b2_568_, lean_object* v_x_569_, size_t v_x_570_, lean_object* v_x_571_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2___redArg(v_x_569_, v_x_570_, v_x_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2___boxed(lean_object* v_00_u03b2_573_, lean_object* v_x_574_, lean_object* v_x_575_, lean_object* v_x_576_){
_start:
{
size_t v_x_9328__boxed_577_; lean_object* v_res_578_; 
v_x_9328__boxed_577_ = lean_unbox_usize(v_x_575_);
lean_dec(v_x_575_);
v_res_578_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2(v_00_u03b2_573_, v_x_574_, v_x_9328__boxed_577_, v_x_576_);
lean_dec(v_x_576_);
lean_dec_ref(v_x_574_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_579_, lean_object* v_n_580_, lean_object* v_k_581_, lean_object* v_v_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1___redArg(v_n_580_, v_k_581_, v_v_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_584_, size_t v_depth_585_, lean_object* v_keys_586_, lean_object* v_vals_587_, lean_object* v_heq_588_, lean_object* v_i_589_, lean_object* v_entries_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg(v_depth_585_, v_keys_586_, v_vals_587_, v_i_589_, v_entries_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_592_, lean_object* v_depth_593_, lean_object* v_keys_594_, lean_object* v_vals_595_, lean_object* v_heq_596_, lean_object* v_i_597_, lean_object* v_entries_598_){
_start:
{
size_t v_depth_boxed_599_; lean_object* v_res_600_; 
v_depth_boxed_599_ = lean_unbox_usize(v_depth_593_);
lean_dec(v_depth_593_);
v_res_600_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2(v_00_u03b2_592_, v_depth_boxed_599_, v_keys_594_, v_vals_595_, v_heq_596_, v_i_597_, v_entries_598_);
lean_dec_ref(v_vals_595_);
lean_dec_ref(v_keys_594_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_601_, lean_object* v_keys_602_, lean_object* v_vals_603_, lean_object* v_heq_604_, lean_object* v_i_605_, lean_object* v_k_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5___redArg(v_keys_602_, v_vals_603_, v_i_605_, v_k_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_608_, lean_object* v_keys_609_, lean_object* v_vals_610_, lean_object* v_heq_611_, lean_object* v_i_612_, lean_object* v_k_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5(v_00_u03b2_608_, v_keys_609_, v_vals_610_, v_heq_611_, v_i_612_, v_k_613_);
lean_dec(v_k_613_);
lean_dec_ref(v_vals_610_);
lean_dec_ref(v_keys_609_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_615_, lean_object* v_x_616_, lean_object* v_x_617_, lean_object* v_x_618_, lean_object* v_x_619_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__3___redArg(v_x_616_, v_x_617_, v_x_618_, v_x_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(lean_object* v_x_621_, lean_object* v_e_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_){
_start:
{
lean_object* v___x_634_; 
lean_inc_ref(v_e_622_);
v___x_634_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_622_, v_a_630_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc(v_a_635_);
lean_dec_ref_known(v___x_634_, 1);
v___x_636_ = l_Lean_Expr_cleanupAnnotations(v_a_635_);
v___x_637_ = l_Lean_Expr_isApp(v___x_636_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; 
lean_dec_ref(v___x_636_);
v___x_638_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_622_, v_x_621_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_);
return v___x_638_;
}
else
{
lean_object* v_arg_639_; lean_object* v___x_640_; uint8_t v___x_641_; 
v_arg_639_ = lean_ctor_get(v___x_636_, 1);
lean_inc_ref(v_arg_639_);
v___x_640_ = l_Lean_Expr_appFnCleanup___redArg(v___x_636_);
v___x_641_ = l_Lean_Expr_isApp(v___x_640_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; 
lean_dec_ref(v___x_640_);
lean_dec_ref(v_arg_639_);
v___x_642_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_622_, v_x_621_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_);
return v___x_642_;
}
else
{
lean_object* v_arg_643_; lean_object* v___x_644_; uint8_t v___x_645_; 
v_arg_643_ = lean_ctor_get(v___x_640_, 1);
lean_inc_ref(v_arg_643_);
v___x_644_ = l_Lean_Expr_appFnCleanup___redArg(v___x_640_);
v___x_645_ = l_Lean_Expr_isApp(v___x_644_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; 
lean_dec_ref(v___x_644_);
lean_dec_ref(v_arg_643_);
lean_dec_ref(v_arg_639_);
v___x_646_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_622_, v_x_621_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_);
return v___x_646_;
}
else
{
lean_object* v_arg_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v_arg_647_ = lean_ctor_get(v___x_644_, 1);
lean_inc_ref(v_arg_647_);
v___x_648_ = l_Lean_Expr_appFnCleanup___redArg(v___x_644_);
v___x_649_ = l_Lean_Expr_isApp(v___x_648_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; 
lean_dec_ref(v___x_648_);
lean_dec_ref(v_arg_647_);
lean_dec_ref(v_arg_643_);
lean_dec_ref(v_arg_639_);
v___x_650_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_622_, v_x_621_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_);
return v___x_650_;
}
else
{
lean_object* v___x_651_; uint8_t v___x_652_; 
v___x_651_ = l_Lean_Expr_appFnCleanup___redArg(v___x_648_);
v___x_652_ = l_Lean_Expr_isApp(v___x_651_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; 
lean_dec_ref(v___x_651_);
lean_dec_ref(v_arg_647_);
lean_dec_ref(v_arg_643_);
lean_dec_ref(v_arg_639_);
v___x_653_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_622_, v_x_621_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_);
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
lean_dec_ref(v_arg_647_);
lean_dec_ref(v_arg_643_);
lean_dec_ref(v_arg_639_);
v___x_656_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_622_, v_x_621_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_);
return v___x_656_;
}
else
{
lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_657_ = l_Lean_Expr_appFnCleanup___redArg(v___x_654_);
v___x_658_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11));
v___x_659_ = l_Lean_Expr_isConstOf(v___x_657_, v___x_658_);
lean_dec_ref(v___x_657_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; 
lean_dec_ref(v_arg_647_);
lean_dec_ref(v_arg_643_);
lean_dec_ref(v_arg_639_);
v___x_660_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_622_, v_x_621_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_);
return v___x_660_;
}
else
{
lean_object* v___x_661_; 
v___x_661_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_647_, v_a_630_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; uint8_t v___x_663_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_a_662_);
lean_dec_ref_known(v___x_661_, 1);
v___x_663_ = lean_unbox(v_a_662_);
lean_dec(v_a_662_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; 
lean_dec_ref(v_arg_643_);
lean_dec_ref(v_arg_639_);
v___x_664_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_622_, v_x_621_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_);
return v___x_664_;
}
else
{
lean_object* v___x_665_; 
lean_dec_ref(v_e_622_);
lean_inc(v_x_621_);
v___x_665_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(v_x_621_, v_arg_643_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_dec_ref_known(v___x_665_, 1);
v_e_622_ = v_arg_639_;
goto _start;
}
else
{
lean_dec_ref(v_arg_639_);
lean_dec(v_x_621_);
return v___x_665_;
}
}
}
else
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_674_; 
lean_dec_ref(v_arg_643_);
lean_dec_ref(v_arg_639_);
lean_dec_ref(v_e_622_);
lean_dec(v_x_621_);
v_a_667_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_674_ == 0)
{
v___x_669_ = v___x_661_;
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_661_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_667_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
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
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_682_; 
lean_dec_ref(v_e_622_);
lean_dec(v_x_621_);
v_a_675_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_682_ == 0)
{
v___x_677_ = v___x_634_;
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_634_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
if (v_isShared_678_ == 0)
{
v___x_680_ = v___x_677_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_a_675_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go___boxed(lean_object* v_x_683_, lean_object* v_e_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(v_x_683_, v_e_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_);
lean_dec(v_a_694_);
lean_dec_ref(v_a_693_);
lean_dec(v_a_692_);
lean_dec_ref(v_a_691_);
lean_dec(v_a_690_);
lean_dec_ref(v_a_689_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
lean_dec(v_a_686_);
lean_dec(v_a_685_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt(lean_object* v_e_697_, lean_object* v_x_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_697_, v_a_706_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_816_; 
v_a_714_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_816_ == 0)
{
v___x_716_ = v___x_713_;
v_isShared_717_ = v_isSharedCheck_816_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_713_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_816_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_723_ = l_Lean_Expr_cleanupAnnotations(v_a_714_);
v___x_724_ = l_Lean_Expr_isApp(v___x_723_);
if (v___x_724_ == 0)
{
lean_dec_ref(v___x_723_);
lean_dec(v_x_698_);
goto v___jp_718_;
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
lean_dec(v_x_698_);
goto v___jp_718_;
}
else
{
lean_object* v_arg_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
v_arg_728_ = lean_ctor_get(v___x_726_, 1);
lean_inc_ref(v_arg_728_);
v___x_729_ = l_Lean_Expr_appFnCleanup___redArg(v___x_726_);
v___x_730_ = l_Lean_Expr_isApp(v___x_729_);
if (v___x_730_ == 0)
{
lean_dec_ref(v___x_729_);
lean_dec_ref(v_arg_728_);
lean_dec_ref(v_arg_725_);
lean_dec(v_x_698_);
goto v___jp_718_;
}
else
{
lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_731_ = l_Lean_Expr_appFnCleanup___redArg(v___x_729_);
v___x_732_ = l_Lean_Expr_isApp(v___x_731_);
if (v___x_732_ == 0)
{
lean_dec_ref(v___x_731_);
lean_dec_ref(v_arg_728_);
lean_dec_ref(v_arg_725_);
lean_dec(v_x_698_);
goto v___jp_718_;
}
else
{
lean_object* v___x_733_; uint8_t v___x_734_; 
v___x_733_ = l_Lean_Expr_appFnCleanup___redArg(v___x_731_);
v___x_734_ = l_Lean_Expr_isApp(v___x_733_);
if (v___x_734_ == 0)
{
lean_dec_ref(v___x_733_);
lean_dec_ref(v_arg_728_);
lean_dec_ref(v_arg_725_);
lean_dec(v_x_698_);
goto v___jp_718_;
}
else
{
lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_735_ = l_Lean_Expr_appFnCleanup___redArg(v___x_733_);
v___x_736_ = l_Lean_Expr_isApp(v___x_735_);
if (v___x_736_ == 0)
{
lean_dec_ref(v___x_735_);
lean_dec_ref(v_arg_728_);
lean_dec_ref(v_arg_725_);
lean_dec(v_x_698_);
goto v___jp_718_;
}
else
{
lean_object* v___x_737_; lean_object* v___x_738_; uint8_t v___x_739_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___y_750_; 
v___x_737_ = l_Lean_Expr_appFnCleanup___redArg(v___x_735_);
v___x_738_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__2));
v___x_739_ = l_Lean_Expr_isConstOf(v___x_737_, v___x_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_795_; uint8_t v___x_796_; 
v___x_795_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__5));
v___x_796_ = l_Lean_Expr_isConstOf(v___x_737_, v___x_795_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; uint8_t v___x_798_; 
v___x_797_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__8));
v___x_798_ = l_Lean_Expr_isConstOf(v___x_737_, v___x_797_);
if (v___x_798_ == 0)
{
lean_object* v___x_799_; uint8_t v___x_800_; 
v___x_799_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11));
v___x_800_ = l_Lean_Expr_isConstOf(v___x_737_, v___x_799_);
lean_dec_ref(v___x_737_);
if (v___x_800_ == 0)
{
lean_dec_ref(v_arg_728_);
lean_dec_ref(v_arg_725_);
lean_dec(v_x_698_);
goto v___jp_718_;
}
else
{
lean_object* v___x_801_; 
lean_del_object(v___x_716_);
lean_inc(v_x_698_);
v___x_801_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(v_x_698_, v_arg_728_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v___x_802_; 
lean_dec_ref_known(v___x_801_, 1);
v___x_802_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(v_x_698_, v_arg_725_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
return v___x_802_;
}
else
{
lean_dec_ref(v_arg_725_);
lean_dec(v_x_698_);
return v___x_801_;
}
}
}
else
{
lean_object* v___x_803_; 
lean_dec_ref(v___x_737_);
lean_dec_ref(v_arg_728_);
lean_del_object(v___x_716_);
v___x_803_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_arg_725_, v_x_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
return v___x_803_;
}
}
else
{
lean_object* v___x_804_; 
lean_dec_ref(v___x_737_);
lean_dec_ref(v_arg_728_);
lean_del_object(v___x_716_);
v___x_804_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_arg_725_, v_x_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
return v___x_804_;
}
}
else
{
lean_object* v___x_805_; 
lean_dec_ref(v___x_737_);
lean_del_object(v___x_716_);
lean_inc_ref(v_arg_728_);
v___x_805_ = l_Lean_Meta_getIntValue_x3f(v_arg_728_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v_a_806_; 
v_a_806_ = lean_ctor_get(v___x_805_, 0);
lean_inc(v_a_806_);
lean_dec_ref_known(v___x_805_, 1);
if (lean_obj_tag(v_a_806_) == 0)
{
if (v___x_739_ == 0)
{
lean_dec_ref(v_arg_728_);
v___y_741_ = v_a_699_;
v___y_742_ = v_a_700_;
v___y_743_ = v_a_701_;
v___y_744_ = v_a_702_;
v___y_745_ = v_a_703_;
v___y_746_ = v_a_704_;
v___y_747_ = v_a_705_;
v___y_748_ = v_a_706_;
v___y_749_ = v_a_707_;
v___y_750_ = v_a_708_;
goto v___jp_740_;
}
else
{
lean_object* v___x_807_; 
lean_inc(v_x_698_);
v___x_807_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_arg_728_, v_x_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_dec_ref_known(v___x_807_, 1);
v___y_741_ = v_a_699_;
v___y_742_ = v_a_700_;
v___y_743_ = v_a_701_;
v___y_744_ = v_a_702_;
v___y_745_ = v_a_703_;
v___y_746_ = v_a_704_;
v___y_747_ = v_a_705_;
v___y_748_ = v_a_706_;
v___y_749_ = v_a_707_;
v___y_750_ = v_a_708_;
goto v___jp_740_;
}
else
{
lean_dec_ref(v_arg_725_);
lean_dec(v_x_698_);
return v___x_807_;
}
}
}
else
{
lean_dec_ref_known(v_a_806_, 1);
lean_dec_ref(v_arg_728_);
v___y_741_ = v_a_699_;
v___y_742_ = v_a_700_;
v___y_743_ = v_a_701_;
v___y_744_ = v_a_702_;
v___y_745_ = v_a_703_;
v___y_746_ = v_a_704_;
v___y_747_ = v_a_705_;
v___y_748_ = v_a_706_;
v___y_749_ = v_a_707_;
v___y_750_ = v_a_708_;
goto v___jp_740_;
}
}
else
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
lean_dec_ref(v_arg_728_);
lean_dec_ref(v_arg_725_);
lean_dec(v_x_698_);
v_a_808_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_815_ == 0)
{
v___x_810_ = v___x_805_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_805_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_808_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
v___jp_740_:
{
lean_object* v___x_751_; 
lean_inc_ref(v_arg_725_);
v___x_751_ = l_Lean_Meta_getIntValue_x3f(v_arg_725_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v___x_753_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_a_752_);
lean_dec_ref_known(v___x_751_, 1);
v___x_753_ = l_Lean_Meta_getNatValue_x3f(v_arg_725_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
if (lean_obj_tag(v___x_753_) == 0)
{
if (lean_obj_tag(v_a_752_) == 0)
{
if (v___x_739_ == 0)
{
lean_dec_ref_known(v___x_753_, 1);
lean_dec_ref(v_arg_725_);
lean_dec(v_x_698_);
goto v___jp_710_;
}
else
{
lean_object* v_a_754_; 
v_a_754_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_a_754_);
lean_dec_ref_known(v___x_753_, 1);
if (lean_obj_tag(v_a_754_) == 0)
{
lean_object* v___x_755_; 
lean_inc_ref(v_arg_725_);
v___x_755_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_arg_725_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; lean_object* v_fst_757_; lean_object* v___x_758_; 
v_a_756_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_a_756_);
lean_dec_ref_known(v___x_755_, 1);
v_fst_757_ = lean_ctor_get(v_a_756_, 0);
lean_inc(v_fst_757_);
lean_dec(v_a_756_);
v___x_758_ = l_Lean_Meta_Grind_getGeneration___redArg(v_arg_725_, v___y_741_);
lean_dec_ref(v_arg_725_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_a_759_);
lean_dec_ref_known(v___x_758_, 1);
v___x_760_ = lean_box(0);
lean_inc(v___y_750_);
lean_inc_ref(v___y_749_);
lean_inc(v___y_748_);
lean_inc_ref(v___y_747_);
lean_inc(v___y_746_);
lean_inc_ref(v___y_745_);
lean_inc(v___y_744_);
lean_inc_ref(v___y_743_);
lean_inc(v___y_742_);
lean_inc(v___y_741_);
lean_inc(v_fst_757_);
v___x_761_ = lean_grind_internalize(v_fst_757_, v_a_759_, v___x_760_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v___x_762_; 
lean_dec_ref_known(v___x_761_, 1);
v___x_762_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_fst_757_, v_x_698_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
return v___x_762_;
}
else
{
lean_dec(v_fst_757_);
lean_dec(v_x_698_);
return v___x_761_;
}
}
else
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
lean_dec(v_fst_757_);
lean_dec(v_x_698_);
v_a_763_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_758_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_758_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_766_ == 0)
{
v___x_768_ = v___x_765_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_763_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_dec_ref(v_arg_725_);
lean_dec(v_x_698_);
v_a_771_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_755_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_755_);
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
lean_dec_ref_known(v_a_754_, 1);
lean_dec_ref(v_arg_725_);
lean_dec(v_x_698_);
goto v___jp_710_;
}
}
}
else
{
lean_dec_ref_known(v_a_752_, 1);
lean_dec_ref_known(v___x_753_, 1);
lean_dec_ref(v_arg_725_);
lean_dec(v_x_698_);
goto v___jp_710_;
}
}
else
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_786_; 
lean_dec(v_a_752_);
lean_dec_ref(v_arg_725_);
lean_dec(v_x_698_);
v_a_779_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_786_ == 0)
{
v___x_781_ = v___x_753_;
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_753_);
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
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
lean_dec_ref(v_arg_725_);
lean_dec(v_x_698_);
v_a_787_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_751_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_751_);
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
}
}
}
}
}
}
v___jp_718_:
{
lean_object* v___x_719_; lean_object* v___x_721_; 
v___x_719_ = lean_box(0);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 0, v___x_719_);
v___x_721_ = v___x_716_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_719_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
else
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_824_; 
lean_dec(v_x_698_);
v_a_817_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_824_ == 0)
{
v___x_819_ = v___x_713_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_713_);
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
v___jp_710_:
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = lean_box(0);
v___x_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
return v___x_712_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt___boxed(lean_object* v_e_825_, lean_object* v_x_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt(v_e_825_, v_x_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_);
lean_dec(v_a_836_);
lean_dec_ref(v_a_835_);
lean_dec(v_a_834_);
lean_dec_ref(v_a_833_);
lean_dec(v_a_832_);
lean_dec_ref(v_a_831_);
lean_dec(v_a_830_);
lean_dec_ref(v_a_829_);
lean_dec(v_a_828_);
lean_dec(v_a_827_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_x_839_, lean_object* v_x_840_, lean_object* v_x_841_, lean_object* v_x_842_){
_start:
{
lean_object* v_ks_843_; lean_object* v_vs_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_870_; 
v_ks_843_ = lean_ctor_get(v_x_839_, 0);
v_vs_844_ = lean_ctor_get(v_x_839_, 1);
v_isSharedCheck_870_ = !lean_is_exclusive(v_x_839_);
if (v_isSharedCheck_870_ == 0)
{
v___x_846_ = v_x_839_;
v_isShared_847_ = v_isSharedCheck_870_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_vs_844_);
lean_inc(v_ks_843_);
lean_dec(v_x_839_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_870_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_848_; uint8_t v___x_849_; 
v___x_848_ = lean_array_get_size(v_ks_843_);
v___x_849_ = lean_nat_dec_lt(v_x_840_, v___x_848_);
if (v___x_849_ == 0)
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_853_; 
lean_dec(v_x_840_);
v___x_850_ = lean_array_push(v_ks_843_, v_x_841_);
v___x_851_ = lean_array_push(v_vs_844_, v_x_842_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 1, v___x_851_);
lean_ctor_set(v___x_846_, 0, v___x_850_);
v___x_853_ = v___x_846_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_850_);
lean_ctor_set(v_reuseFailAlloc_854_, 1, v___x_851_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
else
{
lean_object* v_k_x27_855_; size_t v___x_856_; size_t v___x_857_; uint8_t v___x_858_; 
v_k_x27_855_ = lean_array_fget_borrowed(v_ks_843_, v_x_840_);
v___x_856_ = lean_ptr_addr(v_x_841_);
v___x_857_ = lean_ptr_addr(v_k_x27_855_);
v___x_858_ = lean_usize_dec_eq(v___x_856_, v___x_857_);
if (v___x_858_ == 0)
{
lean_object* v___x_860_; 
if (v_isShared_847_ == 0)
{
v___x_860_ = v___x_846_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_ks_843_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v_vs_844_);
v___x_860_ = v_reuseFailAlloc_864_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = lean_unsigned_to_nat(1u);
v___x_862_ = lean_nat_add(v_x_840_, v___x_861_);
lean_dec(v_x_840_);
v_x_839_ = v___x_860_;
v_x_840_ = v___x_862_;
goto _start;
}
}
else
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_868_; 
v___x_865_ = lean_array_fset(v_ks_843_, v_x_840_, v_x_841_);
v___x_866_ = lean_array_fset(v_vs_844_, v_x_840_, v_x_842_);
lean_dec(v_x_840_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 1, v___x_866_);
lean_ctor_set(v___x_846_, 0, v___x_865_);
v___x_868_ = v___x_846_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_865_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v___x_866_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4___redArg(lean_object* v_n_871_, lean_object* v_k_872_, lean_object* v_v_873_){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = lean_unsigned_to_nat(0u);
v___x_875_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7___redArg(v_n_871_, v___x_874_, v_k_872_, v_v_873_);
return v___x_875_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(lean_object* v_x_877_, size_t v_x_878_, size_t v_x_879_, lean_object* v_x_880_, lean_object* v_x_881_){
_start:
{
if (lean_obj_tag(v_x_877_) == 0)
{
lean_object* v_es_882_; size_t v___x_883_; size_t v___x_884_; lean_object* v_j_885_; lean_object* v___x_886_; uint8_t v___x_887_; 
v_es_882_ = lean_ctor_get(v_x_877_, 0);
v___x_883_ = ((size_t)31ULL);
v___x_884_ = lean_usize_land(v_x_878_, v___x_883_);
v_j_885_ = lean_usize_to_nat(v___x_884_);
v___x_886_ = lean_array_get_size(v_es_882_);
v___x_887_ = lean_nat_dec_lt(v_j_885_, v___x_886_);
if (v___x_887_ == 0)
{
lean_dec(v_j_885_);
lean_dec(v_x_881_);
lean_dec_ref(v_x_880_);
return v_x_877_;
}
else
{
lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_928_; 
lean_inc_ref(v_es_882_);
v_isSharedCheck_928_ = !lean_is_exclusive(v_x_877_);
if (v_isSharedCheck_928_ == 0)
{
lean_object* v_unused_929_; 
v_unused_929_ = lean_ctor_get(v_x_877_, 0);
lean_dec(v_unused_929_);
v___x_889_ = v_x_877_;
v_isShared_890_ = v_isSharedCheck_928_;
goto v_resetjp_888_;
}
else
{
lean_dec(v_x_877_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_928_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v_v_891_; lean_object* v___x_892_; lean_object* v_xs_x27_893_; lean_object* v___y_895_; 
v_v_891_ = lean_array_fget(v_es_882_, v_j_885_);
v___x_892_ = lean_box(0);
v_xs_x27_893_ = lean_array_fset(v_es_882_, v_j_885_, v___x_892_);
switch(lean_obj_tag(v_v_891_))
{
case 0:
{
lean_object* v_key_900_; lean_object* v_val_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_913_; 
v_key_900_ = lean_ctor_get(v_v_891_, 0);
v_val_901_ = lean_ctor_get(v_v_891_, 1);
v_isSharedCheck_913_ = !lean_is_exclusive(v_v_891_);
if (v_isSharedCheck_913_ == 0)
{
v___x_903_ = v_v_891_;
v_isShared_904_ = v_isSharedCheck_913_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_val_901_);
lean_inc(v_key_900_);
lean_dec(v_v_891_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_913_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
size_t v___x_905_; size_t v___x_906_; uint8_t v___x_907_; 
v___x_905_ = lean_ptr_addr(v_x_880_);
v___x_906_ = lean_ptr_addr(v_key_900_);
v___x_907_ = lean_usize_dec_eq(v___x_905_, v___x_906_);
if (v___x_907_ == 0)
{
lean_object* v___x_908_; lean_object* v___x_909_; 
lean_del_object(v___x_903_);
v___x_908_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_900_, v_val_901_, v_x_880_, v_x_881_);
v___x_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
v___y_895_ = v___x_909_;
goto v___jp_894_;
}
else
{
lean_object* v___x_911_; 
lean_dec(v_val_901_);
lean_dec(v_key_900_);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 1, v_x_881_);
lean_ctor_set(v___x_903_, 0, v_x_880_);
v___x_911_ = v___x_903_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_x_880_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_x_881_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
v___y_895_ = v___x_911_;
goto v___jp_894_;
}
}
}
}
case 1:
{
lean_object* v_node_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_926_; 
v_node_914_ = lean_ctor_get(v_v_891_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v_v_891_);
if (v_isSharedCheck_926_ == 0)
{
v___x_916_ = v_v_891_;
v_isShared_917_ = v_isSharedCheck_926_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_node_914_);
lean_dec(v_v_891_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_926_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
size_t v___x_918_; size_t v___x_919_; size_t v___x_920_; size_t v___x_921_; lean_object* v___x_922_; lean_object* v___x_924_; 
v___x_918_ = ((size_t)5ULL);
v___x_919_ = lean_usize_shift_right(v_x_878_, v___x_918_);
v___x_920_ = ((size_t)1ULL);
v___x_921_ = lean_usize_add(v_x_879_, v___x_920_);
v___x_922_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_node_914_, v___x_919_, v___x_921_, v_x_880_, v_x_881_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v___x_922_);
v___x_924_ = v___x_916_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_922_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
v___y_895_ = v___x_924_;
goto v___jp_894_;
}
}
}
default: 
{
lean_object* v___x_927_; 
v___x_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_927_, 0, v_x_880_);
lean_ctor_set(v___x_927_, 1, v_x_881_);
v___y_895_ = v___x_927_;
goto v___jp_894_;
}
}
v___jp_894_:
{
lean_object* v___x_896_; lean_object* v___x_898_; 
v___x_896_ = lean_array_fset(v_xs_x27_893_, v_j_885_, v___y_895_);
lean_dec(v_j_885_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v___x_896_);
v___x_898_ = v___x_889_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_896_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
}
else
{
lean_object* v_ks_930_; lean_object* v_vs_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_951_; 
v_ks_930_ = lean_ctor_get(v_x_877_, 0);
v_vs_931_ = lean_ctor_get(v_x_877_, 1);
v_isSharedCheck_951_ = !lean_is_exclusive(v_x_877_);
if (v_isSharedCheck_951_ == 0)
{
v___x_933_ = v_x_877_;
v_isShared_934_ = v_isSharedCheck_951_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_vs_931_);
lean_inc(v_ks_930_);
lean_dec(v_x_877_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_951_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
v___x_936_ = v___x_933_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_ks_930_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_vs_931_);
v___x_936_ = v_reuseFailAlloc_950_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
lean_object* v_newNode_937_; uint8_t v___y_939_; size_t v___x_945_; uint8_t v___x_946_; 
v_newNode_937_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4___redArg(v___x_936_, v_x_880_, v_x_881_);
v___x_945_ = ((size_t)7ULL);
v___x_946_ = lean_usize_dec_le(v___x_945_, v_x_879_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; lean_object* v___x_948_; uint8_t v___x_949_; 
v___x_947_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_937_);
v___x_948_ = lean_unsigned_to_nat(4u);
v___x_949_ = lean_nat_dec_lt(v___x_947_, v___x_948_);
lean_dec(v___x_947_);
v___y_939_ = v___x_949_;
goto v___jp_938_;
}
else
{
v___y_939_ = v___x_946_;
goto v___jp_938_;
}
v___jp_938_:
{
if (v___y_939_ == 0)
{
lean_object* v_ks_940_; lean_object* v_vs_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v_ks_940_ = lean_ctor_get(v_newNode_937_, 0);
lean_inc_ref(v_ks_940_);
v_vs_941_ = lean_ctor_get(v_newNode_937_, 1);
lean_inc_ref(v_vs_941_);
lean_dec_ref(v_newNode_937_);
v___x_942_ = lean_unsigned_to_nat(0u);
v___x_943_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg___closed__0);
v___x_944_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(v_x_879_, v_ks_940_, v_vs_941_, v___x_942_, v___x_943_);
lean_dec_ref(v_vs_941_);
lean_dec_ref(v_ks_940_);
return v___x_944_;
}
else
{
return v_newNode_937_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(size_t v_depth_952_, lean_object* v_keys_953_, lean_object* v_vals_954_, lean_object* v_i_955_, lean_object* v_entries_956_){
_start:
{
lean_object* v___x_957_; uint8_t v___x_958_; 
v___x_957_ = lean_array_get_size(v_keys_953_);
v___x_958_ = lean_nat_dec_lt(v_i_955_, v___x_957_);
if (v___x_958_ == 0)
{
lean_dec(v_i_955_);
return v_entries_956_;
}
else
{
lean_object* v_k_959_; lean_object* v_v_960_; size_t v___x_961_; size_t v___x_962_; size_t v___x_963_; uint64_t v___x_964_; size_t v_h_965_; size_t v___x_966_; lean_object* v___x_967_; size_t v___x_968_; size_t v___x_969_; size_t v___x_970_; size_t v_h_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v_k_959_ = lean_array_fget_borrowed(v_keys_953_, v_i_955_);
v_v_960_ = lean_array_fget_borrowed(v_vals_954_, v_i_955_);
v___x_961_ = lean_ptr_addr(v_k_959_);
v___x_962_ = ((size_t)3ULL);
v___x_963_ = lean_usize_shift_right(v___x_961_, v___x_962_);
v___x_964_ = lean_usize_to_uint64(v___x_963_);
v_h_965_ = lean_uint64_to_usize(v___x_964_);
v___x_966_ = ((size_t)5ULL);
v___x_967_ = lean_unsigned_to_nat(1u);
v___x_968_ = ((size_t)1ULL);
v___x_969_ = lean_usize_sub(v_depth_952_, v___x_968_);
v___x_970_ = lean_usize_mul(v___x_966_, v___x_969_);
v_h_971_ = lean_usize_shift_right(v_h_965_, v___x_970_);
v___x_972_ = lean_nat_add(v_i_955_, v___x_967_);
lean_dec(v_i_955_);
lean_inc(v_v_960_);
lean_inc(v_k_959_);
v___x_973_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_entries_956_, v_h_971_, v_depth_952_, v_k_959_, v_v_960_);
v_i_955_ = v___x_972_;
v_entries_956_ = v___x_973_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_975_, lean_object* v_keys_976_, lean_object* v_vals_977_, lean_object* v_i_978_, lean_object* v_entries_979_){
_start:
{
size_t v_depth_boxed_980_; lean_object* v_res_981_; 
v_depth_boxed_980_ = lean_unbox_usize(v_depth_975_);
lean_dec(v_depth_975_);
v_res_981_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(v_depth_boxed_980_, v_keys_976_, v_vals_977_, v_i_978_, v_entries_979_);
lean_dec_ref(v_vals_977_);
lean_dec_ref(v_keys_976_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg___boxed(lean_object* v_x_982_, lean_object* v_x_983_, lean_object* v_x_984_, lean_object* v_x_985_, lean_object* v_x_986_){
_start:
{
size_t v_x_30734__boxed_987_; size_t v_x_30735__boxed_988_; lean_object* v_res_989_; 
v_x_30734__boxed_987_ = lean_unbox_usize(v_x_983_);
lean_dec(v_x_983_);
v_x_30735__boxed_988_ = lean_unbox_usize(v_x_984_);
lean_dec(v_x_984_);
v_res_989_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_x_982_, v_x_30734__boxed_987_, v_x_30735__boxed_988_, v_x_985_, v_x_986_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg(lean_object* v_x_990_, lean_object* v_x_991_, lean_object* v_x_992_){
_start:
{
size_t v___x_993_; size_t v___x_994_; size_t v___x_995_; uint64_t v___x_996_; size_t v___x_997_; size_t v___x_998_; lean_object* v___x_999_; 
v___x_993_ = lean_ptr_addr(v_x_991_);
v___x_994_ = ((size_t)3ULL);
v___x_995_ = lean_usize_shift_right(v___x_993_, v___x_994_);
v___x_996_ = lean_usize_to_uint64(v___x_995_);
v___x_997_ = lean_uint64_to_usize(v___x_996_);
v___x_998_ = ((size_t)1ULL);
v___x_999_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_x_990_, v___x_997_, v___x_998_, v_x_991_, v_x_992_);
return v___x_999_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1000_ = lean_unsigned_to_nat(32u);
v___x_1001_ = lean_mk_empty_array_with_capacity(v___x_1000_);
v___x_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
return v___x_1002_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1(void){
_start:
{
size_t v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1003_ = ((size_t)5ULL);
v___x_1004_ = lean_unsigned_to_nat(0u);
v___x_1005_ = lean_unsigned_to_nat(32u);
v___x_1006_ = lean_mk_empty_array_with_capacity(v___x_1005_);
v___x_1007_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0);
v___x_1008_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v___x_1006_);
lean_ctor_set(v___x_1008_, 2, v___x_1004_);
lean_ctor_set(v___x_1008_, 3, v___x_1004_);
lean_ctor_set_usize(v___x_1008_, 4, v___x_1003_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0(lean_object* v_expr_1009_, lean_object* v_size_1010_, lean_object* v_s_1011_){
_start:
{
lean_object* v_vars_1012_; lean_object* v_varMap_1013_; lean_object* v_vars_x27_1014_; lean_object* v_varMap_x27_1015_; lean_object* v_natToIntMap_1016_; lean_object* v_natDef_1017_; lean_object* v_dvds_1018_; lean_object* v_lowers_1019_; lean_object* v_uppers_1020_; lean_object* v_diseqs_1021_; lean_object* v_elimEqs_1022_; lean_object* v_elimStack_1023_; lean_object* v_occurs_1024_; lean_object* v_assignment_1025_; lean_object* v_nextCnstrId_1026_; uint8_t v_caseSplits_1027_; lean_object* v_steps_1028_; lean_object* v_conflict_x3f_1029_; lean_object* v_diseqSplits_1030_; lean_object* v_divMod_1031_; uint8_t v_usedCommRing_1032_; lean_object* v_nonlinearOccs_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1051_; 
v_vars_1012_ = lean_ctor_get(v_s_1011_, 0);
v_varMap_1013_ = lean_ctor_get(v_s_1011_, 1);
v_vars_x27_1014_ = lean_ctor_get(v_s_1011_, 2);
v_varMap_x27_1015_ = lean_ctor_get(v_s_1011_, 3);
v_natToIntMap_1016_ = lean_ctor_get(v_s_1011_, 4);
v_natDef_1017_ = lean_ctor_get(v_s_1011_, 5);
v_dvds_1018_ = lean_ctor_get(v_s_1011_, 6);
v_lowers_1019_ = lean_ctor_get(v_s_1011_, 7);
v_uppers_1020_ = lean_ctor_get(v_s_1011_, 8);
v_diseqs_1021_ = lean_ctor_get(v_s_1011_, 9);
v_elimEqs_1022_ = lean_ctor_get(v_s_1011_, 10);
v_elimStack_1023_ = lean_ctor_get(v_s_1011_, 11);
v_occurs_1024_ = lean_ctor_get(v_s_1011_, 12);
v_assignment_1025_ = lean_ctor_get(v_s_1011_, 13);
v_nextCnstrId_1026_ = lean_ctor_get(v_s_1011_, 14);
v_caseSplits_1027_ = lean_ctor_get_uint8(v_s_1011_, sizeof(void*)*20);
v_steps_1028_ = lean_ctor_get(v_s_1011_, 15);
v_conflict_x3f_1029_ = lean_ctor_get(v_s_1011_, 16);
v_diseqSplits_1030_ = lean_ctor_get(v_s_1011_, 17);
v_divMod_1031_ = lean_ctor_get(v_s_1011_, 18);
v_usedCommRing_1032_ = lean_ctor_get_uint8(v_s_1011_, sizeof(void*)*20 + 1);
v_nonlinearOccs_1033_ = lean_ctor_get(v_s_1011_, 19);
v_isSharedCheck_1051_ = !lean_is_exclusive(v_s_1011_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1035_ = v_s_1011_;
v_isShared_1036_ = v_isSharedCheck_1051_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_nonlinearOccs_1033_);
lean_inc(v_divMod_1031_);
lean_inc(v_diseqSplits_1030_);
lean_inc(v_conflict_x3f_1029_);
lean_inc(v_steps_1028_);
lean_inc(v_nextCnstrId_1026_);
lean_inc(v_assignment_1025_);
lean_inc(v_occurs_1024_);
lean_inc(v_elimStack_1023_);
lean_inc(v_elimEqs_1022_);
lean_inc(v_diseqs_1021_);
lean_inc(v_uppers_1020_);
lean_inc(v_lowers_1019_);
lean_inc(v_dvds_1018_);
lean_inc(v_natDef_1017_);
lean_inc(v_natToIntMap_1016_);
lean_inc(v_varMap_x27_1015_);
lean_inc(v_vars_x27_1014_);
lean_inc(v_varMap_1013_);
lean_inc(v_vars_1012_);
lean_dec(v_s_1011_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1051_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1049_; 
lean_inc_ref(v_expr_1009_);
v___x_1037_ = l_Lean_PersistentArray_push___redArg(v_vars_1012_, v_expr_1009_);
v___x_1038_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg(v_varMap_1013_, v_expr_1009_, v_size_1010_);
v___x_1039_ = lean_box(0);
v___x_1040_ = l_Lean_PersistentArray_push___redArg(v_dvds_1018_, v___x_1039_);
v___x_1041_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1);
v___x_1042_ = l_Lean_PersistentArray_push___redArg(v_lowers_1019_, v___x_1041_);
v___x_1043_ = l_Lean_PersistentArray_push___redArg(v_uppers_1020_, v___x_1041_);
v___x_1044_ = l_Lean_PersistentArray_push___redArg(v_diseqs_1021_, v___x_1041_);
v___x_1045_ = l_Lean_PersistentArray_push___redArg(v_elimEqs_1022_, v___x_1039_);
v___x_1046_ = lean_box(1);
v___x_1047_ = l_Lean_PersistentArray_push___redArg(v_occurs_1024_, v___x_1046_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 12, v___x_1047_);
lean_ctor_set(v___x_1035_, 10, v___x_1045_);
lean_ctor_set(v___x_1035_, 9, v___x_1044_);
lean_ctor_set(v___x_1035_, 8, v___x_1043_);
lean_ctor_set(v___x_1035_, 7, v___x_1042_);
lean_ctor_set(v___x_1035_, 6, v___x_1040_);
lean_ctor_set(v___x_1035_, 1, v___x_1038_);
lean_ctor_set(v___x_1035_, 0, v___x_1037_);
v___x_1049_ = v___x_1035_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 20, 2);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v___x_1038_);
lean_ctor_set(v_reuseFailAlloc_1050_, 2, v_vars_x27_1014_);
lean_ctor_set(v_reuseFailAlloc_1050_, 3, v_varMap_x27_1015_);
lean_ctor_set(v_reuseFailAlloc_1050_, 4, v_natToIntMap_1016_);
lean_ctor_set(v_reuseFailAlloc_1050_, 5, v_natDef_1017_);
lean_ctor_set(v_reuseFailAlloc_1050_, 6, v___x_1040_);
lean_ctor_set(v_reuseFailAlloc_1050_, 7, v___x_1042_);
lean_ctor_set(v_reuseFailAlloc_1050_, 8, v___x_1043_);
lean_ctor_set(v_reuseFailAlloc_1050_, 9, v___x_1044_);
lean_ctor_set(v_reuseFailAlloc_1050_, 10, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1050_, 11, v_elimStack_1023_);
lean_ctor_set(v_reuseFailAlloc_1050_, 12, v___x_1047_);
lean_ctor_set(v_reuseFailAlloc_1050_, 13, v_assignment_1025_);
lean_ctor_set(v_reuseFailAlloc_1050_, 14, v_nextCnstrId_1026_);
lean_ctor_set(v_reuseFailAlloc_1050_, 15, v_steps_1028_);
lean_ctor_set(v_reuseFailAlloc_1050_, 16, v_conflict_x3f_1029_);
lean_ctor_set(v_reuseFailAlloc_1050_, 17, v_diseqSplits_1030_);
lean_ctor_set(v_reuseFailAlloc_1050_, 18, v_divMod_1031_);
lean_ctor_set(v_reuseFailAlloc_1050_, 19, v_nonlinearOccs_1033_);
lean_ctor_set_uint8(v_reuseFailAlloc_1050_, sizeof(void*)*20, v_caseSplits_1027_);
lean_ctor_set_uint8(v_reuseFailAlloc_1050_, sizeof(void*)*20 + 1, v_usedCommRing_1032_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1052_, lean_object* v_vals_1053_, lean_object* v_i_1054_, lean_object* v_k_1055_){
_start:
{
lean_object* v___x_1056_; uint8_t v___x_1057_; 
v___x_1056_ = lean_array_get_size(v_keys_1052_);
v___x_1057_ = lean_nat_dec_lt(v_i_1054_, v___x_1056_);
if (v___x_1057_ == 0)
{
lean_object* v___x_1058_; 
lean_dec(v_i_1054_);
v___x_1058_ = lean_box(0);
return v___x_1058_;
}
else
{
lean_object* v_k_x27_1059_; size_t v___x_1060_; size_t v___x_1061_; uint8_t v___x_1062_; 
v_k_x27_1059_ = lean_array_fget_borrowed(v_keys_1052_, v_i_1054_);
v___x_1060_ = lean_ptr_addr(v_k_1055_);
v___x_1061_ = lean_ptr_addr(v_k_x27_1059_);
v___x_1062_ = lean_usize_dec_eq(v___x_1060_, v___x_1061_);
if (v___x_1062_ == 0)
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = lean_unsigned_to_nat(1u);
v___x_1064_ = lean_nat_add(v_i_1054_, v___x_1063_);
lean_dec(v_i_1054_);
v_i_1054_ = v___x_1064_;
goto _start;
}
else
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = lean_array_fget_borrowed(v_vals_1053_, v_i_1054_);
lean_dec(v_i_1054_);
lean_inc(v___x_1066_);
v___x_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
return v___x_1067_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1068_, lean_object* v_vals_1069_, lean_object* v_i_1070_, lean_object* v_k_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(v_keys_1068_, v_vals_1069_, v_i_1070_, v_k_1071_);
lean_dec_ref(v_k_1071_);
lean_dec_ref(v_vals_1069_);
lean_dec_ref(v_keys_1068_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(lean_object* v_x_1073_, size_t v_x_1074_, lean_object* v_x_1075_){
_start:
{
if (lean_obj_tag(v_x_1073_) == 0)
{
lean_object* v_es_1076_; lean_object* v___x_1077_; size_t v___x_1078_; size_t v___x_1079_; lean_object* v_j_1080_; lean_object* v___x_1081_; 
v_es_1076_ = lean_ctor_get(v_x_1073_, 0);
v___x_1077_ = lean_box(2);
v___x_1078_ = ((size_t)31ULL);
v___x_1079_ = lean_usize_land(v_x_1074_, v___x_1078_);
v_j_1080_ = lean_usize_to_nat(v___x_1079_);
v___x_1081_ = lean_array_get_borrowed(v___x_1077_, v_es_1076_, v_j_1080_);
lean_dec(v_j_1080_);
switch(lean_obj_tag(v___x_1081_))
{
case 0:
{
lean_object* v_key_1082_; lean_object* v_val_1083_; size_t v___x_1084_; size_t v___x_1085_; uint8_t v___x_1086_; 
v_key_1082_ = lean_ctor_get(v___x_1081_, 0);
v_val_1083_ = lean_ctor_get(v___x_1081_, 1);
v___x_1084_ = lean_ptr_addr(v_x_1075_);
v___x_1085_ = lean_ptr_addr(v_key_1082_);
v___x_1086_ = lean_usize_dec_eq(v___x_1084_, v___x_1085_);
if (v___x_1086_ == 0)
{
lean_object* v___x_1087_; 
v___x_1087_ = lean_box(0);
return v___x_1087_;
}
else
{
lean_object* v___x_1088_; 
lean_inc(v_val_1083_);
v___x_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1088_, 0, v_val_1083_);
return v___x_1088_;
}
}
case 1:
{
lean_object* v_node_1089_; size_t v___x_1090_; size_t v___x_1091_; 
v_node_1089_ = lean_ctor_get(v___x_1081_, 0);
v___x_1090_ = ((size_t)5ULL);
v___x_1091_ = lean_usize_shift_right(v_x_1074_, v___x_1090_);
v_x_1073_ = v_node_1089_;
v_x_1074_ = v___x_1091_;
goto _start;
}
default: 
{
lean_object* v___x_1093_; 
v___x_1093_ = lean_box(0);
return v___x_1093_;
}
}
}
else
{
lean_object* v_ks_1094_; lean_object* v_vs_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v_ks_1094_ = lean_ctor_get(v_x_1073_, 0);
v_vs_1095_ = lean_ctor_get(v_x_1073_, 1);
v___x_1096_ = lean_unsigned_to_nat(0u);
v___x_1097_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(v_ks_1094_, v_vs_1095_, v___x_1096_, v_x_1075_);
return v___x_1097_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg___boxed(lean_object* v_x_1098_, lean_object* v_x_1099_, lean_object* v_x_1100_){
_start:
{
size_t v_x_31004__boxed_1101_; lean_object* v_res_1102_; 
v_x_31004__boxed_1101_ = lean_unbox_usize(v_x_1099_);
lean_dec(v_x_1099_);
v_res_1102_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(v_x_1098_, v_x_31004__boxed_1101_, v_x_1100_);
lean_dec_ref(v_x_1100_);
lean_dec_ref(v_x_1098_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(lean_object* v_x_1103_, lean_object* v_x_1104_){
_start:
{
size_t v___x_1105_; size_t v___x_1106_; size_t v___x_1107_; uint64_t v___x_1108_; size_t v___x_1109_; lean_object* v___x_1110_; 
v___x_1105_ = lean_ptr_addr(v_x_1104_);
v___x_1106_ = ((size_t)3ULL);
v___x_1107_ = lean_usize_shift_right(v___x_1105_, v___x_1106_);
v___x_1108_ = lean_usize_to_uint64(v___x_1107_);
v___x_1109_ = lean_uint64_to_usize(v___x_1108_);
v___x_1110_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(v_x_1103_, v___x_1109_, v_x_1104_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg___boxed(lean_object* v_x_1111_, lean_object* v_x_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(v_x_1111_, v_x_1112_);
lean_dec_ref(v_x_1112_);
lean_dec_ref(v_x_1111_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4(lean_object* v_msgData_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v___x_1120_; lean_object* v_env_1121_; lean_object* v___x_1122_; lean_object* v_mctx_1123_; lean_object* v_lctx_1124_; lean_object* v_options_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1120_ = lean_st_ref_get(v___y_1118_);
v_env_1121_ = lean_ctor_get(v___x_1120_, 0);
lean_inc_ref(v_env_1121_);
lean_dec(v___x_1120_);
v___x_1122_ = lean_st_ref_get(v___y_1116_);
v_mctx_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc_ref(v_mctx_1123_);
lean_dec(v___x_1122_);
v_lctx_1124_ = lean_ctor_get(v___y_1115_, 2);
v_options_1125_ = lean_ctor_get(v___y_1117_, 2);
lean_inc_ref(v_options_1125_);
lean_inc_ref(v_lctx_1124_);
v___x_1126_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1126_, 0, v_env_1121_);
lean_ctor_set(v___x_1126_, 1, v_mctx_1123_);
lean_ctor_set(v___x_1126_, 2, v_lctx_1124_);
lean_ctor_set(v___x_1126_, 3, v_options_1125_);
v___x_1127_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1126_);
lean_ctor_set(v___x_1127_, 1, v_msgData_1114_);
v___x_1128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1127_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4___boxed(lean_object* v_msgData_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4(v_msgData_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
return v_res_1135_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1136_; double v___x_1137_; 
v___x_1136_ = lean_unsigned_to_nat(0u);
v___x_1137_ = lean_float_of_nat(v___x_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(lean_object* v_cls_1141_, lean_object* v_msg_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v_ref_1148_; lean_object* v___x_1149_; lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1194_; 
v_ref_1148_ = lean_ctor_get(v___y_1145_, 5);
v___x_1149_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4(v_msg_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1152_ = v___x_1149_;
v_isShared_1153_ = v_isSharedCheck_1194_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1194_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1154_; lean_object* v_traceState_1155_; lean_object* v_env_1156_; lean_object* v_nextMacroScope_1157_; lean_object* v_ngen_1158_; lean_object* v_auxDeclNGen_1159_; lean_object* v_cache_1160_; lean_object* v_messages_1161_; lean_object* v_infoState_1162_; lean_object* v_snapshotTasks_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1193_; 
v___x_1154_ = lean_st_ref_take(v___y_1146_);
v_traceState_1155_ = lean_ctor_get(v___x_1154_, 4);
v_env_1156_ = lean_ctor_get(v___x_1154_, 0);
v_nextMacroScope_1157_ = lean_ctor_get(v___x_1154_, 1);
v_ngen_1158_ = lean_ctor_get(v___x_1154_, 2);
v_auxDeclNGen_1159_ = lean_ctor_get(v___x_1154_, 3);
v_cache_1160_ = lean_ctor_get(v___x_1154_, 5);
v_messages_1161_ = lean_ctor_get(v___x_1154_, 6);
v_infoState_1162_ = lean_ctor_get(v___x_1154_, 7);
v_snapshotTasks_1163_ = lean_ctor_get(v___x_1154_, 8);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1165_ = v___x_1154_;
v_isShared_1166_ = v_isSharedCheck_1193_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_snapshotTasks_1163_);
lean_inc(v_infoState_1162_);
lean_inc(v_messages_1161_);
lean_inc(v_cache_1160_);
lean_inc(v_traceState_1155_);
lean_inc(v_auxDeclNGen_1159_);
lean_inc(v_ngen_1158_);
lean_inc(v_nextMacroScope_1157_);
lean_inc(v_env_1156_);
lean_dec(v___x_1154_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1193_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
uint64_t v_tid_1167_; lean_object* v_traces_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1192_; 
v_tid_1167_ = lean_ctor_get_uint64(v_traceState_1155_, sizeof(void*)*1);
v_traces_1168_ = lean_ctor_get(v_traceState_1155_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v_traceState_1155_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1170_ = v_traceState_1155_;
v_isShared_1171_ = v_isSharedCheck_1192_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_traces_1168_);
lean_dec(v_traceState_1155_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1192_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1172_; double v___x_1173_; uint8_t v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1182_; 
v___x_1172_ = lean_box(0);
v___x_1173_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0);
v___x_1174_ = 0;
v___x_1175_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__1));
v___x_1176_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1176_, 0, v_cls_1141_);
lean_ctor_set(v___x_1176_, 1, v___x_1172_);
lean_ctor_set(v___x_1176_, 2, v___x_1175_);
lean_ctor_set_float(v___x_1176_, sizeof(void*)*3, v___x_1173_);
lean_ctor_set_float(v___x_1176_, sizeof(void*)*3 + 8, v___x_1173_);
lean_ctor_set_uint8(v___x_1176_, sizeof(void*)*3 + 16, v___x_1174_);
v___x_1177_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__2));
v___x_1178_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1176_);
lean_ctor_set(v___x_1178_, 1, v_a_1150_);
lean_ctor_set(v___x_1178_, 2, v___x_1177_);
lean_inc(v_ref_1148_);
v___x_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1179_, 0, v_ref_1148_);
lean_ctor_set(v___x_1179_, 1, v___x_1178_);
v___x_1180_ = l_Lean_PersistentArray_push___redArg(v_traces_1168_, v___x_1179_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 0, v___x_1180_);
v___x_1182_ = v___x_1170_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1180_);
lean_ctor_set_uint64(v_reuseFailAlloc_1191_, sizeof(void*)*1, v_tid_1167_);
v___x_1182_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
lean_object* v___x_1184_; 
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 4, v___x_1182_);
v___x_1184_ = v___x_1165_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_env_1156_);
lean_ctor_set(v_reuseFailAlloc_1190_, 1, v_nextMacroScope_1157_);
lean_ctor_set(v_reuseFailAlloc_1190_, 2, v_ngen_1158_);
lean_ctor_set(v_reuseFailAlloc_1190_, 3, v_auxDeclNGen_1159_);
lean_ctor_set(v_reuseFailAlloc_1190_, 4, v___x_1182_);
lean_ctor_set(v_reuseFailAlloc_1190_, 5, v_cache_1160_);
lean_ctor_set(v_reuseFailAlloc_1190_, 6, v_messages_1161_);
lean_ctor_set(v_reuseFailAlloc_1190_, 7, v_infoState_1162_);
lean_ctor_set(v_reuseFailAlloc_1190_, 8, v_snapshotTasks_1163_);
v___x_1184_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1188_; 
v___x_1185_ = lean_st_ref_put(v___y_1146_, v___x_1184_);
v___x_1186_ = lean_box(0);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v___x_1186_);
v___x_1188_ = v___x_1152_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v___x_1186_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___boxed(lean_object* v_cls_1195_, lean_object* v_msg_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(v_cls_1195_, v_msg_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
return v_res_1202_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7(void){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1215_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4));
v___x_1216_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__6));
v___x_1217_ = l_Lean_Name_append(v___x_1216_, v___x_1215_);
return v___x_1217_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9(void){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__8));
v___x_1220_ = l_Lean_stringToMessageData(v___x_1219_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* lean_grind_cutsat_mk_var(lean_object* v_expr_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1222_, v_a_1230_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1362_; 
v_a_1234_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1236_ = v___x_1233_;
v_isShared_1237_ = v_isSharedCheck_1362_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1233_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1362_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v_varMap_1238_; lean_object* v___x_1239_; 
v_varMap_1238_ = lean_ctor_get(v_a_1234_, 1);
lean_inc_ref(v_varMap_1238_);
lean_dec(v_a_1234_);
v___x_1239_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(v_varMap_1238_, v_expr_1221_);
lean_dec_ref(v_varMap_1238_);
if (lean_obj_tag(v___x_1239_) == 1)
{
lean_object* v_val_1240_; lean_object* v___x_1242_; 
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1230_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_a_1225_);
lean_dec_ref(v_a_1224_);
lean_dec(v_a_1223_);
lean_dec(v_a_1222_);
lean_dec_ref(v_expr_1221_);
v_val_1240_ = lean_ctor_get(v___x_1239_, 0);
lean_inc(v_val_1240_);
lean_dec_ref_known(v___x_1239_, 1);
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 0, v_val_1240_);
v___x_1242_ = v___x_1236_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_val_1240_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
else
{
lean_object* v___x_1244_; 
lean_dec(v___x_1239_);
lean_del_object(v___x_1236_);
v___x_1244_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1222_, v_a_1230_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_a_1245_; lean_object* v_vars_1246_; lean_object* v_options_1247_; lean_object* v_size_1248_; lean_object* v_inheritedTraceOptions_1249_; uint8_t v_hasTrace_1250_; lean_object* v___f_1251_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1261_; lean_object* v___y_1262_; 
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_a_1245_);
lean_dec_ref_known(v___x_1244_, 1);
v_vars_1246_ = lean_ctor_get(v_a_1245_, 0);
lean_inc_ref(v_vars_1246_);
lean_dec(v_a_1245_);
v_options_1247_ = lean_ctor_get(v_a_1230_, 2);
v_size_1248_ = lean_ctor_get(v_vars_1246_, 2);
lean_inc_n(v_size_1248_, 2);
lean_dec_ref(v_vars_1246_);
v_inheritedTraceOptions_1249_ = lean_ctor_get(v_a_1230_, 13);
v_hasTrace_1250_ = lean_ctor_get_uint8(v_options_1247_, sizeof(void*)*1);
lean_inc_ref(v_expr_1221_);
v___f_1251_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0), 3, 2);
lean_closure_set(v___f_1251_, 0, v_expr_1221_);
lean_closure_set(v___f_1251_, 1, v_size_1248_);
if (v_hasTrace_1250_ == 0)
{
v___y_1253_ = v_a_1222_;
v___y_1254_ = v_a_1223_;
v___y_1255_ = v_a_1224_;
v___y_1256_ = v_a_1225_;
v___y_1257_ = v_a_1226_;
v___y_1258_ = v_a_1227_;
v___y_1259_ = v_a_1228_;
v___y_1260_ = v_a_1229_;
v___y_1261_ = v_a_1230_;
v___y_1262_ = v_a_1231_;
goto v___jp_1252_;
}
else
{
lean_object* v___x_1335_; lean_object* v___x_1336_; uint8_t v___x_1337_; 
v___x_1335_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4));
v___x_1336_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7);
v___x_1337_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1249_, v_options_1247_, v___x_1336_);
if (v___x_1337_ == 0)
{
v___y_1253_ = v_a_1222_;
v___y_1254_ = v_a_1223_;
v___y_1255_ = v_a_1224_;
v___y_1256_ = v_a_1225_;
v___y_1257_ = v_a_1226_;
v___y_1258_ = v_a_1227_;
v___y_1259_ = v_a_1228_;
v___y_1260_ = v_a_1229_;
v___y_1261_ = v_a_1230_;
v___y_1262_ = v_a_1231_;
goto v___jp_1252_;
}
else
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
lean_inc_ref(v_expr_1221_);
v___x_1338_ = l_Lean_MessageData_ofExpr(v_expr_1221_);
v___x_1339_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9);
v___x_1340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1338_);
lean_ctor_set(v___x_1340_, 1, v___x_1339_);
lean_inc(v_size_1248_);
v___x_1341_ = l_Nat_reprFast(v_size_1248_);
v___x_1342_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1341_);
v___x_1343_ = l_Lean_MessageData_ofFormat(v___x_1342_);
v___x_1344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1340_);
lean_ctor_set(v___x_1344_, 1, v___x_1343_);
v___x_1345_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(v___x_1335_, v___x_1344_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_dec_ref_known(v___x_1345_, 1);
v___y_1253_ = v_a_1222_;
v___y_1254_ = v_a_1223_;
v___y_1255_ = v_a_1224_;
v___y_1256_ = v_a_1225_;
v___y_1257_ = v_a_1226_;
v___y_1258_ = v_a_1227_;
v___y_1259_ = v_a_1228_;
v___y_1260_ = v_a_1229_;
v___y_1261_ = v_a_1230_;
v___y_1262_ = v_a_1231_;
goto v___jp_1252_;
}
else
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1353_; 
lean_dec_ref(v___f_1251_);
lean_dec(v_size_1248_);
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1230_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_a_1225_);
lean_dec_ref(v_a_1224_);
lean_dec(v_a_1223_);
lean_dec(v_a_1222_);
lean_dec_ref(v_expr_1221_);
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1348_ = v___x_1345_;
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1345_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1351_; 
if (v_isShared_1349_ == 0)
{
v___x_1351_ = v___x_1348_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_a_1346_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
}
v___jp_1252_:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_1264_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1263_, v___f_1251_, v___y_1253_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v___x_1265_; 
lean_dec_ref_known(v___x_1264_, 1);
lean_inc_ref(v_expr_1221_);
v___x_1265_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_1263_, v_expr_1221_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v___x_1266_; 
lean_dec_ref_known(v___x_1265_, 1);
lean_inc(v_size_1248_);
lean_inc_ref(v_expr_1221_);
v___x_1266_ = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(v_expr_1221_, v_size_1248_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v___x_1267_; 
lean_dec_ref_known(v___x_1266_, 1);
lean_inc(v_size_1248_);
lean_inc_ref(v_expr_1221_);
v___x_1267_ = l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg(v_expr_1221_, v_size_1248_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v___x_1268_; 
lean_dec_ref_known(v___x_1267_, 1);
lean_inc_ref(v_expr_1221_);
v___x_1268_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm(v_expr_1221_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1294_; 
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1271_ = v___x_1268_;
v_isShared_1272_ = v_isSharedCheck_1294_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1268_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1294_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
uint8_t v___x_1273_; 
v___x_1273_ = lean_unbox(v_a_1269_);
lean_dec(v_a_1269_);
if (v___x_1273_ == 0)
{
lean_object* v___x_1275_; 
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v_expr_1221_);
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 0, v_size_1248_);
v___x_1275_ = v___x_1271_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_size_1248_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
else
{
lean_object* v___x_1277_; 
lean_del_object(v___x_1271_);
lean_inc(v_size_1248_);
v___x_1277_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt(v_expr_1221_, v_size_1248_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec(v___y_1253_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1284_; 
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1284_ == 0)
{
lean_object* v_unused_1285_; 
v_unused_1285_ = lean_ctor_get(v___x_1277_, 0);
lean_dec(v_unused_1285_);
v___x_1279_ = v___x_1277_;
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
else
{
lean_dec(v___x_1277_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1282_; 
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 0, v_size_1248_);
v___x_1282_ = v___x_1279_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_size_1248_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
lean_dec(v_size_1248_);
v_a_1286_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1277_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1277_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
}
}
else
{
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec(v_size_1248_);
lean_dec_ref(v_expr_1221_);
v_a_1295_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1268_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1268_);
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
else
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec(v_size_1248_);
lean_dec_ref(v_expr_1221_);
v_a_1303_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v___x_1267_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1267_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
if (v_isShared_1306_ == 0)
{
v___x_1308_ = v___x_1305_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_a_1303_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
else
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec(v_size_1248_);
lean_dec_ref(v_expr_1221_);
v_a_1311_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v___x_1266_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1266_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1311_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec(v_size_1248_);
lean_dec_ref(v_expr_1221_);
v_a_1319_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1265_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1265_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1319_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec(v_size_1248_);
lean_dec_ref(v_expr_1221_);
v_a_1327_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1264_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1264_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
}
else
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1230_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_a_1225_);
lean_dec_ref(v_a_1224_);
lean_dec(v_a_1223_);
lean_dec(v_a_1222_);
lean_dec_ref(v_expr_1221_);
v_a_1354_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1356_ = v___x_1244_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1244_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1359_; 
if (v_isShared_1357_ == 0)
{
v___x_1359_ = v___x_1356_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1354_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
}
}
else
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1230_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_a_1225_);
lean_dec_ref(v_a_1224_);
lean_dec(v_a_1223_);
lean_dec(v_a_1222_);
lean_dec_ref(v_expr_1221_);
v_a_1363_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1233_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1233_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___boxed(lean_object* v_expr_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = lean_grind_cutsat_mk_var(v_expr_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0(lean_object* v_00_u03b2_1384_, lean_object* v_x_1385_, lean_object* v_x_1386_){
_start:
{
lean_object* v___x_1387_; 
v___x_1387_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(v_x_1385_, v_x_1386_);
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___boxed(lean_object* v_00_u03b2_1388_, lean_object* v_x_1389_, lean_object* v_x_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0(v_00_u03b2_1388_, v_x_1389_, v_x_1390_);
lean_dec_ref(v_x_1390_);
lean_dec_ref(v_x_1389_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1(lean_object* v_00_u03b2_1392_, lean_object* v_x_1393_, lean_object* v_x_1394_, lean_object* v_x_1395_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg(v_x_1393_, v_x_1394_, v_x_1395_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2(lean_object* v_cls_1397_, lean_object* v_msg_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v___x_1410_; 
v___x_1410_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(v_cls_1397_, v_msg_1398_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___boxed(lean_object* v_cls_1411_, lean_object* v_msg_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2(v_cls_1411_, v_msg_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec(v___y_1414_);
lean_dec(v___y_1413_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0(lean_object* v_00_u03b2_1425_, lean_object* v_x_1426_, size_t v_x_1427_, lean_object* v_x_1428_){
_start:
{
lean_object* v___x_1429_; 
v___x_1429_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(v_x_1426_, v_x_1427_, v_x_1428_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1430_, lean_object* v_x_1431_, lean_object* v_x_1432_, lean_object* v_x_1433_){
_start:
{
size_t v_x_31577__boxed_1434_; lean_object* v_res_1435_; 
v_x_31577__boxed_1434_ = lean_unbox_usize(v_x_1432_);
lean_dec(v_x_1432_);
v_res_1435_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0(v_00_u03b2_1430_, v_x_1431_, v_x_31577__boxed_1434_, v_x_1433_);
lean_dec_ref(v_x_1433_);
lean_dec_ref(v_x_1431_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2(lean_object* v_00_u03b2_1436_, lean_object* v_x_1437_, size_t v_x_1438_, size_t v_x_1439_, lean_object* v_x_1440_, lean_object* v_x_1441_){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_x_1437_, v_x_1438_, v_x_1439_, v_x_1440_, v_x_1441_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1443_, lean_object* v_x_1444_, lean_object* v_x_1445_, lean_object* v_x_1446_, lean_object* v_x_1447_, lean_object* v_x_1448_){
_start:
{
size_t v_x_31588__boxed_1449_; size_t v_x_31589__boxed_1450_; lean_object* v_res_1451_; 
v_x_31588__boxed_1449_ = lean_unbox_usize(v_x_1445_);
lean_dec(v_x_1445_);
v_x_31589__boxed_1450_ = lean_unbox_usize(v_x_1446_);
lean_dec(v_x_1446_);
v_res_1451_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2(v_00_u03b2_1443_, v_x_1444_, v_x_31588__boxed_1449_, v_x_31589__boxed_1450_, v_x_1447_, v_x_1448_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1452_, lean_object* v_keys_1453_, lean_object* v_vals_1454_, lean_object* v_heq_1455_, lean_object* v_i_1456_, lean_object* v_k_1457_){
_start:
{
lean_object* v___x_1458_; 
v___x_1458_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(v_keys_1453_, v_vals_1454_, v_i_1456_, v_k_1457_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1459_, lean_object* v_keys_1460_, lean_object* v_vals_1461_, lean_object* v_heq_1462_, lean_object* v_i_1463_, lean_object* v_k_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1(v_00_u03b2_1459_, v_keys_1460_, v_vals_1461_, v_heq_1462_, v_i_1463_, v_k_1464_);
lean_dec_ref(v_k_1464_);
lean_dec_ref(v_vals_1461_);
lean_dec_ref(v_keys_1460_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1466_, lean_object* v_n_1467_, lean_object* v_k_1468_, lean_object* v_v_1469_){
_start:
{
lean_object* v___x_1470_; 
v___x_1470_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4___redArg(v_n_1467_, v_k_1468_, v_v_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1471_, size_t v_depth_1472_, lean_object* v_keys_1473_, lean_object* v_vals_1474_, lean_object* v_heq_1475_, lean_object* v_i_1476_, lean_object* v_entries_1477_){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(v_depth_1472_, v_keys_1473_, v_vals_1474_, v_i_1476_, v_entries_1477_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1479_, lean_object* v_depth_1480_, lean_object* v_keys_1481_, lean_object* v_vals_1482_, lean_object* v_heq_1483_, lean_object* v_i_1484_, lean_object* v_entries_1485_){
_start:
{
size_t v_depth_boxed_1486_; lean_object* v_res_1487_; 
v_depth_boxed_1486_ = lean_unbox_usize(v_depth_1480_);
lean_dec(v_depth_1480_);
v_res_1487_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5(v_00_u03b2_1479_, v_depth_boxed_1486_, v_keys_1481_, v_vals_1482_, v_heq_1483_, v_i_1484_, v_entries_1485_);
lean_dec_ref(v_vals_1482_);
lean_dec_ref(v_keys_1481_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_1488_, lean_object* v_x_1489_, lean_object* v_x_1490_, lean_object* v_x_1491_, lean_object* v_x_1492_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7___redArg(v_x_1489_, v_x_1490_, v_x_1491_, v_x_1492_);
return v___x_1493_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2(void){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1497_ = lean_box(0);
v___x_1498_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__1));
v___x_1499_ = l_Lean_mkConst(v___x_1498_, v___x_1497_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(lean_object* v_e_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_){
_start:
{
lean_object* v___x_1506_; 
lean_inc(v_a_1504_);
lean_inc_ref(v_a_1503_);
lean_inc(v_a_1502_);
lean_inc_ref(v_a_1501_);
v___x_1506_ = lean_infer_type(v_e_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_);
if (lean_obj_tag(v___x_1506_) == 0)
{
lean_object* v_a_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v_a_1507_ = lean_ctor_get(v___x_1506_, 0);
lean_inc(v_a_1507_);
lean_dec_ref_known(v___x_1506_, 1);
v___x_1508_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2);
v___x_1509_ = l_Lean_Meta_isExprDefEq(v_a_1507_, v___x_1508_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_);
return v___x_1509_;
}
else
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
v_a_1510_ = lean_ctor_get(v___x_1506_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1512_ = v___x_1506_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1506_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1510_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___boxed(lean_object* v_e_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(v_e_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_);
lean_dec(v_a_1522_);
lean_dec_ref(v_a_1521_);
lean_dec(v_a_1520_);
lean_dec_ref(v_a_1519_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt(lean_object* v_e_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_){
_start:
{
lean_object* v___x_1537_; 
v___x_1537_ = l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(v_e_1525_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___boxed(lean_object* v_e_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_Lean_Meta_Grind_Arith_Cutsat_isInt(v_e_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_);
lean_dec(v_a_1548_);
lean_dec_ref(v_a_1547_);
lean_dec(v_a_1546_);
lean_dec_ref(v_a_1545_);
lean_dec(v_a_1544_);
lean_dec_ref(v_a_1543_);
lean_dec(v_a_1542_);
lean_dec_ref(v_a_1541_);
lean_dec(v_a_1540_);
lean_dec(v_a_1539_);
return v_res_1550_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4(void){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1557_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__3));
v___x_1558_ = l_Lean_stringToMessageData(v___x_1557_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(lean_object* v_e_1559_, uint8_t v_report_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_){
_start:
{
lean_object* v___x_1571_; 
lean_inc_ref(v_e_1559_);
v___x_1571_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1559_, v_a_1564_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1642_; 
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1574_ = v___x_1571_;
v_isShared_1575_ = v_isSharedCheck_1642_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1571_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1642_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1581_; uint8_t v___x_1582_; 
v___x_1581_ = l_Lean_Expr_cleanupAnnotations(v_a_1572_);
v___x_1582_ = l_Lean_Expr_isApp(v___x_1581_);
if (v___x_1582_ == 0)
{
lean_dec_ref(v___x_1581_);
lean_dec_ref(v_e_1559_);
goto v___jp_1576_;
}
else
{
lean_object* v_arg_1583_; lean_object* v___x_1584_; uint8_t v___x_1585_; 
v_arg_1583_ = lean_ctor_get(v___x_1581_, 1);
lean_inc_ref(v_arg_1583_);
v___x_1584_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1581_);
v___x_1585_ = l_Lean_Expr_isApp(v___x_1584_);
if (v___x_1585_ == 0)
{
lean_dec_ref(v___x_1584_);
lean_dec_ref(v_arg_1583_);
lean_dec_ref(v_e_1559_);
goto v___jp_1576_;
}
else
{
lean_object* v_arg_1586_; lean_object* v___x_1587_; uint8_t v___x_1588_; 
v_arg_1586_ = lean_ctor_get(v___x_1584_, 1);
lean_inc_ref(v_arg_1586_);
v___x_1587_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1584_);
v___x_1588_ = l_Lean_Expr_isApp(v___x_1587_);
if (v___x_1588_ == 0)
{
lean_dec_ref(v___x_1587_);
lean_dec_ref(v_arg_1586_);
lean_dec_ref(v_arg_1583_);
lean_dec_ref(v_e_1559_);
goto v___jp_1576_;
}
else
{
lean_object* v_arg_1589_; lean_object* v___x_1590_; uint8_t v___x_1591_; 
v_arg_1589_ = lean_ctor_get(v___x_1587_, 1);
lean_inc_ref(v_arg_1589_);
v___x_1590_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1587_);
v___x_1591_ = l_Lean_Expr_isApp(v___x_1590_);
if (v___x_1591_ == 0)
{
lean_dec_ref(v___x_1590_);
lean_dec_ref(v_arg_1589_);
lean_dec_ref(v_arg_1586_);
lean_dec_ref(v_arg_1583_);
lean_dec_ref(v_e_1559_);
goto v___jp_1576_;
}
else
{
lean_object* v___x_1592_; uint8_t v___x_1593_; 
v___x_1592_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1590_);
v___x_1593_ = l_Lean_Expr_isApp(v___x_1592_);
if (v___x_1593_ == 0)
{
lean_dec_ref(v___x_1592_);
lean_dec_ref(v_arg_1589_);
lean_dec_ref(v_arg_1586_);
lean_dec_ref(v_arg_1583_);
lean_dec_ref(v_e_1559_);
goto v___jp_1576_;
}
else
{
lean_object* v___x_1594_; uint8_t v___x_1595_; 
v___x_1594_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1592_);
v___x_1595_ = l_Lean_Expr_isApp(v___x_1594_);
if (v___x_1595_ == 0)
{
lean_dec_ref(v___x_1594_);
lean_dec_ref(v_arg_1589_);
lean_dec_ref(v_arg_1586_);
lean_dec_ref(v_arg_1583_);
lean_dec_ref(v_e_1559_);
goto v___jp_1576_;
}
else
{
lean_object* v___x_1596_; lean_object* v___x_1597_; uint8_t v___x_1598_; 
v___x_1596_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1594_);
v___x_1597_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__2));
v___x_1598_ = l_Lean_Expr_isConstOf(v___x_1596_, v___x_1597_);
lean_dec_ref(v___x_1596_);
if (v___x_1598_ == 0)
{
lean_dec_ref(v_arg_1589_);
lean_dec_ref(v_arg_1586_);
lean_dec_ref(v_arg_1583_);
lean_dec_ref(v_e_1559_);
goto v___jp_1576_;
}
else
{
lean_object* v___x_1599_; 
lean_del_object(v___x_1574_);
v___x_1599_ = l_Lean_Meta_Structural_isInstHAddInt___redArg(v_arg_1589_, v_a_1564_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1633_; 
v_a_1600_ = lean_ctor_get(v___x_1599_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1602_ = v___x_1599_;
v_isShared_1603_ = v_isSharedCheck_1633_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1599_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1633_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
uint8_t v___x_1604_; 
v___x_1604_ = lean_unbox(v_a_1600_);
lean_dec(v_a_1600_);
if (v___x_1604_ == 0)
{
lean_del_object(v___x_1602_);
lean_dec_ref(v_arg_1586_);
lean_dec_ref(v_arg_1583_);
if (v_report_1560_ == 0)
{
lean_dec_ref(v_e_1559_);
goto v___jp_1568_;
}
else
{
lean_object* v___x_1605_; 
v___x_1605_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1561_);
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_object* v_a_1606_; uint8_t v_verbose_1607_; 
v_a_1606_ = lean_ctor_get(v___x_1605_, 0);
lean_inc(v_a_1606_);
lean_dec_ref_known(v___x_1605_, 1);
v_verbose_1607_ = lean_ctor_get_uint8(v_a_1606_, 0);
lean_dec(v_a_1606_);
if (v_verbose_1607_ == 0)
{
lean_dec_ref(v_e_1559_);
goto v___jp_1568_;
}
else
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1608_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4);
v___x_1609_ = l_Lean_indentExpr(v_e_1559_);
v___x_1610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1608_);
lean_ctor_set(v___x_1610_, 1, v___x_1609_);
v___x_1611_ = l_Lean_Meta_Sym_reportIssue(v___x_1610_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_dec_ref_known(v___x_1611_, 1);
goto v___jp_1568_;
}
else
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v___x_1611_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1611_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1612_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
lean_dec_ref(v_e_1559_);
v_a_1620_ = lean_ctor_get(v___x_1605_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1605_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1605_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1605_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
}
else
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1631_; 
lean_dec_ref(v_e_1559_);
v___x_1628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1628_, 0, v_arg_1586_);
lean_ctor_set(v___x_1628_, 1, v_arg_1583_);
v___x_1629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1628_);
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 0, v___x_1629_);
v___x_1631_ = v___x_1602_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v___x_1629_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
}
else
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1641_; 
lean_dec_ref(v_arg_1586_);
lean_dec_ref(v_arg_1583_);
lean_dec_ref(v_e_1559_);
v_a_1634_ = lean_ctor_get(v___x_1599_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1636_ = v___x_1599_;
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1599_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1639_; 
if (v_isShared_1637_ == 0)
{
v___x_1639_ = v___x_1636_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_a_1634_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
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
v___jp_1576_:
{
lean_object* v___x_1577_; lean_object* v___x_1579_; 
v___x_1577_ = lean_box(0);
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 0, v___x_1577_);
v___x_1579_ = v___x_1574_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1577_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
lean_dec_ref(v_e_1559_);
v_a_1643_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1571_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1571_);
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
v___jp_1568_:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1569_ = lean_box(0);
v___x_1570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1569_);
return v___x_1570_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___boxed(lean_object* v_e_1651_, lean_object* v_report_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_){
_start:
{
uint8_t v_report_boxed_1660_; lean_object* v_res_1661_; 
v_report_boxed_1660_ = lean_unbox(v_report_1652_);
v_res_1661_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_1651_, v_report_boxed_1660_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_);
lean_dec(v_a_1658_);
lean_dec_ref(v_a_1657_);
lean_dec(v_a_1656_);
lean_dec_ref(v_a_1655_);
lean_dec(v_a_1654_);
lean_dec_ref(v_a_1653_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f(lean_object* v_e_1662_, uint8_t v_report_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_){
_start:
{
lean_object* v___x_1675_; 
v___x_1675_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_1662_, v_report_1663_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___boxed(lean_object* v_e_1676_, lean_object* v_report_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_){
_start:
{
uint8_t v_report_boxed_1689_; lean_object* v_res_1690_; 
v_report_boxed_1689_ = lean_unbox(v_report_1677_);
v_res_1690_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f(v_e_1676_, v_report_boxed_1689_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_);
lean_dec(v_a_1687_);
lean_dec_ref(v_a_1686_);
lean_dec(v_a_1685_);
lean_dec_ref(v_a_1684_);
lean_dec(v_a_1683_);
lean_dec_ref(v_a_1682_);
lean_dec(v_a_1681_);
lean_dec_ref(v_a_1680_);
lean_dec(v_a_1679_);
lean_dec(v_a_1678_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(lean_object* v_e_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_){
_start:
{
uint8_t v___x_1699_; lean_object* v___x_1700_; 
v___x_1699_ = 0;
v___x_1700_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_1691_, v___x_1699_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1714_; 
v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1703_ = v___x_1700_;
v_isShared_1704_ = v_isSharedCheck_1714_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1700_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1714_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
if (lean_obj_tag(v_a_1701_) == 0)
{
lean_object* v___x_1705_; lean_object* v___x_1707_; 
v___x_1705_ = lean_box(v___x_1699_);
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 0, v___x_1705_);
v___x_1707_ = v___x_1703_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v___x_1705_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
else
{
uint8_t v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1712_; 
lean_dec_ref_known(v_a_1701_, 1);
v___x_1709_ = 1;
v___x_1710_ = lean_box(v___x_1709_);
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 0, v___x_1710_);
v___x_1712_ = v___x_1703_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1710_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
else
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1722_; 
v_a_1715_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1717_ = v___x_1700_;
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1700_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_a_1715_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg___boxed(lean_object* v_e_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(v_e_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_);
lean_dec(v_a_1729_);
lean_dec_ref(v_a_1728_);
lean_dec(v_a_1727_);
lean_dec_ref(v_a_1726_);
lean_dec(v_a_1725_);
lean_dec_ref(v_a_1724_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd(lean_object* v_e_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(v_e_1732_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___boxed(lean_object* v_e_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd(v_e_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_);
lean_dec(v_a_1755_);
lean_dec_ref(v_a_1754_);
lean_dec(v_a_1753_);
lean_dec_ref(v_a_1752_);
lean_dec(v_a_1751_);
lean_dec_ref(v_a_1750_);
lean_dec(v_a_1749_);
lean_dec_ref(v_a_1748_);
lean_dec(v_a_1747_);
lean_dec(v_a_1746_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(lean_object* v_e_1758_, uint8_t v_report_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_){
_start:
{
lean_object* v___x_1770_; 
lean_inc_ref(v_e_1758_);
v___x_1770_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1758_, v_a_1763_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1862_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1773_ = v___x_1770_;
v_isShared_1774_ = v_isSharedCheck_1862_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1770_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1862_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1780_; uint8_t v___x_1781_; 
v___x_1780_ = l_Lean_Expr_cleanupAnnotations(v_a_1771_);
v___x_1781_ = l_Lean_Expr_isApp(v___x_1780_);
if (v___x_1781_ == 0)
{
lean_dec_ref(v___x_1780_);
lean_dec_ref(v_e_1758_);
goto v___jp_1775_;
}
else
{
lean_object* v_arg_1782_; lean_object* v___x_1783_; uint8_t v___x_1784_; 
v_arg_1782_ = lean_ctor_get(v___x_1780_, 1);
lean_inc_ref(v_arg_1782_);
v___x_1783_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1780_);
v___x_1784_ = l_Lean_Expr_isApp(v___x_1783_);
if (v___x_1784_ == 0)
{
lean_dec_ref(v___x_1783_);
lean_dec_ref(v_arg_1782_);
lean_dec_ref(v_e_1758_);
goto v___jp_1775_;
}
else
{
lean_object* v_arg_1785_; lean_object* v___x_1786_; uint8_t v___x_1787_; 
v_arg_1785_ = lean_ctor_get(v___x_1783_, 1);
lean_inc_ref(v_arg_1785_);
v___x_1786_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1783_);
v___x_1787_ = l_Lean_Expr_isApp(v___x_1786_);
if (v___x_1787_ == 0)
{
lean_dec_ref(v___x_1786_);
lean_dec_ref(v_arg_1785_);
lean_dec_ref(v_arg_1782_);
lean_dec_ref(v_e_1758_);
goto v___jp_1775_;
}
else
{
lean_object* v_arg_1788_; lean_object* v___x_1789_; uint8_t v___x_1790_; 
v_arg_1788_ = lean_ctor_get(v___x_1786_, 1);
lean_inc_ref(v_arg_1788_);
v___x_1789_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1786_);
v___x_1790_ = l_Lean_Expr_isApp(v___x_1789_);
if (v___x_1790_ == 0)
{
lean_dec_ref(v___x_1789_);
lean_dec_ref(v_arg_1788_);
lean_dec_ref(v_arg_1785_);
lean_dec_ref(v_arg_1782_);
lean_dec_ref(v_e_1758_);
goto v___jp_1775_;
}
else
{
lean_object* v___x_1791_; uint8_t v___x_1792_; 
v___x_1791_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1789_);
v___x_1792_ = l_Lean_Expr_isApp(v___x_1791_);
if (v___x_1792_ == 0)
{
lean_dec_ref(v___x_1791_);
lean_dec_ref(v_arg_1788_);
lean_dec_ref(v_arg_1785_);
lean_dec_ref(v_arg_1782_);
lean_dec_ref(v_e_1758_);
goto v___jp_1775_;
}
else
{
lean_object* v___x_1793_; uint8_t v___x_1794_; 
v___x_1793_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1791_);
v___x_1794_ = l_Lean_Expr_isApp(v___x_1793_);
if (v___x_1794_ == 0)
{
lean_dec_ref(v___x_1793_);
lean_dec_ref(v_arg_1788_);
lean_dec_ref(v_arg_1785_);
lean_dec_ref(v_arg_1782_);
lean_dec_ref(v_e_1758_);
goto v___jp_1775_;
}
else
{
lean_object* v___x_1795_; lean_object* v___x_1796_; uint8_t v___x_1797_; 
v___x_1795_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1793_);
v___x_1796_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11));
v___x_1797_ = l_Lean_Expr_isConstOf(v___x_1795_, v___x_1796_);
lean_dec_ref(v___x_1795_);
if (v___x_1797_ == 0)
{
lean_dec_ref(v_arg_1788_);
lean_dec_ref(v_arg_1785_);
lean_dec_ref(v_arg_1782_);
lean_dec_ref(v_e_1758_);
goto v___jp_1775_;
}
else
{
lean_object* v___x_1798_; 
lean_del_object(v___x_1773_);
v___x_1798_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_1788_, v_a_1763_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_object* v_a_1799_; uint8_t v___x_1800_; 
v_a_1799_ = lean_ctor_get(v___x_1798_, 0);
lean_inc(v_a_1799_);
lean_dec_ref_known(v___x_1798_, 1);
v___x_1800_ = lean_unbox(v_a_1799_);
lean_dec(v_a_1799_);
if (v___x_1800_ == 0)
{
lean_dec_ref(v_arg_1785_);
lean_dec_ref(v_arg_1782_);
if (v_report_1759_ == 0)
{
lean_dec_ref(v_e_1758_);
goto v___jp_1767_;
}
else
{
lean_object* v___x_1801_; 
v___x_1801_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1760_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v_a_1802_; uint8_t v_verbose_1803_; 
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
lean_inc(v_a_1802_);
lean_dec_ref_known(v___x_1801_, 1);
v_verbose_1803_ = lean_ctor_get_uint8(v_a_1802_, 0);
lean_dec(v_a_1802_);
if (v_verbose_1803_ == 0)
{
lean_dec_ref(v_e_1758_);
goto v___jp_1767_;
}
else
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1804_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4);
v___x_1805_ = l_Lean_indentExpr(v_e_1758_);
v___x_1806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1804_);
lean_ctor_set(v___x_1806_, 1, v___x_1805_);
v___x_1807_ = l_Lean_Meta_Sym_reportIssue(v___x_1806_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_, v_a_1765_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_dec_ref_known(v___x_1807_, 1);
goto v___jp_1767_;
}
else
{
lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1815_; 
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1810_ = v___x_1807_;
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1807_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1813_; 
if (v_isShared_1811_ == 0)
{
v___x_1813_ = v___x_1810_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1808_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
}
}
else
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1823_; 
lean_dec_ref(v_e_1758_);
v_a_1816_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1818_ = v___x_1801_;
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1801_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1821_; 
if (v_isShared_1819_ == 0)
{
v___x_1821_ = v___x_1818_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_a_1816_);
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
}
else
{
lean_object* v___x_1824_; 
lean_dec_ref(v_e_1758_);
v___x_1824_ = l_Lean_Meta_getIntValue_x3f(v_arg_1785_, v_a_1762_, v_a_1763_, v_a_1764_, v_a_1765_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1845_; 
v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1827_ = v___x_1824_;
v_isShared_1828_ = v_isSharedCheck_1845_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1824_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1845_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
if (lean_obj_tag(v_a_1825_) == 1)
{
lean_object* v_val_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1840_; 
v_val_1829_ = lean_ctor_get(v_a_1825_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v_a_1825_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1831_ = v_a_1825_;
v_isShared_1832_ = v_isSharedCheck_1840_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_val_1829_);
lean_dec(v_a_1825_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1840_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1833_; lean_object* v___x_1835_; 
v___x_1833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1833_, 0, v_val_1829_);
lean_ctor_set(v___x_1833_, 1, v_arg_1782_);
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v___x_1833_);
v___x_1835_ = v___x_1831_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1833_);
v___x_1835_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
lean_object* v___x_1837_; 
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 0, v___x_1835_);
v___x_1837_ = v___x_1827_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v___x_1835_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
}
else
{
lean_object* v___x_1841_; lean_object* v___x_1843_; 
lean_dec(v_a_1825_);
lean_dec_ref(v_arg_1782_);
v___x_1841_ = lean_box(0);
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 0, v___x_1841_);
v___x_1843_ = v___x_1827_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1841_);
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
else
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1853_; 
lean_dec_ref(v_arg_1782_);
v_a_1846_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1848_ = v___x_1824_;
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1824_);
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
}
}
else
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
lean_dec_ref(v_arg_1785_);
lean_dec_ref(v_arg_1782_);
lean_dec_ref(v_e_1758_);
v_a_1854_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1856_ = v___x_1798_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1798_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_a_1854_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
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
v___jp_1775_:
{
lean_object* v___x_1776_; lean_object* v___x_1778_; 
v___x_1776_ = lean_box(0);
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 0, v___x_1776_);
v___x_1778_ = v___x_1773_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1776_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
else
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1870_; 
lean_dec_ref(v_e_1758_);
v_a_1863_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1865_ = v___x_1770_;
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1770_);
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
v___jp_1767_:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1768_ = lean_box(0);
v___x_1769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1768_);
return v___x_1769_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg___boxed(lean_object* v_e_1871_, lean_object* v_report_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_){
_start:
{
uint8_t v_report_boxed_1880_; lean_object* v_res_1881_; 
v_report_boxed_1880_ = lean_unbox(v_report_1872_);
v_res_1881_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1871_, v_report_boxed_1880_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_);
lean_dec(v_a_1878_);
lean_dec_ref(v_a_1877_);
lean_dec(v_a_1876_);
lean_dec_ref(v_a_1875_);
lean_dec(v_a_1874_);
lean_dec_ref(v_a_1873_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f(lean_object* v_e_1882_, uint8_t v_report_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_){
_start:
{
lean_object* v___x_1895_; 
v___x_1895_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1882_, v_report_1883_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___boxed(lean_object* v_e_1896_, lean_object* v_report_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_){
_start:
{
uint8_t v_report_boxed_1909_; lean_object* v_res_1910_; 
v_report_boxed_1909_ = lean_unbox(v_report_1897_);
v_res_1910_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f(v_e_1896_, v_report_boxed_1909_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
lean_dec(v_a_1907_);
lean_dec_ref(v_a_1906_);
lean_dec(v_a_1905_);
lean_dec_ref(v_a_1904_);
lean_dec(v_a_1903_);
lean_dec_ref(v_a_1902_);
lean_dec(v_a_1901_);
lean_dec_ref(v_a_1900_);
lean_dec(v_a_1899_);
lean_dec(v_a_1898_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(lean_object* v_e_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_){
_start:
{
uint8_t v___x_1919_; lean_object* v___x_1920_; 
v___x_1919_ = 0;
v___x_1920_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1911_, v___x_1919_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1934_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1923_ = v___x_1920_;
v_isShared_1924_ = v_isSharedCheck_1934_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1920_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1934_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
if (lean_obj_tag(v_a_1921_) == 0)
{
lean_object* v___x_1925_; lean_object* v___x_1927_; 
v___x_1925_ = lean_box(v___x_1919_);
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 0, v___x_1925_);
v___x_1927_ = v___x_1923_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1925_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
else
{
uint8_t v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1932_; 
lean_dec_ref_known(v_a_1921_, 1);
v___x_1929_ = 1;
v___x_1930_ = lean_box(v___x_1929_);
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 0, v___x_1930_);
v___x_1932_ = v___x_1923_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v___x_1930_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
}
else
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1942_; 
v_a_1935_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1937_ = v___x_1920_;
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___x_1920_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1940_; 
if (v_isShared_1938_ == 0)
{
v___x_1940_ = v___x_1937_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_a_1935_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg___boxed(lean_object* v_e_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_){
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(v_e_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_);
lean_dec(v_a_1949_);
lean_dec_ref(v_a_1948_);
lean_dec(v_a_1947_);
lean_dec_ref(v_a_1946_);
lean_dec(v_a_1945_);
lean_dec_ref(v_a_1944_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul(lean_object* v_e_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_){
_start:
{
lean_object* v___x_1964_; 
v___x_1964_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(v_e_1952_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_);
return v___x_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___boxed(lean_object* v_e_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul(v_e_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_);
lean_dec(v_a_1975_);
lean_dec_ref(v_a_1974_);
lean_dec(v_a_1973_);
lean_dec_ref(v_a_1972_);
lean_dec(v_a_1971_);
lean_dec_ref(v_a_1970_);
lean_dec(v_a_1969_);
lean_dec_ref(v_a_1968_);
lean_dec(v_a_1967_);
lean_dec(v_a_1966_);
return v_res_1977_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0(void){
_start:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1978_ = lean_unsigned_to_nat(1u);
v___x_1979_ = lean_nat_to_int(v___x_1978_);
return v___x_1979_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2(void){
_start:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1981_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__1));
v___x_1982_ = l_Lean_stringToMessageData(v___x_1981_);
return v___x_1982_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4(void){
_start:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1984_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__3));
v___x_1985_ = l_Lean_stringToMessageData(v___x_1984_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(lean_object* v_e_1986_, lean_object* v_p_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_){
_start:
{
lean_object* v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v___y_2003_; lean_object* v___y_2004_; lean_object* v___y_2005_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; uint8_t v___x_2029_; lean_object* v___x_2030_; 
v___x_2029_ = 1;
lean_inc_ref(v_e_1986_);
v___x_2030_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1986_, v___x_2029_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v_a_2031_; 
v_a_2031_ = lean_ctor_get(v___x_2030_, 0);
lean_inc(v_a_2031_);
lean_dec_ref_known(v___x_2030_, 1);
if (lean_obj_tag(v_a_2031_) == 1)
{
lean_object* v_val_2032_; lean_object* v_fst_2033_; lean_object* v_snd_2034_; lean_object* v___x_2035_; 
lean_dec_ref(v_e_1986_);
v_val_2032_ = lean_ctor_get(v_a_2031_, 0);
lean_inc(v_val_2032_);
lean_dec_ref_known(v_a_2031_, 1);
v_fst_2033_ = lean_ctor_get(v_val_2032_, 0);
lean_inc(v_fst_2033_);
v_snd_2034_ = lean_ctor_get(v_val_2032_, 1);
lean_inc(v_snd_2034_);
lean_dec(v_val_2032_);
lean_inc(v_a_1997_);
lean_inc_ref(v_a_1996_);
lean_inc(v_a_1995_);
lean_inc_ref(v_a_1994_);
lean_inc(v_a_1993_);
lean_inc_ref(v_a_1992_);
lean_inc(v_a_1991_);
lean_inc_ref(v_a_1990_);
lean_inc(v_a_1989_);
lean_inc(v_a_1988_);
v___x_2035_ = lean_grind_cutsat_mk_var(v_snd_2034_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2044_; 
v_a_2036_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2038_ = v___x_2035_;
v_isShared_2039_ = v_isSharedCheck_2044_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_2035_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2044_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2040_; lean_object* v___x_2042_; 
v___x_2040_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2040_, 0, v_fst_2033_);
lean_ctor_set(v___x_2040_, 1, v_a_2036_);
lean_ctor_set(v___x_2040_, 2, v_p_1987_);
if (v_isShared_2039_ == 0)
{
lean_ctor_set(v___x_2038_, 0, v___x_2040_);
v___x_2042_ = v___x_2038_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2040_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
else
{
lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2052_; 
lean_dec(v_fst_2033_);
lean_dec_ref(v_p_1987_);
v_a_2045_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2047_ = v___x_2035_;
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_2035_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2048_ == 0)
{
v___x_2050_ = v___x_2047_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
else
{
lean_object* v___x_2053_; 
lean_dec(v_a_2031_);
lean_inc_ref(v_e_1986_);
v___x_2053_ = l_Lean_Meta_getIntValue_x3f(v_e_1986_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v_a_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2095_; 
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2056_ = v___x_2053_;
v_isShared_2057_ = v_isSharedCheck_2095_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_a_2054_);
lean_dec(v___x_2053_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2095_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
if (lean_obj_tag(v_a_2054_) == 1)
{
lean_object* v_val_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2094_; 
v_val_2058_ = lean_ctor_get(v_a_2054_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v_a_2054_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2060_ = v_a_2054_;
v_isShared_2061_ = v_isSharedCheck_2094_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_val_2058_);
lean_dec(v_a_2054_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2094_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
uint8_t v___x_2062_; 
v___x_2062_ = l_Int_Internal_Linear_Poly_isZero(v_p_1987_);
if (v___x_2062_ == 0)
{
lean_object* v___x_2063_; 
lean_del_object(v___x_2060_);
lean_dec(v_val_2058_);
lean_del_object(v___x_2056_);
v___x_2063_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1992_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v_a_2064_; uint8_t v_verbose_2065_; 
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_a_2064_);
lean_dec_ref_known(v___x_2063_, 1);
v_verbose_2065_ = lean_ctor_get_uint8(v_a_2064_, 0);
lean_dec(v_a_2064_);
if (v_verbose_2065_ == 0)
{
v___y_2000_ = v_a_1988_;
v___y_2001_ = v_a_1989_;
v___y_2002_ = v_a_1990_;
v___y_2003_ = v_a_1991_;
v___y_2004_ = v_a_1992_;
v___y_2005_ = v_a_1993_;
v___y_2006_ = v_a_1994_;
v___y_2007_ = v_a_1995_;
v___y_2008_ = v_a_1996_;
v___y_2009_ = v_a_1997_;
goto v___jp_1999_;
}
else
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2066_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2);
lean_inc_ref(v_e_1986_);
v___x_2067_ = l_Lean_indentExpr(v_e_1986_);
v___x_2068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2066_);
lean_ctor_set(v___x_2068_, 1, v___x_2067_);
v___x_2069_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4);
v___x_2070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2068_);
lean_ctor_set(v___x_2070_, 1, v___x_2069_);
v___x_2071_ = l_Lean_Meta_Sym_reportIssue(v___x_2070_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_dec_ref_known(v___x_2071_, 1);
v___y_2000_ = v_a_1988_;
v___y_2001_ = v_a_1989_;
v___y_2002_ = v_a_1990_;
v___y_2003_ = v_a_1991_;
v___y_2004_ = v_a_1992_;
v___y_2005_ = v_a_1993_;
v___y_2006_ = v_a_1994_;
v___y_2007_ = v_a_1995_;
v___y_2008_ = v_a_1996_;
v___y_2009_ = v_a_1997_;
goto v___jp_1999_;
}
else
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
lean_dec_ref(v_p_1987_);
lean_dec_ref(v_e_1986_);
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2071_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2071_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2075_ == 0)
{
v___x_2077_ = v___x_2074_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2072_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
}
else
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2087_; 
lean_dec_ref(v_p_1987_);
lean_dec_ref(v_e_1986_);
v_a_2080_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2082_ = v___x_2063_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2063_);
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
else
{
lean_object* v___x_2089_; 
lean_dec_ref(v_p_1987_);
lean_dec_ref(v_e_1986_);
if (v_isShared_2061_ == 0)
{
lean_ctor_set_tag(v___x_2060_, 0);
v___x_2089_ = v___x_2060_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_val_2058_);
v___x_2089_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
lean_object* v___x_2091_; 
if (v_isShared_2057_ == 0)
{
lean_ctor_set(v___x_2056_, 0, v___x_2089_);
v___x_2091_ = v___x_2056_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v___x_2089_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
}
else
{
lean_del_object(v___x_2056_);
lean_dec(v_a_2054_);
v___y_2000_ = v_a_1988_;
v___y_2001_ = v_a_1989_;
v___y_2002_ = v_a_1990_;
v___y_2003_ = v_a_1991_;
v___y_2004_ = v_a_1992_;
v___y_2005_ = v_a_1993_;
v___y_2006_ = v_a_1994_;
v___y_2007_ = v_a_1995_;
v___y_2008_ = v_a_1996_;
v___y_2009_ = v_a_1997_;
goto v___jp_1999_;
}
}
}
else
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
lean_dec_ref(v_p_1987_);
lean_dec_ref(v_e_1986_);
v_a_2096_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2098_ = v___x_2053_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2053_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_a_2096_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
}
else
{
lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2111_; 
lean_dec_ref(v_p_1987_);
lean_dec_ref(v_e_1986_);
v_a_2104_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2106_ = v___x_2030_;
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2030_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2109_; 
if (v_isShared_2107_ == 0)
{
v___x_2109_ = v___x_2106_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_a_2104_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
v___jp_1999_:
{
lean_object* v___x_2010_; 
lean_inc(v___y_2009_);
lean_inc_ref(v___y_2008_);
lean_inc(v___y_2007_);
lean_inc_ref(v___y_2006_);
lean_inc(v___y_2005_);
lean_inc_ref(v___y_2004_);
lean_inc(v___y_2003_);
lean_inc_ref(v___y_2002_);
lean_inc(v___y_2001_);
lean_inc(v___y_2000_);
v___x_2010_ = lean_grind_cutsat_mk_var(v_e_1986_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2020_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2013_ = v___x_2010_;
v_isShared_2014_ = v_isSharedCheck_2020_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_2010_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2020_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2018_; 
v___x_2015_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0);
v___x_2016_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2015_);
lean_ctor_set(v___x_2016_, 1, v_a_2011_);
lean_ctor_set(v___x_2016_, 2, v_p_1987_);
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 0, v___x_2016_);
v___x_2018_ = v___x_2013_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_2016_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
else
{
lean_object* v_a_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2028_; 
lean_dec_ref(v_p_1987_);
v_a_2021_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2023_ = v___x_2010_;
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_a_2021_);
lean_dec(v___x_2010_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2026_; 
if (v_isShared_2024_ == 0)
{
v___x_2026_ = v___x_2023_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_a_2021_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___boxed(lean_object* v_e_2112_, lean_object* v_p_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_){
_start:
{
lean_object* v_res_2125_; 
v_res_2125_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_e_2112_, v_p_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_);
lean_dec(v_a_2123_);
lean_dec_ref(v_a_2122_);
lean_dec(v_a_2121_);
lean_dec_ref(v_a_2120_);
lean_dec(v_a_2119_);
lean_dec_ref(v_a_2118_);
lean_dec(v_a_2117_);
lean_dec_ref(v_a_2116_);
lean_dec(v_a_2115_);
lean_dec(v_a_2114_);
return v_res_2125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go(lean_object* v_e_2126_, lean_object* v_p_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_){
_start:
{
uint8_t v___x_2139_; lean_object* v___x_2140_; 
v___x_2139_ = 1;
lean_inc_ref(v_e_2126_);
v___x_2140_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_2126_, v___x_2139_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v_a_2141_; 
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_a_2141_);
lean_dec_ref_known(v___x_2140_, 1);
if (lean_obj_tag(v_a_2141_) == 1)
{
lean_object* v_val_2142_; lean_object* v_fst_2143_; lean_object* v_snd_2144_; lean_object* v___x_2145_; 
lean_dec_ref(v_e_2126_);
v_val_2142_ = lean_ctor_get(v_a_2141_, 0);
lean_inc(v_val_2142_);
lean_dec_ref_known(v_a_2141_, 1);
v_fst_2143_ = lean_ctor_get(v_val_2142_, 0);
lean_inc(v_fst_2143_);
v_snd_2144_ = lean_ctor_get(v_val_2142_, 1);
lean_inc(v_snd_2144_);
lean_dec(v_val_2142_);
v___x_2145_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_snd_2144_, v_p_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v_a_2146_; 
v_a_2146_ = lean_ctor_get(v___x_2145_, 0);
lean_inc(v_a_2146_);
lean_dec_ref_known(v___x_2145_, 1);
v_e_2126_ = v_fst_2143_;
v_p_2127_ = v_a_2146_;
goto _start;
}
else
{
lean_dec(v_fst_2143_);
return v___x_2145_;
}
}
else
{
lean_object* v___x_2148_; 
lean_dec(v_a_2141_);
v___x_2148_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_e_2126_, v_p_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_);
return v___x_2148_;
}
}
else
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2156_; 
lean_dec_ref(v_p_2127_);
lean_dec_ref(v_e_2126_);
v_a_2149_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2151_ = v___x_2140_;
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2140_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2154_; 
if (v_isShared_2152_ == 0)
{
v___x_2154_ = v___x_2151_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_a_2149_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go___boxed(lean_object* v_e_2157_, lean_object* v_p_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_){
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go(v_e_2157_, v_p_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_);
lean_dec(v_a_2168_);
lean_dec_ref(v_a_2167_);
lean_dec(v_a_2166_);
lean_dec_ref(v_a_2165_);
lean_dec(v_a_2164_);
lean_dec_ref(v_a_2163_);
lean_dec(v_a_2162_);
lean_dec_ref(v_a_2161_);
lean_dec(v_a_2160_);
lean_dec(v_a_2159_);
return v_res_2170_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0(void){
_start:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2171_ = lean_unsigned_to_nat(0u);
v___x_2172_ = lean_nat_to_int(v___x_2171_);
return v___x_2172_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1(void){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2173_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0);
v___x_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2173_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly(lean_object* v_e_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_){
_start:
{
uint8_t v___x_2187_; lean_object* v___x_2188_; 
v___x_2187_ = 1;
lean_inc_ref(v_e_2175_);
v___x_2188_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_2175_, v___x_2187_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v_a_2189_; 
v_a_2189_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_a_2189_);
lean_dec_ref_known(v___x_2188_, 1);
if (lean_obj_tag(v_a_2189_) == 1)
{
lean_object* v_val_2190_; lean_object* v_fst_2191_; lean_object* v_snd_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
lean_dec_ref(v_e_2175_);
v_val_2190_ = lean_ctor_get(v_a_2189_, 0);
lean_inc(v_val_2190_);
lean_dec_ref_known(v_a_2189_, 1);
v_fst_2191_ = lean_ctor_get(v_val_2190_, 0);
lean_inc(v_fst_2191_);
v_snd_2192_ = lean_ctor_get(v_val_2190_, 1);
lean_inc(v_snd_2192_);
lean_dec(v_val_2190_);
v___x_2193_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1);
v___x_2194_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_snd_2192_, v___x_2193_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; lean_object* v___x_2196_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_a_2195_);
lean_dec_ref_known(v___x_2194_, 1);
v___x_2196_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go(v_fst_2191_, v_a_2195_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_);
return v___x_2196_;
}
else
{
lean_dec(v_fst_2191_);
return v___x_2194_;
}
}
else
{
lean_object* v___x_2197_; lean_object* v___x_2198_; 
lean_dec(v_a_2189_);
v___x_2197_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1);
v___x_2198_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_e_2175_, v___x_2197_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_);
return v___x_2198_;
}
}
else
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2206_; 
lean_dec_ref(v_e_2175_);
v_a_2199_ = lean_ctor_get(v___x_2188_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2201_ = v___x_2188_;
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2188_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2204_; 
if (v_isShared_2202_ == 0)
{
v___x_2204_ = v___x_2201_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_a_2199_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly___boxed(lean_object* v_e_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_){
_start:
{
lean_object* v_res_2219_; 
v_res_2219_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_e_2207_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_);
lean_dec(v_a_2217_);
lean_dec_ref(v_a_2216_);
lean_dec(v_a_2215_);
lean_dec_ref(v_a_2214_);
lean_dec(v_a_2213_);
lean_dec_ref(v_a_2212_);
lean_dec(v_a_2211_);
lean_dec_ref(v_a_2210_);
lean_dec(v_a_2209_);
lean_dec(v_a_2208_);
return v_res_2219_;
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
