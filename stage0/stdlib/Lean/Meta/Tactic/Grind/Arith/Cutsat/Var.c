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
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isIntValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHDivInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHModInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHPowInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isNatValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_cutsat_mk_var(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHSubInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstNegInt___redArg(lean_object*, lean_object*);
uint8_t l_Int_Internal_Linear_Poly_isZero(lean_object*);
lean_object* lean_cutsat_propagate_nonlinear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNonlinearTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_cutsat_reactivate_var(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reactivateVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertVarFacts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertVarFacts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_x3f_monomial_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_x3f_monomial_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNonlinearTerm___boxed(lean_object* v_y_14_, lean_object* v_x_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_00___x40___internal___hyg_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = lean_cutsat_propagate_nonlinear(v_y_14_, v_x_15_, v_a_16_, v_a_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_reactivateVar___boxed(lean_object* v_x_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_00___x40___internal___hyg_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = lean_grind_cutsat_reactivate_var(v_x_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm(lean_object* v_e_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_73_, v_a_75_);
if (lean_obj_tag(v___x_83_) == 0)
{
lean_object* v_a_84_; lean_object* v___x_85_; uint8_t v___x_86_; 
v_a_84_ = lean_ctor_get(v___x_83_, 0);
lean_inc(v_a_84_);
lean_dec_ref_known(v___x_83_, 1);
v___x_85_ = l_Lean_Expr_cleanupAnnotations(v_a_84_);
lean_dec(v_a_84_);
v___x_86_ = l_Lean_Expr_isApp(v___x_85_);
if (v___x_86_ == 0)
{
lean_dec_ref(v___x_85_);
goto v___jp_79_;
}
else
{
lean_object* v___x_87_; uint8_t v___x_88_; 
v___x_87_ = l_Lean_Expr_appFnCleanup___redArg(v___x_85_);
v___x_88_ = l_Lean_Expr_isApp(v___x_87_);
if (v___x_88_ == 0)
{
lean_dec_ref(v___x_87_);
lean_dec_ref(v___x_85_);
goto v___jp_79_;
}
else
{
lean_object* v___x_89_; uint8_t v___x_90_; 
v___x_89_ = l_Lean_Expr_appFnCleanup___redArg(v___x_87_);
v___x_90_ = l_Lean_Expr_isApp(v___x_89_);
if (v___x_90_ == 0)
{
lean_dec_ref(v___x_89_);
lean_dec_ref(v___x_87_);
lean_dec_ref(v___x_85_);
goto v___jp_79_;
}
else
{
lean_object* v___x_91_; uint8_t v___x_92_; 
v___x_91_ = l_Lean_Expr_appFnCleanup___redArg(v___x_89_);
v___x_92_ = l_Lean_Expr_isApp(v___x_91_);
if (v___x_92_ == 0)
{
lean_dec_ref(v___x_91_);
lean_dec_ref(v___x_89_);
lean_dec_ref(v___x_87_);
lean_dec_ref(v___x_85_);
goto v___jp_79_;
}
else
{
lean_object* v___x_93_; uint8_t v___x_94_; 
v___x_93_ = l_Lean_Expr_appFnCleanup___redArg(v___x_91_);
lean_dec_ref(v___x_91_);
v___x_94_ = l_Lean_Expr_isApp(v___x_93_);
if (v___x_94_ == 0)
{
lean_dec_ref(v___x_93_);
lean_dec_ref(v___x_89_);
lean_dec_ref(v___x_87_);
lean_dec_ref(v___x_85_);
goto v___jp_79_;
}
else
{
lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_95_ = l_Lean_Expr_appFnCleanup___redArg(v___x_93_);
lean_dec_ref(v___x_93_);
v___x_96_ = l_Lean_Expr_isApp(v___x_95_);
if (v___x_96_ == 0)
{
lean_dec_ref(v___x_95_);
lean_dec_ref(v___x_89_);
lean_dec_ref(v___x_87_);
lean_dec_ref(v___x_85_);
goto v___jp_79_;
}
else
{
lean_object* v_arg_97_; lean_object* v_arg_98_; lean_object* v___x_99_; lean_object* v___x_100_; uint8_t v___x_101_; 
v_arg_97_ = lean_ctor_get(v___x_85_, 1);
lean_inc_ref(v_arg_97_);
lean_dec_ref(v___x_85_);
v_arg_98_ = lean_ctor_get(v___x_89_, 1);
lean_inc_ref(v_arg_98_);
lean_dec_ref(v___x_89_);
v___x_99_ = l_Lean_Expr_appFnCleanup___redArg(v___x_95_);
lean_dec_ref(v___x_95_);
v___x_100_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__2));
v___x_101_ = l_Lean_Expr_isConstOf(v___x_99_, v___x_100_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; uint8_t v___x_103_; 
lean_dec_ref(v___x_87_);
v___x_102_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__5));
v___x_103_ = l_Lean_Expr_isConstOf(v___x_99_, v___x_102_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_104_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__8));
v___x_105_ = l_Lean_Expr_isConstOf(v___x_99_, v___x_104_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; uint8_t v___x_107_; 
lean_dec_ref(v_arg_97_);
v___x_106_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11));
v___x_107_ = l_Lean_Expr_isConstOf(v___x_99_, v___x_106_);
lean_dec_ref(v___x_99_);
if (v___x_107_ == 0)
{
lean_dec_ref(v_arg_98_);
goto v___jp_79_;
}
else
{
lean_object* v___x_108_; 
v___x_108_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_98_, v_a_75_);
return v___x_108_;
}
}
else
{
lean_object* v___x_109_; 
lean_dec_ref(v___x_99_);
v___x_109_ = l_Lean_Meta_isIntValue(v_arg_97_, v_a_74_, v_a_75_, v_a_76_, v_a_77_);
if (lean_obj_tag(v___x_109_) == 0)
{
lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_120_; 
v_a_110_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_120_ == 0)
{
v___x_112_ = v___x_109_;
v_isShared_113_ = v_isSharedCheck_120_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v___x_109_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_120_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
uint8_t v___x_114_; 
v___x_114_ = lean_unbox(v_a_110_);
lean_dec(v_a_110_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; 
lean_del_object(v___x_112_);
v___x_115_ = l_Lean_Meta_Structural_isInstHDivInt___redArg(v_arg_98_, v_a_75_);
return v___x_115_;
}
else
{
lean_object* v___x_116_; lean_object* v___x_118_; 
lean_dec_ref(v_arg_98_);
v___x_116_ = lean_box(v___x_103_);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 0, v___x_116_);
v___x_118_ = v___x_112_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v___x_116_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
}
else
{
lean_dec_ref(v_arg_98_);
return v___x_109_;
}
}
}
else
{
lean_object* v___x_121_; 
lean_dec_ref(v___x_99_);
v___x_121_ = l_Lean_Meta_isIntValue(v_arg_97_, v_a_74_, v_a_75_, v_a_76_, v_a_77_);
if (lean_obj_tag(v___x_121_) == 0)
{
lean_object* v_a_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_132_; 
v_a_122_ = lean_ctor_get(v___x_121_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_121_);
if (v_isSharedCheck_132_ == 0)
{
v___x_124_ = v___x_121_;
v_isShared_125_ = v_isSharedCheck_132_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_a_122_);
lean_dec(v___x_121_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_132_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
uint8_t v___x_126_; 
v___x_126_ = lean_unbox(v_a_122_);
lean_dec(v_a_122_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; 
lean_del_object(v___x_124_);
v___x_127_ = l_Lean_Meta_Structural_isInstHModInt___redArg(v_arg_98_, v_a_75_);
return v___x_127_;
}
else
{
lean_object* v___x_128_; lean_object* v___x_130_; 
lean_dec_ref(v_arg_98_);
v___x_128_ = lean_box(v___x_101_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 0, v___x_128_);
v___x_130_ = v___x_124_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v___x_128_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
}
else
{
lean_dec_ref(v_arg_98_);
return v___x_121_;
}
}
}
else
{
lean_object* v_arg_133_; lean_object* v___x_134_; 
lean_dec_ref(v___x_99_);
v_arg_133_ = lean_ctor_get(v___x_87_, 1);
lean_inc_ref(v_arg_133_);
lean_dec_ref(v___x_87_);
v___x_134_ = l_Lean_Meta_Structural_isInstHPowInt___redArg(v_arg_98_, v_a_75_);
if (lean_obj_tag(v___x_134_) == 0)
{
lean_object* v_a_135_; uint8_t v___x_136_; 
v_a_135_ = lean_ctor_get(v___x_134_, 0);
v___x_136_ = lean_unbox(v_a_135_);
if (v___x_136_ == 0)
{
lean_dec_ref(v_arg_133_);
lean_dec_ref(v_arg_97_);
return v___x_134_;
}
else
{
lean_object* v___x_137_; 
lean_inc(v_a_135_);
lean_dec_ref_known(v___x_134_, 1);
v___x_137_ = l_Lean_Meta_isIntValue(v_arg_133_, v_a_74_, v_a_75_, v_a_76_, v_a_77_);
if (lean_obj_tag(v___x_137_) == 0)
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_161_; 
v_a_138_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_161_ == 0)
{
v___x_140_ = v___x_137_;
v_isShared_141_ = v_isSharedCheck_161_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_137_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_161_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
uint8_t v___x_142_; 
v___x_142_ = lean_unbox(v_a_138_);
lean_dec(v_a_138_);
if (v___x_142_ == 0)
{
lean_object* v___x_144_; 
lean_dec_ref(v_arg_97_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 0, v_a_135_);
v___x_144_ = v___x_140_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_a_135_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
else
{
uint8_t v___x_146_; lean_object* v___x_147_; 
lean_del_object(v___x_140_);
v___x_146_ = 0;
v___x_147_ = l_Lean_Meta_isIntValue(v_arg_97_, v_a_74_, v_a_75_, v_a_76_, v_a_77_);
if (lean_obj_tag(v___x_147_) == 0)
{
lean_object* v_a_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_160_; 
v_a_148_ = lean_ctor_get(v___x_147_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v___x_147_);
if (v_isSharedCheck_160_ == 0)
{
v___x_150_ = v___x_147_;
v_isShared_151_ = v_isSharedCheck_160_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_a_148_);
lean_dec(v___x_147_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_160_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
uint8_t v___x_152_; 
v___x_152_ = lean_unbox(v_a_148_);
lean_dec(v_a_148_);
if (v___x_152_ == 0)
{
lean_object* v___x_154_; 
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 0, v_a_135_);
v___x_154_ = v___x_150_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_a_135_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
else
{
lean_object* v___x_156_; lean_object* v___x_158_; 
lean_dec(v_a_135_);
v___x_156_ = lean_box(v___x_146_);
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 0, v___x_156_);
v___x_158_ = v___x_150_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_156_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
}
else
{
lean_dec(v_a_135_);
return v___x_147_;
}
}
}
}
else
{
lean_dec(v_a_135_);
lean_dec_ref(v_arg_97_);
return v___x_137_;
}
}
}
else
{
lean_dec_ref(v_arg_133_);
lean_dec_ref(v_arg_97_);
return v___x_134_;
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
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_169_; 
v_a_162_ = lean_ctor_get(v___x_83_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_169_ == 0)
{
v___x_164_ = v___x_83_;
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_83_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_167_; 
if (v_isShared_165_ == 0)
{
v___x_167_ = v___x_164_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_a_162_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
v___jp_79_:
{
uint8_t v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_80_ = 0;
v___x_81_ = lean_box(v___x_80_);
v___x_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
return v___x_82_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___boxed(lean_object* v_e_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm(v_e_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_);
lean_dec(v_a_174_);
lean_dec_ref(v_a_173_);
lean_dec(v_a_172_);
lean_dec_ref(v_a_171_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_x_177_, lean_object* v_x_178_, lean_object* v_x_179_, lean_object* v_x_180_){
_start:
{
lean_object* v_ks_181_; lean_object* v_vs_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_206_; 
v_ks_181_ = lean_ctor_get(v_x_177_, 0);
v_vs_182_ = lean_ctor_get(v_x_177_, 1);
v_isSharedCheck_206_ = !lean_is_exclusive(v_x_177_);
if (v_isSharedCheck_206_ == 0)
{
v___x_184_ = v_x_177_;
v_isShared_185_ = v_isSharedCheck_206_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_vs_182_);
lean_inc(v_ks_181_);
lean_dec(v_x_177_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_206_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_186_ = lean_array_get_size(v_ks_181_);
v___x_187_ = lean_nat_dec_lt(v_x_178_, v___x_186_);
if (v___x_187_ == 0)
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_191_; 
lean_dec(v_x_178_);
v___x_188_ = lean_array_push(v_ks_181_, v_x_179_);
v___x_189_ = lean_array_push(v_vs_182_, v_x_180_);
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 1, v___x_189_);
lean_ctor_set(v___x_184_, 0, v___x_188_);
v___x_191_ = v___x_184_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_188_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v___x_189_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
else
{
lean_object* v_k_x27_193_; uint8_t v___x_194_; 
v_k_x27_193_ = lean_array_fget_borrowed(v_ks_181_, v_x_178_);
v___x_194_ = lean_nat_dec_eq(v_x_179_, v_k_x27_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_196_; 
if (v_isShared_185_ == 0)
{
v___x_196_ = v___x_184_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_ks_181_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v_vs_182_);
v___x_196_ = v_reuseFailAlloc_200_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = lean_unsigned_to_nat(1u);
v___x_198_ = lean_nat_add(v_x_178_, v___x_197_);
lean_dec(v_x_178_);
v_x_177_ = v___x_196_;
v_x_178_ = v___x_198_;
goto _start;
}
}
else
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_204_; 
v___x_201_ = lean_array_fset(v_ks_181_, v_x_178_, v_x_179_);
v___x_202_ = lean_array_fset(v_vs_182_, v_x_178_, v_x_180_);
lean_dec(v_x_178_);
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 1, v___x_202_);
lean_ctor_set(v___x_184_, 0, v___x_201_);
v___x_204_ = v___x_184_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_201_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v___x_202_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1___redArg(lean_object* v_n_207_, lean_object* v_k_208_, lean_object* v_v_209_){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = lean_unsigned_to_nat(0u);
v___x_211_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__4___redArg(v_n_207_, v___x_210_, v_k_208_, v_v_209_);
return v___x_211_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(lean_object* v_x_213_, size_t v_x_214_, size_t v_x_215_, lean_object* v_x_216_, lean_object* v_x_217_){
_start:
{
if (lean_obj_tag(v_x_213_) == 0)
{
lean_object* v_es_218_; size_t v___x_219_; size_t v___x_220_; lean_object* v_j_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
v_es_218_ = lean_ctor_get(v_x_213_, 0);
v___x_219_ = ((size_t)31ULL);
v___x_220_ = lean_usize_land(v_x_214_, v___x_219_);
v_j_221_ = lean_usize_to_nat(v___x_220_);
v___x_222_ = lean_array_get_size(v_es_218_);
v___x_223_ = lean_nat_dec_lt(v_j_221_, v___x_222_);
if (v___x_223_ == 0)
{
lean_dec(v_j_221_);
lean_dec(v_x_217_);
lean_dec(v_x_216_);
return v_x_213_;
}
else
{
lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_262_; 
lean_inc_ref(v_es_218_);
v_isSharedCheck_262_ = !lean_is_exclusive(v_x_213_);
if (v_isSharedCheck_262_ == 0)
{
lean_object* v_unused_263_; 
v_unused_263_ = lean_ctor_get(v_x_213_, 0);
lean_dec(v_unused_263_);
v___x_225_ = v_x_213_;
v_isShared_226_ = v_isSharedCheck_262_;
goto v_resetjp_224_;
}
else
{
lean_dec(v_x_213_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_262_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v_v_227_; lean_object* v___x_228_; lean_object* v_xs_x27_229_; lean_object* v___y_231_; 
v_v_227_ = lean_array_fget(v_es_218_, v_j_221_);
v___x_228_ = lean_box(0);
v_xs_x27_229_ = lean_array_fset(v_es_218_, v_j_221_, v___x_228_);
switch(lean_obj_tag(v_v_227_))
{
case 0:
{
lean_object* v_key_236_; lean_object* v_val_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_247_; 
v_key_236_ = lean_ctor_get(v_v_227_, 0);
v_val_237_ = lean_ctor_get(v_v_227_, 1);
v_isSharedCheck_247_ = !lean_is_exclusive(v_v_227_);
if (v_isSharedCheck_247_ == 0)
{
v___x_239_ = v_v_227_;
v_isShared_240_ = v_isSharedCheck_247_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_val_237_);
lean_inc(v_key_236_);
lean_dec(v_v_227_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_247_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
uint8_t v___x_241_; 
v___x_241_ = lean_nat_dec_eq(v_x_216_, v_key_236_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; lean_object* v___x_243_; 
lean_del_object(v___x_239_);
v___x_242_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_236_, v_val_237_, v_x_216_, v_x_217_);
v___x_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
v___y_231_ = v___x_243_;
goto v___jp_230_;
}
else
{
lean_object* v___x_245_; 
lean_dec(v_val_237_);
lean_dec(v_key_236_);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 1, v_x_217_);
lean_ctor_set(v___x_239_, 0, v_x_216_);
v___x_245_ = v___x_239_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_x_216_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v_x_217_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
v___y_231_ = v___x_245_;
goto v___jp_230_;
}
}
}
}
case 1:
{
lean_object* v_node_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_260_; 
v_node_248_ = lean_ctor_get(v_v_227_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v_v_227_);
if (v_isSharedCheck_260_ == 0)
{
v___x_250_ = v_v_227_;
v_isShared_251_ = v_isSharedCheck_260_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_node_248_);
lean_dec(v_v_227_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_260_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
size_t v___x_252_; size_t v___x_253_; size_t v___x_254_; size_t v___x_255_; lean_object* v___x_256_; lean_object* v___x_258_; 
v___x_252_ = ((size_t)5ULL);
v___x_253_ = lean_usize_shift_right(v_x_214_, v___x_252_);
v___x_254_ = ((size_t)1ULL);
v___x_255_ = lean_usize_add(v_x_215_, v___x_254_);
v___x_256_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_node_248_, v___x_253_, v___x_255_, v_x_216_, v_x_217_);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 0, v___x_256_);
v___x_258_ = v___x_250_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_256_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
v___y_231_ = v___x_258_;
goto v___jp_230_;
}
}
}
default: 
{
lean_object* v___x_261_; 
v___x_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_261_, 0, v_x_216_);
lean_ctor_set(v___x_261_, 1, v_x_217_);
v___y_231_ = v___x_261_;
goto v___jp_230_;
}
}
v___jp_230_:
{
lean_object* v___x_232_; lean_object* v___x_234_; 
v___x_232_ = lean_array_fset(v_xs_x27_229_, v_j_221_, v___y_231_);
lean_dec(v_j_221_);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 0, v___x_232_);
v___x_234_ = v___x_225_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_232_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
}
}
else
{
lean_object* v_ks_264_; lean_object* v_vs_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_283_; 
v_ks_264_ = lean_ctor_get(v_x_213_, 0);
v_vs_265_ = lean_ctor_get(v_x_213_, 1);
v_isSharedCheck_283_ = !lean_is_exclusive(v_x_213_);
if (v_isSharedCheck_283_ == 0)
{
v___x_267_ = v_x_213_;
v_isShared_268_ = v_isSharedCheck_283_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_vs_265_);
lean_inc(v_ks_264_);
lean_dec(v_x_213_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_283_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_270_; 
if (v_isShared_268_ == 0)
{
v___x_270_ = v___x_267_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_ks_264_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v_vs_265_);
v___x_270_ = v_reuseFailAlloc_282_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
lean_object* v_newNode_271_; size_t v___x_272_; uint8_t v___x_273_; 
v_newNode_271_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1___redArg(v___x_270_, v_x_216_, v_x_217_);
v___x_272_ = ((size_t)7ULL);
v___x_273_ = lean_usize_dec_le(v___x_272_, v_x_215_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; 
v___x_274_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_271_);
v___x_275_ = lean_unsigned_to_nat(4u);
v___x_276_ = lean_nat_dec_lt(v___x_274_, v___x_275_);
lean_dec(v___x_274_);
if (v___x_276_ == 0)
{
lean_object* v_ks_277_; lean_object* v_vs_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v_ks_277_ = lean_ctor_get(v_newNode_271_, 0);
lean_inc_ref(v_ks_277_);
v_vs_278_ = lean_ctor_get(v_newNode_271_, 1);
lean_inc_ref(v_vs_278_);
lean_dec_ref(v_newNode_271_);
v___x_279_ = lean_unsigned_to_nat(0u);
v___x_280_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0);
v___x_281_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg(v_x_215_, v_ks_277_, v_vs_278_, v___x_279_, v___x_280_);
lean_dec_ref(v_vs_278_);
lean_dec_ref(v_ks_277_);
return v___x_281_;
}
else
{
return v_newNode_271_;
}
}
else
{
return v_newNode_271_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg(size_t v_depth_284_, lean_object* v_keys_285_, lean_object* v_vals_286_, lean_object* v_i_287_, lean_object* v_entries_288_){
_start:
{
lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_289_ = lean_array_get_size(v_keys_285_);
v___x_290_ = lean_nat_dec_lt(v_i_287_, v___x_289_);
if (v___x_290_ == 0)
{
lean_dec(v_i_287_);
return v_entries_288_;
}
else
{
lean_object* v_k_291_; lean_object* v_v_292_; uint64_t v___x_293_; size_t v_h_294_; size_t v___x_295_; lean_object* v___x_296_; size_t v___x_297_; size_t v___x_298_; size_t v___x_299_; size_t v_h_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v_k_291_ = lean_array_fget_borrowed(v_keys_285_, v_i_287_);
v_v_292_ = lean_array_fget_borrowed(v_vals_286_, v_i_287_);
v___x_293_ = lean_uint64_of_nat(v_k_291_);
v_h_294_ = lean_uint64_to_usize(v___x_293_);
v___x_295_ = ((size_t)5ULL);
v___x_296_ = lean_unsigned_to_nat(1u);
v___x_297_ = ((size_t)1ULL);
v___x_298_ = lean_usize_sub(v_depth_284_, v___x_297_);
v___x_299_ = lean_usize_mul(v___x_295_, v___x_298_);
v_h_300_ = lean_usize_shift_right(v_h_294_, v___x_299_);
v___x_301_ = lean_nat_add(v_i_287_, v___x_296_);
lean_dec(v_i_287_);
lean_inc(v_v_292_);
lean_inc(v_k_291_);
v___x_302_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_entries_288_, v_h_300_, v_depth_284_, v_k_291_, v_v_292_);
v_i_287_ = v___x_301_;
v_entries_288_ = v___x_302_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_304_, lean_object* v_keys_305_, lean_object* v_vals_306_, lean_object* v_i_307_, lean_object* v_entries_308_){
_start:
{
size_t v_depth_boxed_309_; lean_object* v_res_310_; 
v_depth_boxed_309_ = lean_unbox_usize(v_depth_304_);
lean_dec(v_depth_304_);
v_res_310_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg(v_depth_boxed_309_, v_keys_305_, v_vals_306_, v_i_307_, v_entries_308_);
lean_dec_ref(v_vals_306_);
lean_dec_ref(v_keys_305_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___boxed(lean_object* v_x_311_, lean_object* v_x_312_, lean_object* v_x_313_, lean_object* v_x_314_, lean_object* v_x_315_){
_start:
{
size_t v_x_8145__boxed_316_; size_t v_x_8146__boxed_317_; lean_object* v_res_318_; 
v_x_8145__boxed_316_ = lean_unbox_usize(v_x_312_);
lean_dec(v_x_312_);
v_x_8146__boxed_317_ = lean_unbox_usize(v_x_313_);
lean_dec(v_x_313_);
v_res_318_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_x_311_, v_x_8145__boxed_316_, v_x_8146__boxed_317_, v_x_314_, v_x_315_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0___redArg(lean_object* v_x_319_, lean_object* v_x_320_, lean_object* v_x_321_){
_start:
{
uint64_t v___x_322_; size_t v___x_323_; size_t v___x_324_; lean_object* v___x_325_; 
v___x_322_ = lean_uint64_of_nat(v_x_320_);
v___x_323_ = lean_uint64_to_usize(v___x_322_);
v___x_324_ = ((size_t)1ULL);
v___x_325_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_x_319_, v___x_323_, v___x_324_, v_x_320_, v_x_321_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___lam__0(lean_object* v_x_326_, lean_object* v___y_327_, lean_object* v_a_328_, lean_object* v_s_329_){
_start:
{
lean_object* v_vars_330_; lean_object* v_varMap_331_; lean_object* v_varsHistory_332_; lean_object* v_natToIntMap_333_; lean_object* v_natDef_334_; lean_object* v_dvds_335_; lean_object* v_lowers_336_; lean_object* v_uppers_337_; lean_object* v_diseqs_338_; lean_object* v_elimEqs_339_; lean_object* v_active_340_; lean_object* v_elimStack_341_; lean_object* v_occurs_342_; lean_object* v_assignment_343_; lean_object* v_nextCnstrId_344_; uint8_t v_caseSplits_345_; lean_object* v_steps_346_; lean_object* v_penalties_347_; lean_object* v_numReorderRequests_348_; lean_object* v_conflict_x3f_349_; lean_object* v_diseqSplits_350_; lean_object* v_divMod_351_; uint8_t v_usedCommRing_352_; lean_object* v_nonlinearOccs_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_362_; 
v_vars_330_ = lean_ctor_get(v_s_329_, 0);
v_varMap_331_ = lean_ctor_get(v_s_329_, 1);
v_varsHistory_332_ = lean_ctor_get(v_s_329_, 2);
v_natToIntMap_333_ = lean_ctor_get(v_s_329_, 3);
v_natDef_334_ = lean_ctor_get(v_s_329_, 4);
v_dvds_335_ = lean_ctor_get(v_s_329_, 5);
v_lowers_336_ = lean_ctor_get(v_s_329_, 6);
v_uppers_337_ = lean_ctor_get(v_s_329_, 7);
v_diseqs_338_ = lean_ctor_get(v_s_329_, 8);
v_elimEqs_339_ = lean_ctor_get(v_s_329_, 9);
v_active_340_ = lean_ctor_get(v_s_329_, 10);
v_elimStack_341_ = lean_ctor_get(v_s_329_, 11);
v_occurs_342_ = lean_ctor_get(v_s_329_, 12);
v_assignment_343_ = lean_ctor_get(v_s_329_, 13);
v_nextCnstrId_344_ = lean_ctor_get(v_s_329_, 14);
v_caseSplits_345_ = lean_ctor_get_uint8(v_s_329_, sizeof(void*)*22);
v_steps_346_ = lean_ctor_get(v_s_329_, 15);
v_penalties_347_ = lean_ctor_get(v_s_329_, 16);
v_numReorderRequests_348_ = lean_ctor_get(v_s_329_, 17);
v_conflict_x3f_349_ = lean_ctor_get(v_s_329_, 18);
v_diseqSplits_350_ = lean_ctor_get(v_s_329_, 19);
v_divMod_351_ = lean_ctor_get(v_s_329_, 20);
v_usedCommRing_352_ = lean_ctor_get_uint8(v_s_329_, sizeof(void*)*22 + 1);
v_nonlinearOccs_353_ = lean_ctor_get(v_s_329_, 21);
v_isSharedCheck_362_ = !lean_is_exclusive(v_s_329_);
if (v_isSharedCheck_362_ == 0)
{
v___x_355_ = v_s_329_;
v_isShared_356_ = v_isSharedCheck_362_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_nonlinearOccs_353_);
lean_inc(v_divMod_351_);
lean_inc(v_diseqSplits_350_);
lean_inc(v_conflict_x3f_349_);
lean_inc(v_numReorderRequests_348_);
lean_inc(v_penalties_347_);
lean_inc(v_steps_346_);
lean_inc(v_nextCnstrId_344_);
lean_inc(v_assignment_343_);
lean_inc(v_occurs_342_);
lean_inc(v_elimStack_341_);
lean_inc(v_active_340_);
lean_inc(v_elimEqs_339_);
lean_inc(v_diseqs_338_);
lean_inc(v_uppers_337_);
lean_inc(v_lowers_336_);
lean_inc(v_dvds_335_);
lean_inc(v_natDef_334_);
lean_inc(v_natToIntMap_333_);
lean_inc(v_varsHistory_332_);
lean_inc(v_varMap_331_);
lean_inc(v_vars_330_);
lean_dec(v_s_329_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_362_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_360_; 
v___x_357_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_357_, 0, v_x_326_);
lean_ctor_set(v___x_357_, 1, v___y_327_);
v___x_358_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0___redArg(v_nonlinearOccs_353_, v_a_328_, v___x_357_);
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 21, v___x_358_);
v___x_360_ = v___x_355_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 22, 2);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_vars_330_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v_varMap_331_);
lean_ctor_set(v_reuseFailAlloc_361_, 2, v_varsHistory_332_);
lean_ctor_set(v_reuseFailAlloc_361_, 3, v_natToIntMap_333_);
lean_ctor_set(v_reuseFailAlloc_361_, 4, v_natDef_334_);
lean_ctor_set(v_reuseFailAlloc_361_, 5, v_dvds_335_);
lean_ctor_set(v_reuseFailAlloc_361_, 6, v_lowers_336_);
lean_ctor_set(v_reuseFailAlloc_361_, 7, v_uppers_337_);
lean_ctor_set(v_reuseFailAlloc_361_, 8, v_diseqs_338_);
lean_ctor_set(v_reuseFailAlloc_361_, 9, v_elimEqs_339_);
lean_ctor_set(v_reuseFailAlloc_361_, 10, v_active_340_);
lean_ctor_set(v_reuseFailAlloc_361_, 11, v_elimStack_341_);
lean_ctor_set(v_reuseFailAlloc_361_, 12, v_occurs_342_);
lean_ctor_set(v_reuseFailAlloc_361_, 13, v_assignment_343_);
lean_ctor_set(v_reuseFailAlloc_361_, 14, v_nextCnstrId_344_);
lean_ctor_set(v_reuseFailAlloc_361_, 15, v_steps_346_);
lean_ctor_set(v_reuseFailAlloc_361_, 16, v_penalties_347_);
lean_ctor_set(v_reuseFailAlloc_361_, 17, v_numReorderRequests_348_);
lean_ctor_set(v_reuseFailAlloc_361_, 18, v_conflict_x3f_349_);
lean_ctor_set(v_reuseFailAlloc_361_, 19, v_diseqSplits_350_);
lean_ctor_set(v_reuseFailAlloc_361_, 20, v_divMod_351_);
lean_ctor_set(v_reuseFailAlloc_361_, 21, v___x_358_);
lean_ctor_set_uint8(v_reuseFailAlloc_361_, sizeof(void*)*22, v_caseSplits_345_);
lean_ctor_set_uint8(v_reuseFailAlloc_361_, sizeof(void*)*22 + 1, v_usedCommRing_352_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1(lean_object* v_a_363_, lean_object* v_x_364_){
_start:
{
if (lean_obj_tag(v_x_364_) == 0)
{
uint8_t v___x_365_; 
v___x_365_ = 0;
return v___x_365_;
}
else
{
lean_object* v_head_366_; lean_object* v_tail_367_; uint8_t v___x_368_; 
v_head_366_ = lean_ctor_get(v_x_364_, 0);
v_tail_367_ = lean_ctor_get(v_x_364_, 1);
v___x_368_ = lean_nat_dec_eq(v_a_363_, v_head_366_);
if (v___x_368_ == 0)
{
v_x_364_ = v_tail_367_;
goto _start;
}
else
{
return v___x_368_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___boxed(lean_object* v_a_370_, lean_object* v_x_371_){
_start:
{
uint8_t v_res_372_; lean_object* v_r_373_; 
v_res_372_ = l_List_elem___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1(v_a_370_, v_x_371_);
lean_dec(v_x_371_);
lean_dec(v_a_370_);
v_r_373_ = lean_box(v_res_372_);
return v_r_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6___redArg(lean_object* v_keys_374_, lean_object* v_vals_375_, lean_object* v_i_376_, lean_object* v_k_377_){
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_keys_388_, lean_object* v_vals_389_, lean_object* v_i_390_, lean_object* v_k_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6___redArg(v_keys_388_, v_vals_389_, v_i_390_, v_k_391_);
lean_dec(v_k_391_);
lean_dec_ref(v_vals_389_);
lean_dec_ref(v_keys_388_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___redArg(lean_object* v_x_393_, size_t v_x_394_, lean_object* v_x_395_){
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
v___x_415_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6___redArg(v_ks_412_, v_vs_413_, v___x_414_, v_x_395_);
return v___x_415_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___redArg___boxed(lean_object* v_x_416_, lean_object* v_x_417_, lean_object* v_x_418_){
_start:
{
size_t v_x_8364__boxed_419_; lean_object* v_res_420_; 
v_x_8364__boxed_419_ = lean_unbox_usize(v_x_417_);
lean_dec(v_x_417_);
v_res_420_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___redArg(v_x_416_, v_x_8364__boxed_419_, v_x_418_);
lean_dec(v_x_418_);
lean_dec_ref(v_x_416_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2___redArg(lean_object* v_x_421_, lean_object* v_x_422_){
_start:
{
uint64_t v___x_423_; size_t v___x_424_; lean_object* v___x_425_; 
v___x_423_ = lean_uint64_of_nat(v_x_422_);
v___x_424_ = lean_uint64_to_usize(v___x_423_);
v___x_425_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___redArg(v_x_421_, v___x_424_, v_x_422_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2___redArg___boxed(lean_object* v_x_426_, lean_object* v_x_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2___redArg(v_x_426_, v_x_427_);
lean_dec(v_x_427_);
lean_dec_ref(v_x_426_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(lean_object* v_arg_429_, lean_object* v_x_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = lean_box(0);
lean_inc(v_a_440_);
lean_inc_ref(v_a_439_);
lean_inc(v_a_438_);
lean_inc_ref(v_a_437_);
lean_inc(v_a_436_);
lean_inc_ref(v_a_435_);
lean_inc(v_a_434_);
lean_inc_ref(v_a_433_);
lean_inc(v_a_432_);
lean_inc(v_a_431_);
v___x_443_ = lean_grind_cutsat_mk_var(v_arg_429_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_512_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_512_ == 0)
{
v___x_446_ = v___x_443_;
v_isShared_447_ = v_isSharedCheck_512_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_443_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_512_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___y_449_; lean_object* v___y_450_; lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v___x_476_; 
v___x_476_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_431_, v_a_439_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v_a_477_; lean_object* v___y_479_; lean_object* v_elimEqs_499_; lean_object* v_size_500_; uint8_t v___x_501_; 
v_a_477_ = lean_ctor_get(v___x_476_, 0);
lean_inc(v_a_477_);
lean_dec_ref_known(v___x_476_, 1);
v_elimEqs_499_ = lean_ctor_get(v_a_477_, 9);
lean_inc_ref(v_elimEqs_499_);
lean_dec(v_a_477_);
v_size_500_ = lean_ctor_get(v_elimEqs_499_, 2);
v___x_501_ = lean_nat_dec_lt(v_a_444_, v_size_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; 
lean_dec_ref(v_elimEqs_499_);
v___x_502_ = l_outOfBounds___redArg(v___x_442_);
v___y_479_ = v___x_502_;
goto v___jp_478_;
}
else
{
lean_object* v___x_503_; 
v___x_503_ = l_Lean_PersistentArray_get_x21___redArg(v___x_442_, v_elimEqs_499_, v_a_444_);
lean_dec_ref(v_elimEqs_499_);
v___y_479_ = v___x_503_;
goto v___jp_478_;
}
v___jp_478_:
{
if (lean_obj_tag(v___y_479_) == 0)
{
v___y_460_ = v_a_431_;
v___y_461_ = v_a_439_;
goto v___jp_459_;
}
else
{
lean_object* v___x_480_; 
lean_dec_ref_known(v___y_479_, 1);
lean_inc(v_a_440_);
lean_inc_ref(v_a_439_);
lean_inc(v_a_438_);
lean_inc_ref(v_a_437_);
lean_inc(v_a_436_);
lean_inc_ref(v_a_435_);
lean_inc(v_a_434_);
lean_inc_ref(v_a_433_);
lean_inc(v_a_432_);
lean_inc(v_a_431_);
lean_inc(v_x_430_);
lean_inc(v_a_444_);
v___x_480_ = lean_cutsat_propagate_nonlinear(v_a_444_, v_x_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_490_; 
v_a_481_ = lean_ctor_get(v___x_480_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_490_ == 0)
{
v___x_483_ = v___x_480_;
v_isShared_484_ = v_isSharedCheck_490_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_480_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_490_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
uint8_t v___x_485_; 
v___x_485_ = lean_unbox(v_a_481_);
lean_dec(v_a_481_);
if (v___x_485_ == 0)
{
lean_del_object(v___x_483_);
v___y_460_ = v_a_431_;
v___y_461_ = v_a_439_;
goto v___jp_459_;
}
else
{
lean_object* v___x_486_; lean_object* v___x_488_; 
lean_del_object(v___x_446_);
lean_dec(v_a_444_);
lean_dec(v_x_430_);
v___x_486_ = lean_box(0);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 0, v___x_486_);
v___x_488_ = v___x_483_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v___x_486_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
else
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_498_; 
lean_del_object(v___x_446_);
lean_dec(v_a_444_);
lean_dec(v_x_430_);
v_a_491_ = lean_ctor_get(v___x_480_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_498_ == 0)
{
v___x_493_ = v___x_480_;
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_480_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_498_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_496_; 
if (v_isShared_494_ == 0)
{
v___x_496_ = v___x_493_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_a_491_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
}
}
else
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_511_; 
lean_del_object(v___x_446_);
lean_dec(v_a_444_);
lean_dec(v_x_430_);
v_a_504_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_511_ == 0)
{
v___x_506_ = v___x_476_;
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_476_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_509_; 
if (v_isShared_507_ == 0)
{
v___x_509_ = v___x_506_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_a_504_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
v___jp_448_:
{
uint8_t v___x_451_; 
v___x_451_ = l_List_elem___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1(v_x_430_, v___y_450_);
if (v___x_451_ == 0)
{
lean_object* v___f_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
lean_del_object(v___x_446_);
v___f_452_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___lam__0), 4, 3);
lean_closure_set(v___f_452_, 0, v_x_430_);
lean_closure_set(v___f_452_, 1, v___y_450_);
lean_closure_set(v___f_452_, 2, v_a_444_);
v___x_453_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_454_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_453_, v___f_452_, v___y_449_);
return v___x_454_;
}
else
{
lean_object* v___x_455_; lean_object* v___x_457_; 
lean_dec(v___y_450_);
lean_dec(v_a_444_);
lean_dec(v_x_430_);
v___x_455_ = lean_box(0);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 0, v___x_455_);
v___x_457_ = v___x_446_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v___x_455_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
v___jp_459_:
{
lean_object* v___x_462_; 
v___x_462_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v___y_460_, v___y_461_);
if (lean_obj_tag(v___x_462_) == 0)
{
lean_object* v_a_463_; lean_object* v_nonlinearOccs_464_; lean_object* v___x_465_; 
v_a_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_a_463_);
lean_dec_ref_known(v___x_462_, 1);
v_nonlinearOccs_464_ = lean_ctor_get(v_a_463_, 21);
lean_inc_ref(v_nonlinearOccs_464_);
lean_dec(v_a_463_);
v___x_465_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2___redArg(v_nonlinearOccs_464_, v_a_444_);
lean_dec_ref(v_nonlinearOccs_464_);
if (lean_obj_tag(v___x_465_) == 0)
{
lean_object* v___x_466_; 
v___x_466_ = lean_box(0);
v___y_449_ = v___y_460_;
v___y_450_ = v___x_466_;
goto v___jp_448_;
}
else
{
lean_object* v_val_467_; 
v_val_467_ = lean_ctor_get(v___x_465_, 0);
lean_inc(v_val_467_);
lean_dec_ref_known(v___x_465_, 1);
v___y_449_ = v___y_460_;
v___y_450_ = v_val_467_;
goto v___jp_448_;
}
}
else
{
lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_475_; 
lean_del_object(v___x_446_);
lean_dec(v_a_444_);
lean_dec(v_x_430_);
v_a_468_ = lean_ctor_get(v___x_462_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_462_);
if (v_isSharedCheck_475_ == 0)
{
v___x_470_ = v___x_462_;
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v___x_462_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_475_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_473_; 
if (v_isShared_471_ == 0)
{
v___x_473_ = v___x_470_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_a_468_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
}
}
else
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
lean_dec(v_x_430_);
v_a_513_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_520_ == 0)
{
v___x_515_ = v___x_443_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_443_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_516_ == 0)
{
v___x_518_ = v___x_515_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_a_513_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___boxed(lean_object* v_arg_521_, lean_object* v_x_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_arg_521_, v_x_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
lean_dec(v_a_530_);
lean_dec_ref(v_a_529_);
lean_dec(v_a_528_);
lean_dec_ref(v_a_527_);
lean_dec(v_a_526_);
lean_dec_ref(v_a_525_);
lean_dec(v_a_524_);
lean_dec(v_a_523_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0(lean_object* v_00_u03b2_535_, lean_object* v_x_536_, lean_object* v_x_537_, lean_object* v_x_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0___redArg(v_x_536_, v_x_537_, v_x_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2(lean_object* v_00_u03b2_540_, lean_object* v_x_541_, lean_object* v_x_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2___redArg(v_x_541_, v_x_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2___boxed(lean_object* v_00_u03b2_544_, lean_object* v_x_545_, lean_object* v_x_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2(v_00_u03b2_544_, v_x_545_, v_x_546_);
lean_dec(v_x_546_);
lean_dec_ref(v_x_545_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0(lean_object* v_00_u03b2_548_, lean_object* v_x_549_, size_t v_x_550_, size_t v_x_551_, lean_object* v_x_552_, lean_object* v_x_553_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_x_549_, v_x_550_, v_x_551_, v_x_552_, v_x_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___boxed(lean_object* v_00_u03b2_555_, lean_object* v_x_556_, lean_object* v_x_557_, lean_object* v_x_558_, lean_object* v_x_559_, lean_object* v_x_560_){
_start:
{
size_t v_x_8595__boxed_561_; size_t v_x_8596__boxed_562_; lean_object* v_res_563_; 
v_x_8595__boxed_561_ = lean_unbox_usize(v_x_557_);
lean_dec(v_x_557_);
v_x_8596__boxed_562_ = lean_unbox_usize(v_x_558_);
lean_dec(v_x_558_);
v_res_563_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0(v_00_u03b2_555_, v_x_556_, v_x_8595__boxed_561_, v_x_8596__boxed_562_, v_x_559_, v_x_560_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3(lean_object* v_00_u03b2_564_, lean_object* v_x_565_, size_t v_x_566_, lean_object* v_x_567_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___redArg(v_x_565_, v_x_566_, v_x_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3___boxed(lean_object* v_00_u03b2_569_, lean_object* v_x_570_, lean_object* v_x_571_, lean_object* v_x_572_){
_start:
{
size_t v_x_8612__boxed_573_; lean_object* v_res_574_; 
v_x_8612__boxed_573_ = lean_unbox_usize(v_x_571_);
lean_dec(v_x_571_);
v_res_574_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3(v_00_u03b2_569_, v_x_570_, v_x_8612__boxed_573_, v_x_572_);
lean_dec(v_x_572_);
lean_dec_ref(v_x_570_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_575_, lean_object* v_n_576_, lean_object* v_k_577_, lean_object* v_v_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1___redArg(v_n_576_, v_k_577_, v_v_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_580_, size_t v_depth_581_, lean_object* v_keys_582_, lean_object* v_vals_583_, lean_object* v_heq_584_, lean_object* v_i_585_, lean_object* v_entries_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg(v_depth_581_, v_keys_582_, v_vals_583_, v_i_585_, v_entries_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_588_, lean_object* v_depth_589_, lean_object* v_keys_590_, lean_object* v_vals_591_, lean_object* v_heq_592_, lean_object* v_i_593_, lean_object* v_entries_594_){
_start:
{
size_t v_depth_boxed_595_; lean_object* v_res_596_; 
v_depth_boxed_595_ = lean_unbox_usize(v_depth_589_);
lean_dec(v_depth_589_);
v_res_596_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2(v_00_u03b2_588_, v_depth_boxed_595_, v_keys_590_, v_vals_591_, v_heq_592_, v_i_593_, v_entries_594_);
lean_dec_ref(v_vals_591_);
lean_dec_ref(v_keys_590_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_597_, lean_object* v_keys_598_, lean_object* v_vals_599_, lean_object* v_heq_600_, lean_object* v_i_601_, lean_object* v_k_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6___redArg(v_keys_598_, v_vals_599_, v_i_601_, v_k_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_604_, lean_object* v_keys_605_, lean_object* v_vals_606_, lean_object* v_heq_607_, lean_object* v_i_608_, lean_object* v_k_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__2_spec__3_spec__6(v_00_u03b2_604_, v_keys_605_, v_vals_606_, v_heq_607_, v_i_608_, v_k_609_);
lean_dec(v_k_609_);
lean_dec_ref(v_vals_606_);
lean_dec_ref(v_keys_605_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_611_, lean_object* v_x_612_, lean_object* v_x_613_, lean_object* v_x_614_, lean_object* v_x_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__4___redArg(v_x_612_, v_x_613_, v_x_614_, v_x_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(lean_object* v_x_617_, lean_object* v_e_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_){
_start:
{
lean_object* v___x_630_; 
lean_inc_ref(v_e_618_);
v___x_630_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_618_, v_a_626_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v_a_631_; lean_object* v___x_632_; uint8_t v___x_633_; 
v_a_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_a_631_);
lean_dec_ref_known(v___x_630_, 1);
v___x_632_ = l_Lean_Expr_cleanupAnnotations(v_a_631_);
lean_dec(v_a_631_);
v___x_633_ = l_Lean_Expr_isApp(v___x_632_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; 
lean_dec_ref(v___x_632_);
v___x_634_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_618_, v_x_617_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
return v___x_634_;
}
else
{
lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_635_ = l_Lean_Expr_appFnCleanup___redArg(v___x_632_);
v___x_636_ = l_Lean_Expr_isApp(v___x_635_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; 
lean_dec_ref(v___x_635_);
lean_dec_ref(v___x_632_);
v___x_637_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_618_, v_x_617_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
return v___x_637_;
}
else
{
lean_object* v___x_638_; uint8_t v___x_639_; 
v___x_638_ = l_Lean_Expr_appFnCleanup___redArg(v___x_635_);
v___x_639_ = l_Lean_Expr_isApp(v___x_638_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; 
lean_dec_ref(v___x_638_);
lean_dec_ref(v___x_635_);
lean_dec_ref(v___x_632_);
v___x_640_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_618_, v_x_617_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
return v___x_640_;
}
else
{
lean_object* v___x_641_; uint8_t v___x_642_; 
v___x_641_ = l_Lean_Expr_appFnCleanup___redArg(v___x_638_);
v___x_642_ = l_Lean_Expr_isApp(v___x_641_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; 
lean_dec_ref(v___x_641_);
lean_dec_ref(v___x_638_);
lean_dec_ref(v___x_635_);
lean_dec_ref(v___x_632_);
v___x_643_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_618_, v_x_617_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
return v___x_643_;
}
else
{
lean_object* v___x_644_; uint8_t v___x_645_; 
v___x_644_ = l_Lean_Expr_appFnCleanup___redArg(v___x_641_);
lean_dec_ref(v___x_641_);
v___x_645_ = l_Lean_Expr_isApp(v___x_644_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; 
lean_dec_ref(v___x_644_);
lean_dec_ref(v___x_638_);
lean_dec_ref(v___x_635_);
lean_dec_ref(v___x_632_);
v___x_646_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_618_, v_x_617_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
return v___x_646_;
}
else
{
lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_647_ = l_Lean_Expr_appFnCleanup___redArg(v___x_644_);
lean_dec_ref(v___x_644_);
v___x_648_ = l_Lean_Expr_isApp(v___x_647_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; 
lean_dec_ref(v___x_647_);
lean_dec_ref(v___x_638_);
lean_dec_ref(v___x_635_);
lean_dec_ref(v___x_632_);
v___x_649_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_618_, v_x_617_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
return v___x_649_;
}
else
{
lean_object* v___x_650_; lean_object* v___x_651_; uint8_t v___x_652_; 
v___x_650_ = l_Lean_Expr_appFnCleanup___redArg(v___x_647_);
lean_dec_ref(v___x_647_);
v___x_651_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11));
v___x_652_ = l_Lean_Expr_isConstOf(v___x_650_, v___x_651_);
lean_dec_ref(v___x_650_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; 
lean_dec_ref(v___x_638_);
lean_dec_ref(v___x_635_);
lean_dec_ref(v___x_632_);
v___x_653_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_618_, v_x_617_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
return v___x_653_;
}
else
{
lean_object* v_arg_654_; lean_object* v_arg_655_; lean_object* v_arg_656_; lean_object* v___x_657_; 
v_arg_654_ = lean_ctor_get(v___x_632_, 1);
lean_inc_ref(v_arg_654_);
lean_dec_ref(v___x_632_);
v_arg_655_ = lean_ctor_get(v___x_635_, 1);
lean_inc_ref(v_arg_655_);
lean_dec_ref(v___x_635_);
v_arg_656_ = lean_ctor_get(v___x_638_, 1);
lean_inc_ref(v_arg_656_);
lean_dec_ref(v___x_638_);
v___x_657_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_656_, v_a_626_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_a_658_; uint8_t v___x_659_; 
v_a_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_a_658_);
lean_dec_ref_known(v___x_657_, 1);
v___x_659_ = lean_unbox(v_a_658_);
lean_dec(v_a_658_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; 
lean_dec_ref(v_arg_655_);
lean_dec_ref(v_arg_654_);
v___x_660_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_618_, v_x_617_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
return v___x_660_;
}
else
{
lean_object* v___x_661_; 
lean_dec_ref(v_e_618_);
lean_inc(v_x_617_);
v___x_661_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(v_x_617_, v_arg_655_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_dec_ref_known(v___x_661_, 1);
v_e_618_ = v_arg_654_;
goto _start;
}
else
{
lean_dec_ref(v_arg_654_);
lean_dec(v_x_617_);
return v___x_661_;
}
}
}
else
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_670_; 
lean_dec_ref(v_arg_655_);
lean_dec_ref(v_arg_654_);
lean_dec_ref(v_e_618_);
lean_dec(v_x_617_);
v_a_663_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_670_ == 0)
{
v___x_665_ = v___x_657_;
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_657_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_668_; 
if (v_isShared_666_ == 0)
{
v___x_668_ = v___x_665_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_a_663_);
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
}
}
}
}
}
}
}
else
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_678_; 
lean_dec_ref(v_e_618_);
lean_dec(v_x_617_);
v_a_671_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_678_ == 0)
{
v___x_673_ = v___x_630_;
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_630_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_676_; 
if (v_isShared_674_ == 0)
{
v___x_676_ = v___x_673_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_a_671_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go___boxed(lean_object* v_x_679_, lean_object* v_e_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(v_x_679_, v_e_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
lean_dec(v_a_690_);
lean_dec_ref(v_a_689_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
lean_dec(v_a_686_);
lean_dec_ref(v_a_685_);
lean_dec(v_a_684_);
lean_dec_ref(v_a_683_);
lean_dec(v_a_682_);
lean_dec(v_a_681_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt(lean_object* v_e_693_, lean_object* v_x_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_693_, v_a_702_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v_a_713_; lean_object* v___x_714_; uint8_t v___x_715_; 
v_a_713_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_a_713_);
lean_dec_ref_known(v___x_712_, 1);
v___x_714_ = l_Lean_Expr_cleanupAnnotations(v_a_713_);
lean_dec(v_a_713_);
v___x_715_ = l_Lean_Expr_isApp(v___x_714_);
if (v___x_715_ == 0)
{
lean_dec_ref(v___x_714_);
lean_dec(v_x_694_);
goto v___jp_709_;
}
else
{
lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_716_ = l_Lean_Expr_appFnCleanup___redArg(v___x_714_);
v___x_717_ = l_Lean_Expr_isApp(v___x_716_);
if (v___x_717_ == 0)
{
lean_dec_ref(v___x_716_);
lean_dec_ref(v___x_714_);
lean_dec(v_x_694_);
goto v___jp_709_;
}
else
{
lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_718_ = l_Lean_Expr_appFnCleanup___redArg(v___x_716_);
v___x_719_ = l_Lean_Expr_isApp(v___x_718_);
if (v___x_719_ == 0)
{
lean_dec_ref(v___x_718_);
lean_dec_ref(v___x_716_);
lean_dec_ref(v___x_714_);
lean_dec(v_x_694_);
goto v___jp_709_;
}
else
{
lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_720_ = l_Lean_Expr_appFnCleanup___redArg(v___x_718_);
lean_dec_ref(v___x_718_);
v___x_721_ = l_Lean_Expr_isApp(v___x_720_);
if (v___x_721_ == 0)
{
lean_dec_ref(v___x_720_);
lean_dec_ref(v___x_716_);
lean_dec_ref(v___x_714_);
lean_dec(v_x_694_);
goto v___jp_709_;
}
else
{
lean_object* v___x_722_; uint8_t v___x_723_; 
v___x_722_ = l_Lean_Expr_appFnCleanup___redArg(v___x_720_);
lean_dec_ref(v___x_720_);
v___x_723_ = l_Lean_Expr_isApp(v___x_722_);
if (v___x_723_ == 0)
{
lean_dec_ref(v___x_722_);
lean_dec_ref(v___x_716_);
lean_dec_ref(v___x_714_);
lean_dec(v_x_694_);
goto v___jp_709_;
}
else
{
lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_724_ = l_Lean_Expr_appFnCleanup___redArg(v___x_722_);
lean_dec_ref(v___x_722_);
v___x_725_ = l_Lean_Expr_isApp(v___x_724_);
if (v___x_725_ == 0)
{
lean_dec_ref(v___x_724_);
lean_dec_ref(v___x_716_);
lean_dec_ref(v___x_714_);
lean_dec(v_x_694_);
goto v___jp_709_;
}
else
{
lean_object* v_arg_726_; lean_object* v___y_728_; lean_object* v___y_729_; lean_object* v___y_730_; lean_object* v___y_731_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v_arg_784_; lean_object* v___x_785_; lean_object* v___x_786_; uint8_t v___x_787_; 
v_arg_726_ = lean_ctor_get(v___x_714_, 1);
lean_inc_ref(v_arg_726_);
lean_dec_ref(v___x_714_);
v_arg_784_ = lean_ctor_get(v___x_716_, 1);
lean_inc_ref(v_arg_784_);
lean_dec_ref(v___x_716_);
v___x_785_ = l_Lean_Expr_appFnCleanup___redArg(v___x_724_);
lean_dec_ref(v___x_724_);
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
lean_dec_ref(v_arg_784_);
lean_dec_ref(v_arg_726_);
lean_dec(v_x_694_);
goto v___jp_709_;
}
else
{
lean_object* v___x_794_; 
lean_inc(v_x_694_);
v___x_794_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(v_x_694_, v_arg_784_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v___x_795_; 
lean_dec_ref_known(v___x_794_, 1);
v___x_795_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(v_x_694_, v_arg_726_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_);
return v___x_795_;
}
else
{
lean_dec_ref(v_arg_726_);
lean_dec(v_x_694_);
return v___x_794_;
}
}
}
else
{
lean_object* v___x_796_; 
lean_dec_ref(v___x_785_);
lean_dec_ref(v_arg_784_);
v___x_796_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_arg_726_, v_x_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_);
return v___x_796_;
}
}
else
{
lean_object* v___x_797_; 
lean_dec_ref(v___x_785_);
lean_dec_ref(v_arg_784_);
v___x_797_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_arg_726_, v_x_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_);
return v___x_797_;
}
}
else
{
lean_object* v___x_798_; 
lean_dec_ref(v___x_785_);
lean_inc_ref(v_arg_784_);
v___x_798_ = l_Lean_Meta_isIntValue(v_arg_784_, v_a_701_, v_a_702_, v_a_703_, v_a_704_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; uint8_t v___x_800_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_a_799_);
lean_dec_ref_known(v___x_798_, 1);
v___x_800_ = lean_unbox(v_a_799_);
lean_dec(v_a_799_);
if (v___x_800_ == 0)
{
lean_object* v___x_801_; 
lean_inc(v_x_694_);
v___x_801_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_arg_784_, v_x_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_dec_ref_known(v___x_801_, 1);
v___y_728_ = v_a_695_;
v___y_729_ = v_a_696_;
v___y_730_ = v_a_697_;
v___y_731_ = v_a_698_;
v___y_732_ = v_a_699_;
v___y_733_ = v_a_700_;
v___y_734_ = v_a_701_;
v___y_735_ = v_a_702_;
v___y_736_ = v_a_703_;
v___y_737_ = v_a_704_;
goto v___jp_727_;
}
else
{
lean_dec_ref(v_arg_726_);
lean_dec(v_x_694_);
return v___x_801_;
}
}
else
{
lean_dec_ref(v_arg_784_);
v___y_728_ = v_a_695_;
v___y_729_ = v_a_696_;
v___y_730_ = v_a_697_;
v___y_731_ = v_a_698_;
v___y_732_ = v_a_699_;
v___y_733_ = v_a_700_;
v___y_734_ = v_a_701_;
v___y_735_ = v_a_702_;
v___y_736_ = v_a_703_;
v___y_737_ = v_a_704_;
goto v___jp_727_;
}
}
else
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_809_; 
lean_dec_ref(v_arg_784_);
lean_dec_ref(v_arg_726_);
lean_dec(v_x_694_);
v_a_802_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_809_ == 0)
{
v___x_804_ = v___x_798_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_798_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_807_; 
if (v_isShared_805_ == 0)
{
v___x_807_ = v___x_804_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_802_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
v___jp_727_:
{
lean_object* v___x_738_; 
lean_inc_ref(v_arg_726_);
v___x_738_ = l_Lean_Meta_isIntValue(v_arg_726_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; uint8_t v___x_740_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_739_);
lean_dec_ref_known(v___x_738_, 1);
v___x_740_ = lean_unbox(v_a_739_);
lean_dec(v_a_739_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; 
v___x_741_ = l_Lean_Meta_isNatValue(v_arg_726_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v_a_742_; uint8_t v___x_743_; 
v_a_742_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_a_742_);
lean_dec_ref_known(v___x_741_, 1);
v___x_743_ = lean_unbox(v_a_742_);
lean_dec(v_a_742_);
if (v___x_743_ == 0)
{
lean_object* v___x_744_; 
lean_inc_ref(v_arg_726_);
v___x_744_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_arg_726_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; lean_object* v_fst_746_; lean_object* v___x_747_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_a_745_);
lean_dec_ref_known(v___x_744_, 1);
v_fst_746_ = lean_ctor_get(v_a_745_, 0);
lean_inc(v_fst_746_);
lean_dec(v_a_745_);
v___x_747_ = l_Lean_Meta_Grind_getGeneration___redArg(v_arg_726_, v___y_728_);
lean_dec_ref(v_arg_726_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v_a_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_748_);
lean_dec_ref_known(v___x_747_, 1);
v___x_749_ = lean_box(0);
lean_inc(v___y_737_);
lean_inc_ref(v___y_736_);
lean_inc(v___y_735_);
lean_inc_ref(v___y_734_);
lean_inc(v___y_733_);
lean_inc_ref(v___y_732_);
lean_inc(v___y_731_);
lean_inc_ref(v___y_730_);
lean_inc(v___y_729_);
lean_inc(v___y_728_);
lean_inc(v_fst_746_);
v___x_750_ = lean_grind_internalize(v_fst_746_, v_a_748_, v___x_749_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v___x_751_; 
lean_dec_ref_known(v___x_750_, 1);
v___x_751_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_fst_746_, v_x_694_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
return v___x_751_;
}
else
{
lean_dec(v_fst_746_);
lean_dec(v_x_694_);
return v___x_750_;
}
}
else
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_759_; 
lean_dec(v_fst_746_);
lean_dec(v_x_694_);
v_a_752_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_759_ == 0)
{
v___x_754_ = v___x_747_;
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_747_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_757_; 
if (v_isShared_755_ == 0)
{
v___x_757_ = v___x_754_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_a_752_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
else
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
lean_dec_ref(v_arg_726_);
lean_dec(v_x_694_);
v_a_760_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_744_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_744_);
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
lean_dec_ref(v_arg_726_);
lean_dec(v_x_694_);
goto v___jp_706_;
}
}
else
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
lean_dec_ref(v_arg_726_);
lean_dec(v_x_694_);
v_a_768_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_741_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_741_);
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
lean_dec_ref(v_arg_726_);
lean_dec(v_x_694_);
goto v___jp_706_;
}
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_dec_ref(v_arg_726_);
lean_dec(v_x_694_);
v_a_776_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_738_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_738_);
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
}
}
}
}
}
}
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_dec(v_x_694_);
v_a_810_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_712_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_712_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
v___jp_706_:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = lean_box(0);
v___x_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
return v___x_708_;
}
v___jp_709_:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = lean_box(0);
v___x_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
return v___x_711_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt___boxed(lean_object* v_e_818_, lean_object* v_x_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt(v_e_818_, v_x_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
lean_dec(v_a_827_);
lean_dec_ref(v_a_826_);
lean_dec(v_a_825_);
lean_dec_ref(v_a_824_);
lean_dec(v_a_823_);
lean_dec_ref(v_a_822_);
lean_dec(v_a_821_);
lean_dec(v_a_820_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertVarFacts(lean_object* v_e_832_, lean_object* v_x_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_){
_start:
{
lean_object* v___x_845_; 
lean_inc(v_x_833_);
v___x_845_ = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(v_e_832_, v_x_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v___x_846_; 
lean_dec_ref_known(v___x_845_, 1);
lean_inc(v_x_833_);
lean_inc_ref(v_e_832_);
v___x_846_ = l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg(v_e_832_, v_x_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v___x_847_; 
lean_dec_ref_known(v___x_846_, 1);
lean_inc_ref(v_e_832_);
v___x_847_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm(v_e_832_, v_a_840_, v_a_841_, v_a_842_, v_a_843_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_858_; 
v_a_848_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_858_ == 0)
{
v___x_850_ = v___x_847_;
v_isShared_851_ = v_isSharedCheck_858_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_847_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_858_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
uint8_t v___x_852_; 
v___x_852_ = lean_unbox(v_a_848_);
lean_dec(v_a_848_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; lean_object* v___x_855_; 
lean_dec(v_x_833_);
lean_dec_ref(v_e_832_);
v___x_853_ = lean_box(0);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v___x_853_);
v___x_855_ = v___x_850_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_853_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
else
{
lean_object* v___x_857_; 
lean_del_object(v___x_850_);
v___x_857_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt(v_e_832_, v_x_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_);
return v___x_857_;
}
}
}
else
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_866_; 
lean_dec(v_x_833_);
lean_dec_ref(v_e_832_);
v_a_859_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_866_ == 0)
{
v___x_861_ = v___x_847_;
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_847_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_864_; 
if (v_isShared_862_ == 0)
{
v___x_864_ = v___x_861_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_a_859_);
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
else
{
lean_dec(v_x_833_);
lean_dec_ref(v_e_832_);
return v___x_846_;
}
}
else
{
lean_dec(v_x_833_);
lean_dec_ref(v_e_832_);
return v___x_845_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertVarFacts___boxed(lean_object* v_e_867_, lean_object* v_x_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Lean_Meta_Grind_Arith_Cutsat_assertVarFacts(v_e_867_, v_x_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
lean_dec(v_a_878_);
lean_dec_ref(v_a_877_);
lean_dec(v_a_876_);
lean_dec_ref(v_a_875_);
lean_dec(v_a_874_);
lean_dec_ref(v_a_873_);
lean_dec(v_a_872_);
lean_dec_ref(v_a_871_);
lean_dec(v_a_870_);
lean_dec(v_a_869_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_x_881_, lean_object* v_x_882_, lean_object* v_x_883_, lean_object* v_x_884_){
_start:
{
lean_object* v_ks_885_; lean_object* v_vs_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_912_; 
v_ks_885_ = lean_ctor_get(v_x_881_, 0);
v_vs_886_ = lean_ctor_get(v_x_881_, 1);
v_isSharedCheck_912_ = !lean_is_exclusive(v_x_881_);
if (v_isSharedCheck_912_ == 0)
{
v___x_888_ = v_x_881_;
v_isShared_889_ = v_isSharedCheck_912_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_vs_886_);
lean_inc(v_ks_885_);
lean_dec(v_x_881_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_912_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_890_; uint8_t v___x_891_; 
v___x_890_ = lean_array_get_size(v_ks_885_);
v___x_891_ = lean_nat_dec_lt(v_x_882_, v___x_890_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_895_; 
lean_dec(v_x_882_);
v___x_892_ = lean_array_push(v_ks_885_, v_x_883_);
v___x_893_ = lean_array_push(v_vs_886_, v_x_884_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 1, v___x_893_);
lean_ctor_set(v___x_888_, 0, v___x_892_);
v___x_895_ = v___x_888_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_892_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v___x_893_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
else
{
lean_object* v_k_x27_897_; size_t v___x_898_; size_t v___x_899_; uint8_t v___x_900_; 
v_k_x27_897_ = lean_array_fget_borrowed(v_ks_885_, v_x_882_);
v___x_898_ = lean_ptr_addr(v_x_883_);
v___x_899_ = lean_ptr_addr(v_k_x27_897_);
v___x_900_ = lean_usize_dec_eq(v___x_898_, v___x_899_);
if (v___x_900_ == 0)
{
lean_object* v___x_902_; 
if (v_isShared_889_ == 0)
{
v___x_902_ = v___x_888_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_ks_885_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v_vs_886_);
v___x_902_ = v_reuseFailAlloc_906_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = lean_unsigned_to_nat(1u);
v___x_904_ = lean_nat_add(v_x_882_, v___x_903_);
lean_dec(v_x_882_);
v_x_881_ = v___x_902_;
v_x_882_ = v___x_904_;
goto _start;
}
}
else
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_910_; 
v___x_907_ = lean_array_fset(v_ks_885_, v_x_882_, v_x_883_);
v___x_908_ = lean_array_fset(v_vs_886_, v_x_882_, v_x_884_);
lean_dec(v_x_882_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 1, v___x_908_);
lean_ctor_set(v___x_888_, 0, v___x_907_);
v___x_910_ = v___x_888_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_907_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v___x_908_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4___redArg(lean_object* v_n_913_, lean_object* v_k_914_, lean_object* v_v_915_){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_916_ = lean_unsigned_to_nat(0u);
v___x_917_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7___redArg(v_n_913_, v___x_916_, v_k_914_, v_v_915_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(lean_object* v_x_918_, size_t v_x_919_, size_t v_x_920_, lean_object* v_x_921_, lean_object* v_x_922_){
_start:
{
if (lean_obj_tag(v_x_918_) == 0)
{
lean_object* v_es_923_; size_t v___x_924_; size_t v___x_925_; lean_object* v_j_926_; lean_object* v___x_927_; uint8_t v___x_928_; 
v_es_923_ = lean_ctor_get(v_x_918_, 0);
v___x_924_ = ((size_t)31ULL);
v___x_925_ = lean_usize_land(v_x_919_, v___x_924_);
v_j_926_ = lean_usize_to_nat(v___x_925_);
v___x_927_ = lean_array_get_size(v_es_923_);
v___x_928_ = lean_nat_dec_lt(v_j_926_, v___x_927_);
if (v___x_928_ == 0)
{
lean_dec(v_j_926_);
lean_dec(v_x_922_);
lean_dec_ref(v_x_921_);
return v_x_918_;
}
else
{
lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_969_; 
lean_inc_ref(v_es_923_);
v_isSharedCheck_969_ = !lean_is_exclusive(v_x_918_);
if (v_isSharedCheck_969_ == 0)
{
lean_object* v_unused_970_; 
v_unused_970_ = lean_ctor_get(v_x_918_, 0);
lean_dec(v_unused_970_);
v___x_930_ = v_x_918_;
v_isShared_931_ = v_isSharedCheck_969_;
goto v_resetjp_929_;
}
else
{
lean_dec(v_x_918_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_969_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v_v_932_; lean_object* v___x_933_; lean_object* v_xs_x27_934_; lean_object* v___y_936_; 
v_v_932_ = lean_array_fget(v_es_923_, v_j_926_);
v___x_933_ = lean_box(0);
v_xs_x27_934_ = lean_array_fset(v_es_923_, v_j_926_, v___x_933_);
switch(lean_obj_tag(v_v_932_))
{
case 0:
{
lean_object* v_key_941_; lean_object* v_val_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_954_; 
v_key_941_ = lean_ctor_get(v_v_932_, 0);
v_val_942_ = lean_ctor_get(v_v_932_, 1);
v_isSharedCheck_954_ = !lean_is_exclusive(v_v_932_);
if (v_isSharedCheck_954_ == 0)
{
v___x_944_ = v_v_932_;
v_isShared_945_ = v_isSharedCheck_954_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_val_942_);
lean_inc(v_key_941_);
lean_dec(v_v_932_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_954_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
size_t v___x_946_; size_t v___x_947_; uint8_t v___x_948_; 
v___x_946_ = lean_ptr_addr(v_x_921_);
v___x_947_ = lean_ptr_addr(v_key_941_);
v___x_948_ = lean_usize_dec_eq(v___x_946_, v___x_947_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; lean_object* v___x_950_; 
lean_del_object(v___x_944_);
v___x_949_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_941_, v_val_942_, v_x_921_, v_x_922_);
v___x_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
v___y_936_ = v___x_950_;
goto v___jp_935_;
}
else
{
lean_object* v___x_952_; 
lean_dec(v_val_942_);
lean_dec(v_key_941_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 1, v_x_922_);
lean_ctor_set(v___x_944_, 0, v_x_921_);
v___x_952_ = v___x_944_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_x_921_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v_x_922_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
v___y_936_ = v___x_952_;
goto v___jp_935_;
}
}
}
}
case 1:
{
lean_object* v_node_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_967_; 
v_node_955_ = lean_ctor_get(v_v_932_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v_v_932_);
if (v_isSharedCheck_967_ == 0)
{
v___x_957_ = v_v_932_;
v_isShared_958_ = v_isSharedCheck_967_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_node_955_);
lean_dec(v_v_932_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_967_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
size_t v___x_959_; size_t v___x_960_; size_t v___x_961_; size_t v___x_962_; lean_object* v___x_963_; lean_object* v___x_965_; 
v___x_959_ = ((size_t)5ULL);
v___x_960_ = lean_usize_shift_right(v_x_919_, v___x_959_);
v___x_961_ = ((size_t)1ULL);
v___x_962_ = lean_usize_add(v_x_920_, v___x_961_);
v___x_963_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_node_955_, v___x_960_, v___x_962_, v_x_921_, v_x_922_);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 0, v___x_963_);
v___x_965_ = v___x_957_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_963_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
v___y_936_ = v___x_965_;
goto v___jp_935_;
}
}
}
default: 
{
lean_object* v___x_968_; 
v___x_968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_968_, 0, v_x_921_);
lean_ctor_set(v___x_968_, 1, v_x_922_);
v___y_936_ = v___x_968_;
goto v___jp_935_;
}
}
v___jp_935_:
{
lean_object* v___x_937_; lean_object* v___x_939_; 
v___x_937_ = lean_array_fset(v_xs_x27_934_, v_j_926_, v___y_936_);
lean_dec(v_j_926_);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 0, v___x_937_);
v___x_939_ = v___x_930_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v___x_937_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
}
else
{
lean_object* v_ks_971_; lean_object* v_vs_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_990_; 
v_ks_971_ = lean_ctor_get(v_x_918_, 0);
v_vs_972_ = lean_ctor_get(v_x_918_, 1);
v_isSharedCheck_990_ = !lean_is_exclusive(v_x_918_);
if (v_isSharedCheck_990_ == 0)
{
v___x_974_ = v_x_918_;
v_isShared_975_ = v_isSharedCheck_990_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_vs_972_);
lean_inc(v_ks_971_);
lean_dec(v_x_918_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_990_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_977_; 
if (v_isShared_975_ == 0)
{
v___x_977_ = v___x_974_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_ks_971_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v_vs_972_);
v___x_977_ = v_reuseFailAlloc_989_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
lean_object* v_newNode_978_; size_t v___x_979_; uint8_t v___x_980_; 
v_newNode_978_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4___redArg(v___x_977_, v_x_921_, v_x_922_);
v___x_979_ = ((size_t)7ULL);
v___x_980_ = lean_usize_dec_le(v___x_979_, v_x_920_);
if (v___x_980_ == 0)
{
lean_object* v___x_981_; lean_object* v___x_982_; uint8_t v___x_983_; 
v___x_981_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_978_);
v___x_982_ = lean_unsigned_to_nat(4u);
v___x_983_ = lean_nat_dec_lt(v___x_981_, v___x_982_);
lean_dec(v___x_981_);
if (v___x_983_ == 0)
{
lean_object* v_ks_984_; lean_object* v_vs_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v_ks_984_ = lean_ctor_get(v_newNode_978_, 0);
lean_inc_ref(v_ks_984_);
v_vs_985_ = lean_ctor_get(v_newNode_978_, 1);
lean_inc_ref(v_vs_985_);
lean_dec_ref(v_newNode_978_);
v___x_986_ = lean_unsigned_to_nat(0u);
v___x_987_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0);
v___x_988_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(v_x_920_, v_ks_984_, v_vs_985_, v___x_986_, v___x_987_);
lean_dec_ref(v_vs_985_);
lean_dec_ref(v_ks_984_);
return v___x_988_;
}
else
{
return v_newNode_978_;
}
}
else
{
return v_newNode_978_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(size_t v_depth_991_, lean_object* v_keys_992_, lean_object* v_vals_993_, lean_object* v_i_994_, lean_object* v_entries_995_){
_start:
{
lean_object* v___x_996_; uint8_t v___x_997_; 
v___x_996_ = lean_array_get_size(v_keys_992_);
v___x_997_ = lean_nat_dec_lt(v_i_994_, v___x_996_);
if (v___x_997_ == 0)
{
lean_dec(v_i_994_);
return v_entries_995_;
}
else
{
lean_object* v_k_998_; lean_object* v_v_999_; size_t v___x_1000_; size_t v___x_1001_; size_t v___x_1002_; uint64_t v___x_1003_; size_t v_h_1004_; size_t v___x_1005_; lean_object* v___x_1006_; size_t v___x_1007_; size_t v___x_1008_; size_t v___x_1009_; size_t v_h_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v_k_998_ = lean_array_fget_borrowed(v_keys_992_, v_i_994_);
v_v_999_ = lean_array_fget_borrowed(v_vals_993_, v_i_994_);
v___x_1000_ = lean_ptr_addr(v_k_998_);
v___x_1001_ = ((size_t)3ULL);
v___x_1002_ = lean_usize_shift_right(v___x_1000_, v___x_1001_);
v___x_1003_ = lean_usize_to_uint64(v___x_1002_);
v_h_1004_ = lean_uint64_to_usize(v___x_1003_);
v___x_1005_ = ((size_t)5ULL);
v___x_1006_ = lean_unsigned_to_nat(1u);
v___x_1007_ = ((size_t)1ULL);
v___x_1008_ = lean_usize_sub(v_depth_991_, v___x_1007_);
v___x_1009_ = lean_usize_mul(v___x_1005_, v___x_1008_);
v_h_1010_ = lean_usize_shift_right(v_h_1004_, v___x_1009_);
v___x_1011_ = lean_nat_add(v_i_994_, v___x_1006_);
lean_dec(v_i_994_);
lean_inc(v_v_999_);
lean_inc(v_k_998_);
v___x_1012_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_entries_995_, v_h_1010_, v_depth_991_, v_k_998_, v_v_999_);
v_i_994_ = v___x_1011_;
v_entries_995_ = v___x_1012_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_1014_, lean_object* v_keys_1015_, lean_object* v_vals_1016_, lean_object* v_i_1017_, lean_object* v_entries_1018_){
_start:
{
size_t v_depth_boxed_1019_; lean_object* v_res_1020_; 
v_depth_boxed_1019_ = lean_unbox_usize(v_depth_1014_);
lean_dec(v_depth_1014_);
v_res_1020_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(v_depth_boxed_1019_, v_keys_1015_, v_vals_1016_, v_i_1017_, v_entries_1018_);
lean_dec_ref(v_vals_1016_);
lean_dec_ref(v_keys_1015_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg___boxed(lean_object* v_x_1021_, lean_object* v_x_1022_, lean_object* v_x_1023_, lean_object* v_x_1024_, lean_object* v_x_1025_){
_start:
{
size_t v_x_25020__boxed_1026_; size_t v_x_25021__boxed_1027_; lean_object* v_res_1028_; 
v_x_25020__boxed_1026_ = lean_unbox_usize(v_x_1022_);
lean_dec(v_x_1022_);
v_x_25021__boxed_1027_ = lean_unbox_usize(v_x_1023_);
lean_dec(v_x_1023_);
v_res_1028_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_x_1021_, v_x_25020__boxed_1026_, v_x_25021__boxed_1027_, v_x_1024_, v_x_1025_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg(lean_object* v_x_1029_, lean_object* v_x_1030_, lean_object* v_x_1031_){
_start:
{
size_t v___x_1032_; size_t v___x_1033_; size_t v___x_1034_; uint64_t v___x_1035_; size_t v___x_1036_; size_t v___x_1037_; lean_object* v___x_1038_; 
v___x_1032_ = lean_ptr_addr(v_x_1030_);
v___x_1033_ = ((size_t)3ULL);
v___x_1034_ = lean_usize_shift_right(v___x_1032_, v___x_1033_);
v___x_1035_ = lean_usize_to_uint64(v___x_1034_);
v___x_1036_ = lean_uint64_to_usize(v___x_1035_);
v___x_1037_ = ((size_t)1ULL);
v___x_1038_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_x_1029_, v___x_1036_, v___x_1037_, v_x_1030_, v_x_1031_);
return v___x_1038_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1039_ = lean_unsigned_to_nat(32u);
v___x_1040_ = lean_mk_empty_array_with_capacity(v___x_1039_);
v___x_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
return v___x_1041_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1(void){
_start:
{
size_t v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1042_ = ((size_t)5ULL);
v___x_1043_ = lean_unsigned_to_nat(0u);
v___x_1044_ = lean_unsigned_to_nat(32u);
v___x_1045_ = lean_mk_empty_array_with_capacity(v___x_1044_);
v___x_1046_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0);
v___x_1047_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
lean_ctor_set(v___x_1047_, 1, v___x_1045_);
lean_ctor_set(v___x_1047_, 2, v___x_1043_);
lean_ctor_set(v___x_1047_, 3, v___x_1043_);
lean_ctor_set_usize(v___x_1047_, 4, v___x_1042_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0(lean_object* v_expr_1048_, lean_object* v_size_1049_, lean_object* v_s_1050_){
_start:
{
lean_object* v_vars_1051_; lean_object* v_varMap_1052_; lean_object* v_varsHistory_1053_; lean_object* v_natToIntMap_1054_; lean_object* v_natDef_1055_; lean_object* v_dvds_1056_; lean_object* v_lowers_1057_; lean_object* v_uppers_1058_; lean_object* v_diseqs_1059_; lean_object* v_elimEqs_1060_; lean_object* v_active_1061_; lean_object* v_elimStack_1062_; lean_object* v_occurs_1063_; lean_object* v_assignment_1064_; lean_object* v_nextCnstrId_1065_; uint8_t v_caseSplits_1066_; lean_object* v_steps_1067_; lean_object* v_penalties_1068_; lean_object* v_numReorderRequests_1069_; lean_object* v_conflict_x3f_1070_; lean_object* v_diseqSplits_1071_; lean_object* v_divMod_1072_; uint8_t v_usedCommRing_1073_; lean_object* v_nonlinearOccs_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1095_; 
v_vars_1051_ = lean_ctor_get(v_s_1050_, 0);
v_varMap_1052_ = lean_ctor_get(v_s_1050_, 1);
v_varsHistory_1053_ = lean_ctor_get(v_s_1050_, 2);
v_natToIntMap_1054_ = lean_ctor_get(v_s_1050_, 3);
v_natDef_1055_ = lean_ctor_get(v_s_1050_, 4);
v_dvds_1056_ = lean_ctor_get(v_s_1050_, 5);
v_lowers_1057_ = lean_ctor_get(v_s_1050_, 6);
v_uppers_1058_ = lean_ctor_get(v_s_1050_, 7);
v_diseqs_1059_ = lean_ctor_get(v_s_1050_, 8);
v_elimEqs_1060_ = lean_ctor_get(v_s_1050_, 9);
v_active_1061_ = lean_ctor_get(v_s_1050_, 10);
v_elimStack_1062_ = lean_ctor_get(v_s_1050_, 11);
v_occurs_1063_ = lean_ctor_get(v_s_1050_, 12);
v_assignment_1064_ = lean_ctor_get(v_s_1050_, 13);
v_nextCnstrId_1065_ = lean_ctor_get(v_s_1050_, 14);
v_caseSplits_1066_ = lean_ctor_get_uint8(v_s_1050_, sizeof(void*)*22);
v_steps_1067_ = lean_ctor_get(v_s_1050_, 15);
v_penalties_1068_ = lean_ctor_get(v_s_1050_, 16);
v_numReorderRequests_1069_ = lean_ctor_get(v_s_1050_, 17);
v_conflict_x3f_1070_ = lean_ctor_get(v_s_1050_, 18);
v_diseqSplits_1071_ = lean_ctor_get(v_s_1050_, 19);
v_divMod_1072_ = lean_ctor_get(v_s_1050_, 20);
v_usedCommRing_1073_ = lean_ctor_get_uint8(v_s_1050_, sizeof(void*)*22 + 1);
v_nonlinearOccs_1074_ = lean_ctor_get(v_s_1050_, 21);
v_isSharedCheck_1095_ = !lean_is_exclusive(v_s_1050_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1076_ = v_s_1050_;
v_isShared_1077_ = v_isSharedCheck_1095_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_nonlinearOccs_1074_);
lean_inc(v_divMod_1072_);
lean_inc(v_diseqSplits_1071_);
lean_inc(v_conflict_x3f_1070_);
lean_inc(v_numReorderRequests_1069_);
lean_inc(v_penalties_1068_);
lean_inc(v_steps_1067_);
lean_inc(v_nextCnstrId_1065_);
lean_inc(v_assignment_1064_);
lean_inc(v_occurs_1063_);
lean_inc(v_elimStack_1062_);
lean_inc(v_active_1061_);
lean_inc(v_elimEqs_1060_);
lean_inc(v_diseqs_1059_);
lean_inc(v_uppers_1058_);
lean_inc(v_lowers_1057_);
lean_inc(v_dvds_1056_);
lean_inc(v_natDef_1055_);
lean_inc(v_natToIntMap_1054_);
lean_inc(v_varsHistory_1053_);
lean_inc(v_varMap_1052_);
lean_inc(v_vars_1051_);
lean_dec(v_s_1050_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1095_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; uint8_t v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1093_; 
lean_inc_ref(v_expr_1048_);
v___x_1078_ = l_Lean_PersistentArray_push___redArg(v_vars_1051_, v_expr_1048_);
v___x_1079_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg(v_varMap_1052_, v_expr_1048_, v_size_1049_);
v___x_1080_ = lean_box(0);
v___x_1081_ = l_Lean_PersistentArray_push___redArg(v_dvds_1056_, v___x_1080_);
v___x_1082_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1);
v___x_1083_ = l_Lean_PersistentArray_push___redArg(v_lowers_1057_, v___x_1082_);
v___x_1084_ = l_Lean_PersistentArray_push___redArg(v_uppers_1058_, v___x_1082_);
v___x_1085_ = l_Lean_PersistentArray_push___redArg(v_diseqs_1059_, v___x_1082_);
v___x_1086_ = l_Lean_PersistentArray_push___redArg(v_elimEqs_1060_, v___x_1080_);
v___x_1087_ = 1;
v___x_1088_ = lean_box(v___x_1087_);
v___x_1089_ = l_Lean_PersistentArray_push___redArg(v_active_1061_, v___x_1088_);
v___x_1090_ = lean_box(1);
v___x_1091_ = l_Lean_PersistentArray_push___redArg(v_occurs_1063_, v___x_1090_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 12, v___x_1091_);
lean_ctor_set(v___x_1076_, 10, v___x_1089_);
lean_ctor_set(v___x_1076_, 9, v___x_1086_);
lean_ctor_set(v___x_1076_, 8, v___x_1085_);
lean_ctor_set(v___x_1076_, 7, v___x_1084_);
lean_ctor_set(v___x_1076_, 6, v___x_1083_);
lean_ctor_set(v___x_1076_, 5, v___x_1081_);
lean_ctor_set(v___x_1076_, 1, v___x_1079_);
lean_ctor_set(v___x_1076_, 0, v___x_1078_);
v___x_1093_ = v___x_1076_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 22, 2);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___x_1078_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v___x_1079_);
lean_ctor_set(v_reuseFailAlloc_1094_, 2, v_varsHistory_1053_);
lean_ctor_set(v_reuseFailAlloc_1094_, 3, v_natToIntMap_1054_);
lean_ctor_set(v_reuseFailAlloc_1094_, 4, v_natDef_1055_);
lean_ctor_set(v_reuseFailAlloc_1094_, 5, v___x_1081_);
lean_ctor_set(v_reuseFailAlloc_1094_, 6, v___x_1083_);
lean_ctor_set(v_reuseFailAlloc_1094_, 7, v___x_1084_);
lean_ctor_set(v_reuseFailAlloc_1094_, 8, v___x_1085_);
lean_ctor_set(v_reuseFailAlloc_1094_, 9, v___x_1086_);
lean_ctor_set(v_reuseFailAlloc_1094_, 10, v___x_1089_);
lean_ctor_set(v_reuseFailAlloc_1094_, 11, v_elimStack_1062_);
lean_ctor_set(v_reuseFailAlloc_1094_, 12, v___x_1091_);
lean_ctor_set(v_reuseFailAlloc_1094_, 13, v_assignment_1064_);
lean_ctor_set(v_reuseFailAlloc_1094_, 14, v_nextCnstrId_1065_);
lean_ctor_set(v_reuseFailAlloc_1094_, 15, v_steps_1067_);
lean_ctor_set(v_reuseFailAlloc_1094_, 16, v_penalties_1068_);
lean_ctor_set(v_reuseFailAlloc_1094_, 17, v_numReorderRequests_1069_);
lean_ctor_set(v_reuseFailAlloc_1094_, 18, v_conflict_x3f_1070_);
lean_ctor_set(v_reuseFailAlloc_1094_, 19, v_diseqSplits_1071_);
lean_ctor_set(v_reuseFailAlloc_1094_, 20, v_divMod_1072_);
lean_ctor_set(v_reuseFailAlloc_1094_, 21, v_nonlinearOccs_1074_);
lean_ctor_set_uint8(v_reuseFailAlloc_1094_, sizeof(void*)*22, v_caseSplits_1066_);
lean_ctor_set_uint8(v_reuseFailAlloc_1094_, sizeof(void*)*22 + 1, v_usedCommRing_1073_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1096_, lean_object* v_vals_1097_, lean_object* v_i_1098_, lean_object* v_k_1099_){
_start:
{
lean_object* v___x_1100_; uint8_t v___x_1101_; 
v___x_1100_ = lean_array_get_size(v_keys_1096_);
v___x_1101_ = lean_nat_dec_lt(v_i_1098_, v___x_1100_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1102_; 
lean_dec(v_i_1098_);
v___x_1102_ = lean_box(0);
return v___x_1102_;
}
else
{
lean_object* v_k_x27_1103_; size_t v___x_1104_; size_t v___x_1105_; uint8_t v___x_1106_; 
v_k_x27_1103_ = lean_array_fget_borrowed(v_keys_1096_, v_i_1098_);
v___x_1104_ = lean_ptr_addr(v_k_1099_);
v___x_1105_ = lean_ptr_addr(v_k_x27_1103_);
v___x_1106_ = lean_usize_dec_eq(v___x_1104_, v___x_1105_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = lean_unsigned_to_nat(1u);
v___x_1108_ = lean_nat_add(v_i_1098_, v___x_1107_);
lean_dec(v_i_1098_);
v_i_1098_ = v___x_1108_;
goto _start;
}
else
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = lean_array_fget_borrowed(v_vals_1097_, v_i_1098_);
lean_dec(v_i_1098_);
lean_inc(v___x_1110_);
v___x_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1110_);
return v___x_1111_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1112_, lean_object* v_vals_1113_, lean_object* v_i_1114_, lean_object* v_k_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(v_keys_1112_, v_vals_1113_, v_i_1114_, v_k_1115_);
lean_dec_ref(v_k_1115_);
lean_dec_ref(v_vals_1113_);
lean_dec_ref(v_keys_1112_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(lean_object* v_x_1117_, size_t v_x_1118_, lean_object* v_x_1119_){
_start:
{
if (lean_obj_tag(v_x_1117_) == 0)
{
lean_object* v_es_1120_; lean_object* v___x_1121_; size_t v___x_1122_; size_t v___x_1123_; lean_object* v_j_1124_; lean_object* v___x_1125_; 
v_es_1120_ = lean_ctor_get(v_x_1117_, 0);
v___x_1121_ = lean_box(2);
v___x_1122_ = ((size_t)31ULL);
v___x_1123_ = lean_usize_land(v_x_1118_, v___x_1122_);
v_j_1124_ = lean_usize_to_nat(v___x_1123_);
v___x_1125_ = lean_array_get_borrowed(v___x_1121_, v_es_1120_, v_j_1124_);
lean_dec(v_j_1124_);
switch(lean_obj_tag(v___x_1125_))
{
case 0:
{
lean_object* v_key_1126_; lean_object* v_val_1127_; size_t v___x_1128_; size_t v___x_1129_; uint8_t v___x_1130_; 
v_key_1126_ = lean_ctor_get(v___x_1125_, 0);
v_val_1127_ = lean_ctor_get(v___x_1125_, 1);
v___x_1128_ = lean_ptr_addr(v_x_1119_);
v___x_1129_ = lean_ptr_addr(v_key_1126_);
v___x_1130_ = lean_usize_dec_eq(v___x_1128_, v___x_1129_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; 
v___x_1131_ = lean_box(0);
return v___x_1131_;
}
else
{
lean_object* v___x_1132_; 
lean_inc(v_val_1127_);
v___x_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1132_, 0, v_val_1127_);
return v___x_1132_;
}
}
case 1:
{
lean_object* v_node_1133_; size_t v___x_1134_; size_t v___x_1135_; 
v_node_1133_ = lean_ctor_get(v___x_1125_, 0);
v___x_1134_ = ((size_t)5ULL);
v___x_1135_ = lean_usize_shift_right(v_x_1118_, v___x_1134_);
v_x_1117_ = v_node_1133_;
v_x_1118_ = v___x_1135_;
goto _start;
}
default: 
{
lean_object* v___x_1137_; 
v___x_1137_ = lean_box(0);
return v___x_1137_;
}
}
}
else
{
lean_object* v_ks_1138_; lean_object* v_vs_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v_ks_1138_ = lean_ctor_get(v_x_1117_, 0);
v_vs_1139_ = lean_ctor_get(v_x_1117_, 1);
v___x_1140_ = lean_unsigned_to_nat(0u);
v___x_1141_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(v_ks_1138_, v_vs_1139_, v___x_1140_, v_x_1119_);
return v___x_1141_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg___boxed(lean_object* v_x_1142_, lean_object* v_x_1143_, lean_object* v_x_1144_){
_start:
{
size_t v_x_25291__boxed_1145_; lean_object* v_res_1146_; 
v_x_25291__boxed_1145_ = lean_unbox_usize(v_x_1143_);
lean_dec(v_x_1143_);
v_res_1146_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(v_x_1142_, v_x_25291__boxed_1145_, v_x_1144_);
lean_dec_ref(v_x_1144_);
lean_dec_ref(v_x_1142_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(lean_object* v_x_1147_, lean_object* v_x_1148_){
_start:
{
size_t v___x_1149_; size_t v___x_1150_; size_t v___x_1151_; uint64_t v___x_1152_; size_t v___x_1153_; lean_object* v___x_1154_; 
v___x_1149_ = lean_ptr_addr(v_x_1148_);
v___x_1150_ = ((size_t)3ULL);
v___x_1151_ = lean_usize_shift_right(v___x_1149_, v___x_1150_);
v___x_1152_ = lean_usize_to_uint64(v___x_1151_);
v___x_1153_ = lean_uint64_to_usize(v___x_1152_);
v___x_1154_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(v_x_1147_, v___x_1153_, v_x_1148_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg___boxed(lean_object* v_x_1155_, lean_object* v_x_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(v_x_1155_, v_x_1156_);
lean_dec_ref(v_x_1156_);
lean_dec_ref(v_x_1155_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4(lean_object* v_msgData_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v___x_1164_; lean_object* v_env_1165_; uint8_t v___x_1166_; lean_object* v_env_1167_; lean_object* v___x_1168_; lean_object* v_toCold_1169_; lean_object* v_mctx_1170_; lean_object* v_lctx_1171_; lean_object* v_options_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1164_ = lean_st_ref_get(v___y_1162_);
v_env_1165_ = lean_ctor_get(v___x_1164_, 0);
lean_inc_ref(v_env_1165_);
lean_dec(v___x_1164_);
v___x_1166_ = 0;
v_env_1167_ = l_Lean_Environment_setRecordingDeps(v_env_1165_, v___x_1166_);
v___x_1168_ = lean_st_ref_get(v___y_1160_);
v_toCold_1169_ = lean_ctor_get(v___y_1161_, 0);
v_mctx_1170_ = lean_ctor_get(v___x_1168_, 0);
lean_inc_ref(v_mctx_1170_);
lean_dec(v___x_1168_);
v_lctx_1171_ = lean_ctor_get(v___y_1159_, 2);
v_options_1172_ = lean_ctor_get(v_toCold_1169_, 2);
lean_inc_ref(v_options_1172_);
lean_inc_ref(v_lctx_1171_);
v___x_1173_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1173_, 0, v_env_1167_);
lean_ctor_set(v___x_1173_, 1, v_mctx_1170_);
lean_ctor_set(v___x_1173_, 2, v_lctx_1171_);
lean_ctor_set(v___x_1173_, 3, v_options_1172_);
v___x_1174_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
lean_ctor_set(v___x_1174_, 1, v_msgData_1158_);
v___x_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4___boxed(lean_object* v_msgData_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4(v_msgData_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
return v_res_1182_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1183_; double v___x_1184_; 
v___x_1183_ = lean_unsigned_to_nat(0u);
v___x_1184_ = lean_float_of_nat(v___x_1183_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(lean_object* v_cls_1188_, lean_object* v_msg_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v_ref_1195_; lean_object* v___x_1196_; lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1242_; 
v_ref_1195_ = lean_ctor_get(v___y_1192_, 2);
v___x_1196_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4(v_msg_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
v_a_1197_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1199_ = v___x_1196_;
v_isShared_1200_ = v_isSharedCheck_1242_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1196_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1242_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1201_; lean_object* v_traceState_1202_; lean_object* v_env_1203_; lean_object* v_nextMacroScope_1204_; lean_object* v_ngen_1205_; lean_object* v_auxDeclNGen_1206_; lean_object* v_cache_1207_; lean_object* v_recordedDeps_1208_; lean_object* v_messages_1209_; lean_object* v_infoState_1210_; lean_object* v_snapshotTasks_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1241_; 
v___x_1201_ = lean_st_ref_take(v___y_1193_);
v_traceState_1202_ = lean_ctor_get(v___x_1201_, 4);
v_env_1203_ = lean_ctor_get(v___x_1201_, 0);
v_nextMacroScope_1204_ = lean_ctor_get(v___x_1201_, 1);
v_ngen_1205_ = lean_ctor_get(v___x_1201_, 2);
v_auxDeclNGen_1206_ = lean_ctor_get(v___x_1201_, 3);
v_cache_1207_ = lean_ctor_get(v___x_1201_, 5);
v_recordedDeps_1208_ = lean_ctor_get(v___x_1201_, 6);
v_messages_1209_ = lean_ctor_get(v___x_1201_, 7);
v_infoState_1210_ = lean_ctor_get(v___x_1201_, 8);
v_snapshotTasks_1211_ = lean_ctor_get(v___x_1201_, 9);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1213_ = v___x_1201_;
v_isShared_1214_ = v_isSharedCheck_1241_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_snapshotTasks_1211_);
lean_inc(v_infoState_1210_);
lean_inc(v_messages_1209_);
lean_inc(v_recordedDeps_1208_);
lean_inc(v_cache_1207_);
lean_inc(v_traceState_1202_);
lean_inc(v_auxDeclNGen_1206_);
lean_inc(v_ngen_1205_);
lean_inc(v_nextMacroScope_1204_);
lean_inc(v_env_1203_);
lean_dec(v___x_1201_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1241_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
uint64_t v_tid_1215_; lean_object* v_traces_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1240_; 
v_tid_1215_ = lean_ctor_get_uint64(v_traceState_1202_, sizeof(void*)*1);
v_traces_1216_ = lean_ctor_get(v_traceState_1202_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v_traceState_1202_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1218_ = v_traceState_1202_;
v_isShared_1219_ = v_isSharedCheck_1240_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_traces_1216_);
lean_dec(v_traceState_1202_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1240_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; double v___x_1222_; uint8_t v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1231_; 
v___x_1220_ = lean_box(0);
v___x_1221_ = lean_box(0);
v___x_1222_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0);
v___x_1223_ = 0;
v___x_1224_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__1));
v___x_1225_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1225_, 0, v_cls_1188_);
lean_ctor_set(v___x_1225_, 1, v___x_1221_);
lean_ctor_set(v___x_1225_, 2, v___x_1224_);
lean_ctor_set_float(v___x_1225_, sizeof(void*)*3, v___x_1222_);
lean_ctor_set_float(v___x_1225_, sizeof(void*)*3 + 8, v___x_1222_);
lean_ctor_set_uint8(v___x_1225_, sizeof(void*)*3 + 16, v___x_1223_);
v___x_1226_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__2));
v___x_1227_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1225_);
lean_ctor_set(v___x_1227_, 1, v_a_1197_);
lean_ctor_set(v___x_1227_, 2, v___x_1226_);
lean_inc(v_ref_1195_);
v___x_1228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1228_, 0, v_ref_1195_);
lean_ctor_set(v___x_1228_, 1, v___x_1227_);
v___x_1229_ = l_Lean_PersistentArray_push___redArg(v_traces_1216_, v___x_1228_);
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 0, v___x_1229_);
v___x_1231_ = v___x_1218_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1229_);
lean_ctor_set_uint64(v_reuseFailAlloc_1239_, sizeof(void*)*1, v_tid_1215_);
v___x_1231_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
lean_object* v___x_1233_; 
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 4, v___x_1231_);
v___x_1233_ = v___x_1213_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_env_1203_);
lean_ctor_set(v_reuseFailAlloc_1238_, 1, v_nextMacroScope_1204_);
lean_ctor_set(v_reuseFailAlloc_1238_, 2, v_ngen_1205_);
lean_ctor_set(v_reuseFailAlloc_1238_, 3, v_auxDeclNGen_1206_);
lean_ctor_set(v_reuseFailAlloc_1238_, 4, v___x_1231_);
lean_ctor_set(v_reuseFailAlloc_1238_, 5, v_cache_1207_);
lean_ctor_set(v_reuseFailAlloc_1238_, 6, v_recordedDeps_1208_);
lean_ctor_set(v_reuseFailAlloc_1238_, 7, v_messages_1209_);
lean_ctor_set(v_reuseFailAlloc_1238_, 8, v_infoState_1210_);
lean_ctor_set(v_reuseFailAlloc_1238_, 9, v_snapshotTasks_1211_);
v___x_1233_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
lean_object* v___x_1234_; lean_object* v___x_1236_; 
v___x_1234_ = lean_st_ref_put(v___y_1193_, v___x_1233_);
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 0, v___x_1220_);
v___x_1236_ = v___x_1199_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1220_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___boxed(lean_object* v_cls_1243_, lean_object* v_msg_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(v_cls_1243_, v_msg_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
return v_res_1250_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7(void){
_start:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1263_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4));
v___x_1264_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__6));
v___x_1265_ = l_Lean_Name_append(v___x_1264_, v___x_1263_);
return v___x_1265_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9(void){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1267_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__8));
v___x_1268_ = l_Lean_stringToMessageData(v___x_1267_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* lean_grind_cutsat_mk_var(lean_object* v_expr_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_){
_start:
{
uint8_t v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = 0;
v___x_1282_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1270_, v_a_1278_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; lean_object* v_varMap_1284_; lean_object* v___x_1285_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_a_1283_);
lean_dec_ref_known(v___x_1282_, 1);
v_varMap_1284_ = lean_ctor_get(v_a_1283_, 1);
lean_inc_ref(v_varMap_1284_);
lean_dec(v_a_1283_);
v___x_1285_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(v_varMap_1284_, v_expr_1269_);
lean_dec_ref(v_varMap_1284_);
if (lean_obj_tag(v___x_1285_) == 1)
{
lean_object* v_val_1286_; lean_object* v___x_1287_; 
lean_dec_ref(v_expr_1269_);
v_val_1286_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_val_1286_);
lean_dec_ref_known(v___x_1285_, 1);
v___x_1287_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1270_, v_a_1278_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1323_; 
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1290_ = v___x_1287_;
v_isShared_1291_ = v_isSharedCheck_1323_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1287_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1323_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
uint8_t v___y_1293_; lean_object* v_active_1314_; lean_object* v_size_1315_; uint8_t v___x_1316_; 
v_active_1314_ = lean_ctor_get(v_a_1288_, 10);
lean_inc_ref(v_active_1314_);
lean_dec(v_a_1288_);
v_size_1315_ = lean_ctor_get(v_active_1314_, 2);
v___x_1316_ = lean_nat_dec_lt(v_val_1286_, v_size_1315_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1317_; lean_object* v___x_1318_; uint8_t v___x_1319_; 
lean_dec_ref(v_active_1314_);
v___x_1317_ = lean_box(v___x_1281_);
v___x_1318_ = l_outOfBounds___redArg(v___x_1317_);
lean_dec(v___x_1317_);
v___x_1319_ = lean_unbox(v___x_1318_);
lean_dec(v___x_1318_);
v___y_1293_ = v___x_1319_;
goto v___jp_1292_;
}
else
{
lean_object* v___x_1320_; lean_object* v___x_1321_; uint8_t v___x_1322_; 
v___x_1320_ = lean_box(v___x_1281_);
v___x_1321_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1320_, v_active_1314_, v_val_1286_);
lean_dec_ref(v_active_1314_);
lean_dec(v___x_1320_);
v___x_1322_ = lean_unbox(v___x_1321_);
lean_dec(v___x_1321_);
v___y_1293_ = v___x_1322_;
goto v___jp_1292_;
}
v___jp_1292_:
{
if (v___y_1293_ == 0)
{
lean_object* v___x_1294_; 
lean_del_object(v___x_1290_);
lean_inc(v_val_1286_);
v___x_1294_ = lean_grind_cutsat_reactivate_var(v_val_1286_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_);
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1301_ == 0)
{
lean_object* v_unused_1302_; 
v_unused_1302_ = lean_ctor_get(v___x_1294_, 0);
lean_dec(v_unused_1302_);
v___x_1296_ = v___x_1294_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_dec(v___x_1294_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 0, v_val_1286_);
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_val_1286_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
else
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
lean_dec(v_val_1286_);
v_a_1303_ = lean_ctor_get(v___x_1294_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v___x_1294_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1294_);
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
lean_object* v___x_1312_; 
lean_dec(v_a_1279_);
lean_dec_ref(v_a_1278_);
lean_dec(v_a_1277_);
lean_dec_ref(v_a_1276_);
lean_dec(v_a_1275_);
lean_dec_ref(v_a_1274_);
lean_dec(v_a_1273_);
lean_dec_ref(v_a_1272_);
lean_dec(v_a_1271_);
lean_dec(v_a_1270_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 0, v_val_1286_);
v___x_1312_ = v___x_1290_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_val_1286_);
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
}
else
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1331_; 
lean_dec(v_val_1286_);
lean_dec(v_a_1279_);
lean_dec_ref(v_a_1278_);
lean_dec(v_a_1277_);
lean_dec_ref(v_a_1276_);
lean_dec(v_a_1275_);
lean_dec_ref(v_a_1274_);
lean_dec(v_a_1273_);
lean_dec_ref(v_a_1272_);
lean_dec(v_a_1271_);
lean_dec(v_a_1270_);
v_a_1324_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1326_ = v___x_1287_;
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1287_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1324_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
else
{
lean_object* v___x_1332_; 
lean_dec(v___x_1285_);
v___x_1332_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1270_, v_a_1278_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_a_1333_; lean_object* v_vars_1334_; lean_object* v_toCold_1335_; lean_object* v_options_1336_; lean_object* v_size_1337_; lean_object* v_inheritedTraceOptions_1338_; uint8_t v_hasTrace_1339_; lean_object* v___f_1340_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1351_; 
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_a_1333_);
lean_dec_ref_known(v___x_1332_, 1);
v_vars_1334_ = lean_ctor_get(v_a_1333_, 0);
lean_inc_ref(v_vars_1334_);
lean_dec(v_a_1333_);
v_toCold_1335_ = lean_ctor_get(v_a_1278_, 0);
v_options_1336_ = lean_ctor_get(v_toCold_1335_, 2);
v_size_1337_ = lean_ctor_get(v_vars_1334_, 2);
lean_inc_n(v_size_1337_, 2);
lean_dec_ref(v_vars_1334_);
v_inheritedTraceOptions_1338_ = lean_ctor_get(v_toCold_1335_, 11);
v_hasTrace_1339_ = lean_ctor_get_uint8(v_options_1336_, sizeof(void*)*1);
lean_inc_ref(v_expr_1269_);
v___f_1340_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0), 3, 2);
lean_closure_set(v___f_1340_, 0, v_expr_1269_);
lean_closure_set(v___f_1340_, 1, v_size_1337_);
if (v_hasTrace_1339_ == 0)
{
v___y_1342_ = v_a_1270_;
v___y_1343_ = v_a_1271_;
v___y_1344_ = v_a_1272_;
v___y_1345_ = v_a_1273_;
v___y_1346_ = v_a_1274_;
v___y_1347_ = v_a_1275_;
v___y_1348_ = v_a_1276_;
v___y_1349_ = v_a_1277_;
v___y_1350_ = v_a_1278_;
v___y_1351_ = v_a_1279_;
goto v___jp_1341_;
}
else
{
lean_object* v___x_1388_; lean_object* v___x_1389_; uint8_t v___x_1390_; 
v___x_1388_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4));
v___x_1389_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7);
v___x_1390_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1338_, v_options_1336_, v___x_1389_);
if (v___x_1390_ == 0)
{
v___y_1342_ = v_a_1270_;
v___y_1343_ = v_a_1271_;
v___y_1344_ = v_a_1272_;
v___y_1345_ = v_a_1273_;
v___y_1346_ = v_a_1274_;
v___y_1347_ = v_a_1275_;
v___y_1348_ = v_a_1276_;
v___y_1349_ = v_a_1277_;
v___y_1350_ = v_a_1278_;
v___y_1351_ = v_a_1279_;
goto v___jp_1341_;
}
else
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
lean_inc_ref(v_expr_1269_);
v___x_1391_ = l_Lean_MessageData_ofExpr(v_expr_1269_);
v___x_1392_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9);
v___x_1393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1391_);
lean_ctor_set(v___x_1393_, 1, v___x_1392_);
lean_inc(v_size_1337_);
v___x_1394_ = l_Nat_reprFast(v_size_1337_);
v___x_1395_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1394_);
v___x_1396_ = l_Lean_MessageData_ofFormat(v___x_1395_);
v___x_1397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1393_);
lean_ctor_set(v___x_1397_, 1, v___x_1396_);
v___x_1398_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(v___x_1388_, v___x_1397_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_dec_ref_known(v___x_1398_, 1);
v___y_1342_ = v_a_1270_;
v___y_1343_ = v_a_1271_;
v___y_1344_ = v_a_1272_;
v___y_1345_ = v_a_1273_;
v___y_1346_ = v_a_1274_;
v___y_1347_ = v_a_1275_;
v___y_1348_ = v_a_1276_;
v___y_1349_ = v_a_1277_;
v___y_1350_ = v_a_1278_;
v___y_1351_ = v_a_1279_;
goto v___jp_1341_;
}
else
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1406_; 
lean_dec_ref(v___f_1340_);
lean_dec(v_size_1337_);
lean_dec(v_a_1279_);
lean_dec_ref(v_a_1278_);
lean_dec(v_a_1277_);
lean_dec_ref(v_a_1276_);
lean_dec(v_a_1275_);
lean_dec_ref(v_a_1274_);
lean_dec(v_a_1273_);
lean_dec_ref(v_a_1272_);
lean_dec(v_a_1271_);
lean_dec(v_a_1270_);
lean_dec_ref(v_expr_1269_);
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1401_ = v___x_1398_;
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1398_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1402_ == 0)
{
v___x_1404_ = v___x_1401_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1399_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
}
v___jp_1341_:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1352_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_1353_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1352_, v___f_1340_, v___y_1342_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v___x_1354_; 
lean_dec_ref_known(v___x_1353_, 1);
lean_inc_ref(v_expr_1269_);
v___x_1354_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_1352_, v_expr_1269_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v___x_1355_; 
lean_dec_ref_known(v___x_1354_, 1);
lean_inc(v_size_1337_);
v___x_1355_ = l_Lean_Meta_Grind_Arith_Cutsat_assertVarFacts(v_expr_1269_, v_size_1337_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v___y_1343_);
lean_dec(v___y_1342_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1362_ == 0)
{
lean_object* v_unused_1363_; 
v_unused_1363_ = lean_ctor_get(v___x_1355_, 0);
lean_dec(v_unused_1363_);
v___x_1357_ = v___x_1355_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_dec(v___x_1355_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 0, v_size_1337_);
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_size_1337_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
else
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
lean_dec(v_size_1337_);
v_a_1364_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___x_1355_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1355_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
else
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec(v_size_1337_);
lean_dec_ref(v_expr_1269_);
v_a_1372_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1374_ = v___x_1354_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1354_);
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
else
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1387_; 
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec(v_size_1337_);
lean_dec_ref(v_expr_1269_);
v_a_1380_ = lean_ctor_get(v___x_1353_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1382_ = v___x_1353_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1353_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1380_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1414_; 
lean_dec(v_a_1279_);
lean_dec_ref(v_a_1278_);
lean_dec(v_a_1277_);
lean_dec_ref(v_a_1276_);
lean_dec(v_a_1275_);
lean_dec_ref(v_a_1274_);
lean_dec(v_a_1273_);
lean_dec_ref(v_a_1272_);
lean_dec(v_a_1271_);
lean_dec(v_a_1270_);
lean_dec_ref(v_expr_1269_);
v_a_1407_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1409_ = v___x_1332_;
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1332_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1412_; 
if (v_isShared_1410_ == 0)
{
v___x_1412_ = v___x_1409_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1407_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
}
else
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
lean_dec(v_a_1279_);
lean_dec_ref(v_a_1278_);
lean_dec(v_a_1277_);
lean_dec_ref(v_a_1276_);
lean_dec(v_a_1275_);
lean_dec_ref(v_a_1274_);
lean_dec(v_a_1273_);
lean_dec_ref(v_a_1272_);
lean_dec(v_a_1271_);
lean_dec(v_a_1270_);
lean_dec_ref(v_expr_1269_);
v_a_1415_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1417_ = v___x_1282_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1282_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1420_; 
if (v_isShared_1418_ == 0)
{
v___x_1420_ = v___x_1417_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1415_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___boxed(lean_object* v_expr_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = lean_grind_cutsat_mk_var(v_expr_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0(lean_object* v_00_u03b2_1436_, lean_object* v_x_1437_, lean_object* v_x_1438_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(v_x_1437_, v_x_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___boxed(lean_object* v_00_u03b2_1440_, lean_object* v_x_1441_, lean_object* v_x_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0(v_00_u03b2_1440_, v_x_1441_, v_x_1442_);
lean_dec_ref(v_x_1442_);
lean_dec_ref(v_x_1441_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1(lean_object* v_00_u03b2_1444_, lean_object* v_x_1445_, lean_object* v_x_1446_, lean_object* v_x_1447_){
_start:
{
lean_object* v___x_1448_; 
v___x_1448_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg(v_x_1445_, v_x_1446_, v_x_1447_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2(lean_object* v_cls_1449_, lean_object* v_msg_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(v_cls_1449_, v_msg_1450_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___boxed(lean_object* v_cls_1463_, lean_object* v_msg_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2(v_cls_1463_, v_msg_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec(v___y_1465_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0(lean_object* v_00_u03b2_1477_, lean_object* v_x_1478_, size_t v_x_1479_, lean_object* v_x_1480_){
_start:
{
lean_object* v___x_1481_; 
v___x_1481_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(v_x_1478_, v_x_1479_, v_x_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1482_, lean_object* v_x_1483_, lean_object* v_x_1484_, lean_object* v_x_1485_){
_start:
{
size_t v_x_25867__boxed_1486_; lean_object* v_res_1487_; 
v_x_25867__boxed_1486_ = lean_unbox_usize(v_x_1484_);
lean_dec(v_x_1484_);
v_res_1487_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0(v_00_u03b2_1482_, v_x_1483_, v_x_25867__boxed_1486_, v_x_1485_);
lean_dec_ref(v_x_1485_);
lean_dec_ref(v_x_1483_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2(lean_object* v_00_u03b2_1488_, lean_object* v_x_1489_, size_t v_x_1490_, size_t v_x_1491_, lean_object* v_x_1492_, lean_object* v_x_1493_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_x_1489_, v_x_1490_, v_x_1491_, v_x_1492_, v_x_1493_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1495_, lean_object* v_x_1496_, lean_object* v_x_1497_, lean_object* v_x_1498_, lean_object* v_x_1499_, lean_object* v_x_1500_){
_start:
{
size_t v_x_25878__boxed_1501_; size_t v_x_25879__boxed_1502_; lean_object* v_res_1503_; 
v_x_25878__boxed_1501_ = lean_unbox_usize(v_x_1497_);
lean_dec(v_x_1497_);
v_x_25879__boxed_1502_ = lean_unbox_usize(v_x_1498_);
lean_dec(v_x_1498_);
v_res_1503_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2(v_00_u03b2_1495_, v_x_1496_, v_x_25878__boxed_1501_, v_x_25879__boxed_1502_, v_x_1499_, v_x_1500_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1504_, lean_object* v_keys_1505_, lean_object* v_vals_1506_, lean_object* v_heq_1507_, lean_object* v_i_1508_, lean_object* v_k_1509_){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(v_keys_1505_, v_vals_1506_, v_i_1508_, v_k_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1511_, lean_object* v_keys_1512_, lean_object* v_vals_1513_, lean_object* v_heq_1514_, lean_object* v_i_1515_, lean_object* v_k_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1(v_00_u03b2_1511_, v_keys_1512_, v_vals_1513_, v_heq_1514_, v_i_1515_, v_k_1516_);
lean_dec_ref(v_k_1516_);
lean_dec_ref(v_vals_1513_);
lean_dec_ref(v_keys_1512_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1518_, lean_object* v_n_1519_, lean_object* v_k_1520_, lean_object* v_v_1521_){
_start:
{
lean_object* v___x_1522_; 
v___x_1522_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4___redArg(v_n_1519_, v_k_1520_, v_v_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1523_, size_t v_depth_1524_, lean_object* v_keys_1525_, lean_object* v_vals_1526_, lean_object* v_heq_1527_, lean_object* v_i_1528_, lean_object* v_entries_1529_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(v_depth_1524_, v_keys_1525_, v_vals_1526_, v_i_1528_, v_entries_1529_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1531_, lean_object* v_depth_1532_, lean_object* v_keys_1533_, lean_object* v_vals_1534_, lean_object* v_heq_1535_, lean_object* v_i_1536_, lean_object* v_entries_1537_){
_start:
{
size_t v_depth_boxed_1538_; lean_object* v_res_1539_; 
v_depth_boxed_1538_ = lean_unbox_usize(v_depth_1532_);
lean_dec(v_depth_1532_);
v_res_1539_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5(v_00_u03b2_1531_, v_depth_boxed_1538_, v_keys_1533_, v_vals_1534_, v_heq_1535_, v_i_1536_, v_entries_1537_);
lean_dec_ref(v_vals_1534_);
lean_dec_ref(v_keys_1533_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_1540_, lean_object* v_x_1541_, lean_object* v_x_1542_, lean_object* v_x_1543_, lean_object* v_x_1544_){
_start:
{
lean_object* v___x_1545_; 
v___x_1545_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7___redArg(v_x_1541_, v_x_1542_, v_x_1543_, v_x_1544_);
return v___x_1545_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2(void){
_start:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1549_ = lean_box(0);
v___x_1550_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__1));
v___x_1551_ = l_Lean_mkConst(v___x_1550_, v___x_1549_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(lean_object* v_e_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_){
_start:
{
lean_object* v___x_1558_; 
lean_inc(v_a_1556_);
lean_inc_ref(v_a_1555_);
lean_inc(v_a_1554_);
lean_inc_ref(v_a_1553_);
v___x_1558_ = lean_infer_type(v_e_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_a_1559_);
lean_dec_ref_known(v___x_1558_, 1);
v___x_1560_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2);
v___x_1561_ = l_Lean_Meta_isExprDefEq(v_a_1559_, v___x_1560_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_);
return v___x_1561_;
}
else
{
lean_object* v_a_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1569_; 
v_a_1562_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1564_ = v___x_1558_;
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_a_1562_);
lean_dec(v___x_1558_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1567_; 
if (v_isShared_1565_ == 0)
{
v___x_1567_ = v___x_1564_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_a_1562_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___boxed(lean_object* v_e_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_){
_start:
{
lean_object* v_res_1576_; 
v_res_1576_ = l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(v_e_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_);
lean_dec(v_a_1574_);
lean_dec_ref(v_a_1573_);
lean_dec(v_a_1572_);
lean_dec_ref(v_a_1571_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt(lean_object* v_e_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(v_e_1577_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___boxed(lean_object* v_e_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l_Lean_Meta_Grind_Arith_Cutsat_isInt(v_e_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_);
lean_dec(v_a_1600_);
lean_dec_ref(v_a_1599_);
lean_dec(v_a_1598_);
lean_dec_ref(v_a_1597_);
lean_dec(v_a_1596_);
lean_dec_ref(v_a_1595_);
lean_dec(v_a_1594_);
lean_dec_ref(v_a_1593_);
lean_dec(v_a_1592_);
lean_dec(v_a_1591_);
return v_res_1602_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4(void){
_start:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1609_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__3));
v___x_1610_ = l_Lean_stringToMessageData(v___x_1609_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(lean_object* v_e_1611_, uint8_t v_report_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_){
_start:
{
lean_object* v___x_1626_; 
lean_inc_ref(v_e_1611_);
v___x_1626_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1611_, v_a_1616_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v_a_1627_; lean_object* v___x_1628_; uint8_t v___x_1629_; 
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_a_1627_);
lean_dec_ref_known(v___x_1626_, 1);
v___x_1628_ = l_Lean_Expr_cleanupAnnotations(v_a_1627_);
lean_dec(v_a_1627_);
v___x_1629_ = l_Lean_Expr_isApp(v___x_1628_);
if (v___x_1629_ == 0)
{
lean_dec_ref(v___x_1628_);
lean_dec_ref(v_e_1611_);
goto v___jp_1620_;
}
else
{
lean_object* v___x_1630_; uint8_t v___x_1631_; 
v___x_1630_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1628_);
v___x_1631_ = l_Lean_Expr_isApp(v___x_1630_);
if (v___x_1631_ == 0)
{
lean_dec_ref(v___x_1630_);
lean_dec_ref(v___x_1628_);
lean_dec_ref(v_e_1611_);
goto v___jp_1620_;
}
else
{
lean_object* v___x_1632_; uint8_t v___x_1633_; 
v___x_1632_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1630_);
v___x_1633_ = l_Lean_Expr_isApp(v___x_1632_);
if (v___x_1633_ == 0)
{
lean_dec_ref(v___x_1632_);
lean_dec_ref(v___x_1630_);
lean_dec_ref(v___x_1628_);
lean_dec_ref(v_e_1611_);
goto v___jp_1620_;
}
else
{
lean_object* v___x_1634_; uint8_t v___x_1635_; 
v___x_1634_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1632_);
v___x_1635_ = l_Lean_Expr_isApp(v___x_1634_);
if (v___x_1635_ == 0)
{
lean_dec_ref(v___x_1634_);
lean_dec_ref(v___x_1632_);
lean_dec_ref(v___x_1630_);
lean_dec_ref(v___x_1628_);
lean_dec_ref(v_e_1611_);
goto v___jp_1620_;
}
else
{
lean_object* v___x_1636_; uint8_t v___x_1637_; 
v___x_1636_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1634_);
lean_dec_ref(v___x_1634_);
v___x_1637_ = l_Lean_Expr_isApp(v___x_1636_);
if (v___x_1637_ == 0)
{
lean_dec_ref(v___x_1636_);
lean_dec_ref(v___x_1632_);
lean_dec_ref(v___x_1630_);
lean_dec_ref(v___x_1628_);
lean_dec_ref(v_e_1611_);
goto v___jp_1620_;
}
else
{
lean_object* v___x_1638_; uint8_t v___x_1639_; 
v___x_1638_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1636_);
lean_dec_ref(v___x_1636_);
v___x_1639_ = l_Lean_Expr_isApp(v___x_1638_);
if (v___x_1639_ == 0)
{
lean_dec_ref(v___x_1638_);
lean_dec_ref(v___x_1632_);
lean_dec_ref(v___x_1630_);
lean_dec_ref(v___x_1628_);
lean_dec_ref(v_e_1611_);
goto v___jp_1620_;
}
else
{
lean_object* v___x_1640_; lean_object* v___x_1641_; uint8_t v___x_1642_; 
v___x_1640_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1638_);
lean_dec_ref(v___x_1638_);
v___x_1641_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__2));
v___x_1642_ = l_Lean_Expr_isConstOf(v___x_1640_, v___x_1641_);
lean_dec_ref(v___x_1640_);
if (v___x_1642_ == 0)
{
lean_dec_ref(v___x_1632_);
lean_dec_ref(v___x_1630_);
lean_dec_ref(v___x_1628_);
lean_dec_ref(v_e_1611_);
goto v___jp_1620_;
}
else
{
lean_object* v_arg_1643_; lean_object* v_arg_1644_; lean_object* v_arg_1645_; lean_object* v___x_1646_; 
v_arg_1643_ = lean_ctor_get(v___x_1628_, 1);
lean_inc_ref(v_arg_1643_);
lean_dec_ref(v___x_1628_);
v_arg_1644_ = lean_ctor_get(v___x_1630_, 1);
lean_inc_ref(v_arg_1644_);
lean_dec_ref(v___x_1630_);
v_arg_1645_ = lean_ctor_get(v___x_1632_, 1);
lean_inc_ref(v_arg_1645_);
lean_dec_ref(v___x_1632_);
v___x_1646_ = l_Lean_Meta_Structural_isInstHAddInt___redArg(v_arg_1645_, v_a_1616_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1680_; 
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1649_ = v___x_1646_;
v_isShared_1650_ = v_isSharedCheck_1680_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v___x_1646_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1680_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
uint8_t v___x_1651_; 
v___x_1651_ = lean_unbox(v_a_1647_);
lean_dec(v_a_1647_);
if (v___x_1651_ == 0)
{
lean_del_object(v___x_1649_);
lean_dec_ref(v_arg_1644_);
lean_dec_ref(v_arg_1643_);
if (v_report_1612_ == 0)
{
lean_dec_ref(v_e_1611_);
goto v___jp_1623_;
}
else
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1652_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4);
v___x_1653_ = l_Lean_indentExpr(v_e_1611_);
v___x_1654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1652_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
v___x_1655_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1613_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; uint8_t v_verbose_1657_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
lean_inc(v_a_1656_);
lean_dec_ref_known(v___x_1655_, 1);
v_verbose_1657_ = lean_ctor_get_uint8(v_a_1656_, 0);
lean_dec(v_a_1656_);
if (v_verbose_1657_ == 0)
{
lean_dec_ref_known(v___x_1654_, 2);
goto v___jp_1623_;
}
else
{
lean_object* v___x_1658_; 
v___x_1658_ = l_Lean_Meta_Sym_reportIssue(v___x_1654_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_dec_ref_known(v___x_1658_, 1);
goto v___jp_1623_;
}
else
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1666_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1661_ = v___x_1658_;
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1658_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
if (v_isShared_1662_ == 0)
{
v___x_1664_ = v___x_1661_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_a_1659_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
}
else
{
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1674_; 
lean_dec_ref_known(v___x_1654_, 2);
v_a_1667_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1674_ == 0)
{
v___x_1669_ = v___x_1655_;
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___x_1655_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1674_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1672_; 
if (v_isShared_1670_ == 0)
{
v___x_1672_ = v___x_1669_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_a_1667_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
}
else
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1678_; 
lean_dec_ref(v_e_1611_);
v___x_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1675_, 0, v_arg_1644_);
lean_ctor_set(v___x_1675_, 1, v_arg_1643_);
v___x_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1675_);
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 0, v___x_1676_);
v___x_1678_ = v___x_1649_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v___x_1676_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
}
else
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
lean_dec_ref(v_arg_1644_);
lean_dec_ref(v_arg_1643_);
lean_dec_ref(v_e_1611_);
v_a_1681_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1683_ = v___x_1646_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1646_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1684_ == 0)
{
v___x_1686_ = v___x_1683_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_a_1681_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
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
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
lean_dec_ref(v_e_1611_);
v_a_1689_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1691_ = v___x_1626_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1626_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1692_ == 0)
{
v___x_1694_ = v___x_1691_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_a_1689_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
v___jp_1620_:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1621_ = lean_box(0);
v___x_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1621_);
return v___x_1622_;
}
v___jp_1623_:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1624_ = lean_box(0);
v___x_1625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
return v___x_1625_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___boxed(lean_object* v_e_1697_, lean_object* v_report_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_){
_start:
{
uint8_t v_report_boxed_1706_; lean_object* v_res_1707_; 
v_report_boxed_1706_ = lean_unbox(v_report_1698_);
v_res_1707_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_1697_, v_report_boxed_1706_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
lean_dec(v_a_1704_);
lean_dec_ref(v_a_1703_);
lean_dec(v_a_1702_);
lean_dec_ref(v_a_1701_);
lean_dec(v_a_1700_);
lean_dec_ref(v_a_1699_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f(lean_object* v_e_1708_, uint8_t v_report_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_){
_start:
{
lean_object* v___x_1721_; 
v___x_1721_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_1708_, v_report_1709_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___boxed(lean_object* v_e_1722_, lean_object* v_report_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_){
_start:
{
uint8_t v_report_boxed_1735_; lean_object* v_res_1736_; 
v_report_boxed_1735_ = lean_unbox(v_report_1723_);
v_res_1736_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f(v_e_1722_, v_report_boxed_1735_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_);
lean_dec(v_a_1733_);
lean_dec_ref(v_a_1732_);
lean_dec(v_a_1731_);
lean_dec_ref(v_a_1730_);
lean_dec(v_a_1729_);
lean_dec_ref(v_a_1728_);
lean_dec(v_a_1727_);
lean_dec_ref(v_a_1726_);
lean_dec(v_a_1725_);
lean_dec(v_a_1724_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(lean_object* v_e_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_){
_start:
{
uint8_t v___x_1745_; lean_object* v___x_1746_; 
v___x_1745_ = 0;
v___x_1746_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_1737_, v___x_1745_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1760_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1749_ = v___x_1746_;
v_isShared_1750_ = v_isSharedCheck_1760_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1746_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1760_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
if (lean_obj_tag(v_a_1747_) == 0)
{
lean_object* v___x_1751_; lean_object* v___x_1753_; 
v___x_1751_ = lean_box(v___x_1745_);
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 0, v___x_1751_);
v___x_1753_ = v___x_1749_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v___x_1751_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
else
{
uint8_t v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1758_; 
lean_dec_ref_known(v_a_1747_, 1);
v___x_1755_ = 1;
v___x_1756_ = lean_box(v___x_1755_);
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 0, v___x_1756_);
v___x_1758_ = v___x_1749_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1756_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
v_a_1761_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1746_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1746_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg___boxed(lean_object* v_e_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(v_e_1769_, v_a_1770_, v_a_1771_, v_a_1772_, v_a_1773_, v_a_1774_, v_a_1775_);
lean_dec(v_a_1775_);
lean_dec_ref(v_a_1774_);
lean_dec(v_a_1773_);
lean_dec_ref(v_a_1772_);
lean_dec(v_a_1771_);
lean_dec_ref(v_a_1770_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd(lean_object* v_e_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v___x_1790_; 
v___x_1790_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(v_e_1778_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___boxed(lean_object* v_e_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd(v_e_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_);
lean_dec(v_a_1801_);
lean_dec_ref(v_a_1800_);
lean_dec(v_a_1799_);
lean_dec_ref(v_a_1798_);
lean_dec(v_a_1797_);
lean_dec_ref(v_a_1796_);
lean_dec(v_a_1795_);
lean_dec_ref(v_a_1794_);
lean_dec(v_a_1793_);
lean_dec(v_a_1792_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(lean_object* v_e_1804_, uint8_t v_report_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_){
_start:
{
lean_object* v___x_1819_; 
lean_inc_ref(v_e_1804_);
v___x_1819_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1804_, v_a_1809_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_a_1820_; lean_object* v___x_1821_; uint8_t v___x_1822_; 
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_a_1820_);
lean_dec_ref_known(v___x_1819_, 1);
v___x_1821_ = l_Lean_Expr_cleanupAnnotations(v_a_1820_);
lean_dec(v_a_1820_);
v___x_1822_ = l_Lean_Expr_isApp(v___x_1821_);
if (v___x_1822_ == 0)
{
lean_dec_ref(v___x_1821_);
lean_dec_ref(v_e_1804_);
goto v___jp_1813_;
}
else
{
lean_object* v___x_1823_; uint8_t v___x_1824_; 
v___x_1823_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1821_);
v___x_1824_ = l_Lean_Expr_isApp(v___x_1823_);
if (v___x_1824_ == 0)
{
lean_dec_ref(v___x_1823_);
lean_dec_ref(v___x_1821_);
lean_dec_ref(v_e_1804_);
goto v___jp_1813_;
}
else
{
lean_object* v___x_1825_; uint8_t v___x_1826_; 
v___x_1825_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1823_);
v___x_1826_ = l_Lean_Expr_isApp(v___x_1825_);
if (v___x_1826_ == 0)
{
lean_dec_ref(v___x_1825_);
lean_dec_ref(v___x_1823_);
lean_dec_ref(v___x_1821_);
lean_dec_ref(v_e_1804_);
goto v___jp_1813_;
}
else
{
lean_object* v___x_1827_; uint8_t v___x_1828_; 
v___x_1827_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1825_);
v___x_1828_ = l_Lean_Expr_isApp(v___x_1827_);
if (v___x_1828_ == 0)
{
lean_dec_ref(v___x_1827_);
lean_dec_ref(v___x_1825_);
lean_dec_ref(v___x_1823_);
lean_dec_ref(v___x_1821_);
lean_dec_ref(v_e_1804_);
goto v___jp_1813_;
}
else
{
lean_object* v___x_1829_; uint8_t v___x_1830_; 
v___x_1829_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1827_);
lean_dec_ref(v___x_1827_);
v___x_1830_ = l_Lean_Expr_isApp(v___x_1829_);
if (v___x_1830_ == 0)
{
lean_dec_ref(v___x_1829_);
lean_dec_ref(v___x_1825_);
lean_dec_ref(v___x_1823_);
lean_dec_ref(v___x_1821_);
lean_dec_ref(v_e_1804_);
goto v___jp_1813_;
}
else
{
lean_object* v___x_1831_; uint8_t v___x_1832_; 
v___x_1831_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1829_);
lean_dec_ref(v___x_1829_);
v___x_1832_ = l_Lean_Expr_isApp(v___x_1831_);
if (v___x_1832_ == 0)
{
lean_dec_ref(v___x_1831_);
lean_dec_ref(v___x_1825_);
lean_dec_ref(v___x_1823_);
lean_dec_ref(v___x_1821_);
lean_dec_ref(v_e_1804_);
goto v___jp_1813_;
}
else
{
lean_object* v___x_1833_; lean_object* v___x_1834_; uint8_t v___x_1835_; 
v___x_1833_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1831_);
lean_dec_ref(v___x_1831_);
v___x_1834_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11));
v___x_1835_ = l_Lean_Expr_isConstOf(v___x_1833_, v___x_1834_);
lean_dec_ref(v___x_1833_);
if (v___x_1835_ == 0)
{
lean_dec_ref(v___x_1825_);
lean_dec_ref(v___x_1823_);
lean_dec_ref(v___x_1821_);
lean_dec_ref(v_e_1804_);
goto v___jp_1813_;
}
else
{
lean_object* v_arg_1836_; lean_object* v_arg_1837_; lean_object* v_arg_1838_; lean_object* v___x_1839_; 
v_arg_1836_ = lean_ctor_get(v___x_1821_, 1);
lean_inc_ref(v_arg_1836_);
lean_dec_ref(v___x_1821_);
v_arg_1837_ = lean_ctor_get(v___x_1823_, 1);
lean_inc_ref(v_arg_1837_);
lean_dec_ref(v___x_1823_);
v_arg_1838_ = lean_ctor_get(v___x_1825_, 1);
lean_inc_ref(v_arg_1838_);
lean_dec_ref(v___x_1825_);
v___x_1839_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_1838_, v_a_1809_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v_a_1840_; uint8_t v___x_1841_; 
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
lean_inc(v_a_1840_);
lean_dec_ref_known(v___x_1839_, 1);
v___x_1841_ = lean_unbox(v_a_1840_);
lean_dec(v_a_1840_);
if (v___x_1841_ == 0)
{
lean_dec_ref(v_arg_1837_);
lean_dec_ref(v_arg_1836_);
if (v_report_1805_ == 0)
{
lean_dec_ref(v_e_1804_);
goto v___jp_1816_;
}
else
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1842_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4);
v___x_1843_ = l_Lean_indentExpr(v_e_1804_);
v___x_1844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1842_);
lean_ctor_set(v___x_1844_, 1, v___x_1843_);
v___x_1845_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1806_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; uint8_t v_verbose_1847_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
lean_inc(v_a_1846_);
lean_dec_ref_known(v___x_1845_, 1);
v_verbose_1847_ = lean_ctor_get_uint8(v_a_1846_, 0);
lean_dec(v_a_1846_);
if (v_verbose_1847_ == 0)
{
lean_dec_ref_known(v___x_1844_, 2);
goto v___jp_1816_;
}
else
{
lean_object* v___x_1848_; 
v___x_1848_ = l_Lean_Meta_Sym_reportIssue(v___x_1844_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_dec_ref_known(v___x_1848_, 1);
goto v___jp_1816_;
}
else
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1848_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1848_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
if (v_isShared_1852_ == 0)
{
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_a_1849_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
}
else
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
lean_dec_ref_known(v___x_1844_, 2);
v_a_1857_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1845_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1845_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_a_1857_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
}
else
{
lean_object* v___x_1865_; 
lean_dec_ref(v_e_1804_);
v___x_1865_ = l_Lean_Meta_getIntValue_x3f(v_arg_1837_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1886_; 
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1868_ = v___x_1865_;
v_isShared_1869_ = v_isSharedCheck_1886_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1865_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1886_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
if (lean_obj_tag(v_a_1866_) == 1)
{
lean_object* v_val_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1881_; 
v_val_1870_ = lean_ctor_get(v_a_1866_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v_a_1866_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1872_ = v_a_1866_;
v_isShared_1873_ = v_isSharedCheck_1881_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_val_1870_);
lean_dec(v_a_1866_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1881_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1874_; lean_object* v___x_1876_; 
v___x_1874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1874_, 0, v_val_1870_);
lean_ctor_set(v___x_1874_, 1, v_arg_1836_);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 0, v___x_1874_);
v___x_1876_ = v___x_1872_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1874_);
v___x_1876_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
lean_object* v___x_1878_; 
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 0, v___x_1876_);
v___x_1878_ = v___x_1868_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1876_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
else
{
lean_object* v___x_1882_; lean_object* v___x_1884_; 
lean_dec(v_a_1866_);
lean_dec_ref(v_arg_1836_);
v___x_1882_ = lean_box(0);
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 0, v___x_1882_);
v___x_1884_ = v___x_1868_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1882_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
}
else
{
lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1894_; 
lean_dec_ref(v_arg_1836_);
v_a_1887_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1889_ = v___x_1865_;
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_dec(v___x_1865_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1894_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1892_; 
if (v_isShared_1890_ == 0)
{
v___x_1892_ = v___x_1889_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_a_1887_);
v___x_1892_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
return v___x_1892_;
}
}
}
}
}
else
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1902_; 
lean_dec_ref(v_arg_1837_);
lean_dec_ref(v_arg_1836_);
lean_dec_ref(v_e_1804_);
v_a_1895_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1897_ = v___x_1839_;
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1839_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1900_; 
if (v_isShared_1898_ == 0)
{
v___x_1900_ = v___x_1897_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_a_1895_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
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
lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1910_; 
lean_dec_ref(v_e_1804_);
v_a_1903_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1905_ = v___x_1819_;
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___x_1819_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1908_; 
if (v_isShared_1906_ == 0)
{
v___x_1908_ = v___x_1905_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1903_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
v___jp_1813_:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1814_ = lean_box(0);
v___x_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1814_);
return v___x_1815_;
}
v___jp_1816_:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1817_ = lean_box(0);
v___x_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1817_);
return v___x_1818_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg___boxed(lean_object* v_e_1911_, lean_object* v_report_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_){
_start:
{
uint8_t v_report_boxed_1920_; lean_object* v_res_1921_; 
v_report_boxed_1920_ = lean_unbox(v_report_1912_);
v_res_1921_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1911_, v_report_boxed_1920_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
lean_dec(v_a_1918_);
lean_dec_ref(v_a_1917_);
lean_dec(v_a_1916_);
lean_dec_ref(v_a_1915_);
lean_dec(v_a_1914_);
lean_dec_ref(v_a_1913_);
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f(lean_object* v_e_1922_, uint8_t v_report_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_){
_start:
{
lean_object* v___x_1935_; 
v___x_1935_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1922_, v_report_1923_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___boxed(lean_object* v_e_1936_, lean_object* v_report_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_){
_start:
{
uint8_t v_report_boxed_1949_; lean_object* v_res_1950_; 
v_report_boxed_1949_ = lean_unbox(v_report_1937_);
v_res_1950_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f(v_e_1936_, v_report_boxed_1949_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_);
lean_dec(v_a_1947_);
lean_dec_ref(v_a_1946_);
lean_dec(v_a_1945_);
lean_dec_ref(v_a_1944_);
lean_dec(v_a_1943_);
lean_dec_ref(v_a_1942_);
lean_dec(v_a_1941_);
lean_dec_ref(v_a_1940_);
lean_dec(v_a_1939_);
lean_dec(v_a_1938_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(lean_object* v_e_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_){
_start:
{
uint8_t v___x_1959_; lean_object* v___x_1960_; 
v___x_1959_ = 0;
v___x_1960_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1951_, v___x_1959_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1974_; 
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1963_ = v___x_1960_;
v_isShared_1964_ = v_isSharedCheck_1974_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1960_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1974_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
if (lean_obj_tag(v_a_1961_) == 0)
{
lean_object* v___x_1965_; lean_object* v___x_1967_; 
v___x_1965_ = lean_box(v___x_1959_);
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 0, v___x_1965_);
v___x_1967_ = v___x_1963_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v___x_1965_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
else
{
uint8_t v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1972_; 
lean_dec_ref_known(v_a_1961_, 1);
v___x_1969_ = 1;
v___x_1970_ = lean_box(v___x_1969_);
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 0, v___x_1970_);
v___x_1972_ = v___x_1963_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1970_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
else
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
v_a_1975_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1977_ = v___x_1960_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1960_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1975_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg___boxed(lean_object* v_e_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_){
_start:
{
lean_object* v_res_1991_; 
v_res_1991_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(v_e_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_);
lean_dec(v_a_1989_);
lean_dec_ref(v_a_1988_);
lean_dec(v_a_1987_);
lean_dec_ref(v_a_1986_);
lean_dec(v_a_1985_);
lean_dec_ref(v_a_1984_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul(lean_object* v_e_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_){
_start:
{
lean_object* v___x_2004_; 
v___x_2004_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(v_e_1992_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_);
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___boxed(lean_object* v_e_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul(v_e_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_);
lean_dec(v_a_2015_);
lean_dec_ref(v_a_2014_);
lean_dec(v_a_2013_);
lean_dec_ref(v_a_2012_);
lean_dec(v_a_2011_);
lean_dec_ref(v_a_2010_);
lean_dec(v_a_2009_);
lean_dec_ref(v_a_2008_);
lean_dec(v_a_2007_);
lean_dec(v_a_2006_);
return v_res_2017_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0(void){
_start:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2018_ = lean_unsigned_to_nat(1u);
v___x_2019_ = lean_nat_to_int(v___x_2018_);
return v___x_2019_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2(void){
_start:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2021_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__1));
v___x_2022_ = l_Lean_stringToMessageData(v___x_2021_);
return v___x_2022_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4(void){
_start:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2024_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__3));
v___x_2025_ = l_Lean_stringToMessageData(v___x_2024_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(lean_object* v_e_2026_, lean_object* v_p_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_){
_start:
{
lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; uint8_t v___x_2069_; lean_object* v___x_2070_; 
v___x_2069_ = 1;
lean_inc_ref(v_e_2026_);
v___x_2070_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_2026_, v___x_2069_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v_a_2071_; 
v_a_2071_ = lean_ctor_get(v___x_2070_, 0);
lean_inc(v_a_2071_);
lean_dec_ref_known(v___x_2070_, 1);
if (lean_obj_tag(v_a_2071_) == 1)
{
lean_object* v_val_2072_; lean_object* v_fst_2073_; lean_object* v_snd_2074_; lean_object* v___x_2075_; 
lean_dec_ref(v_e_2026_);
v_val_2072_ = lean_ctor_get(v_a_2071_, 0);
lean_inc(v_val_2072_);
lean_dec_ref_known(v_a_2071_, 1);
v_fst_2073_ = lean_ctor_get(v_val_2072_, 0);
lean_inc(v_fst_2073_);
v_snd_2074_ = lean_ctor_get(v_val_2072_, 1);
lean_inc(v_snd_2074_);
lean_dec(v_val_2072_);
lean_inc(v_a_2037_);
lean_inc_ref(v_a_2036_);
lean_inc(v_a_2035_);
lean_inc_ref(v_a_2034_);
lean_inc(v_a_2033_);
lean_inc_ref(v_a_2032_);
lean_inc(v_a_2031_);
lean_inc_ref(v_a_2030_);
lean_inc(v_a_2029_);
lean_inc(v_a_2028_);
v___x_2075_ = lean_grind_cutsat_mk_var(v_snd_2074_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2084_; 
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2078_ = v___x_2075_;
v_isShared_2079_ = v_isSharedCheck_2084_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2075_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2084_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2080_; lean_object* v___x_2082_; 
v___x_2080_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2080_, 0, v_fst_2073_);
lean_ctor_set(v___x_2080_, 1, v_a_2076_);
lean_ctor_set(v___x_2080_, 2, v_p_2027_);
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 0, v___x_2080_);
v___x_2082_ = v___x_2078_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2080_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
else
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2092_; 
lean_dec(v_fst_2073_);
lean_dec_ref(v_p_2027_);
v_a_2085_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2087_ = v___x_2075_;
v_isShared_2088_ = v_isSharedCheck_2092_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2075_);
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
}
else
{
lean_object* v___x_2093_; 
lean_dec(v_a_2071_);
lean_inc_ref(v_e_2026_);
v___x_2093_ = l_Lean_Meta_getIntValue_x3f(v_e_2026_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v_a_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2135_; 
v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2096_ = v___x_2093_;
v_isShared_2097_ = v_isSharedCheck_2135_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_a_2094_);
lean_dec(v___x_2093_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2135_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
if (lean_obj_tag(v_a_2094_) == 1)
{
lean_object* v_val_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2134_; 
v_val_2098_ = lean_ctor_get(v_a_2094_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v_a_2094_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2100_ = v_a_2094_;
v_isShared_2101_ = v_isSharedCheck_2134_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_val_2098_);
lean_dec(v_a_2094_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2134_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
uint8_t v___x_2102_; 
v___x_2102_ = l_Int_Internal_Linear_Poly_isZero(v_p_2027_);
if (v___x_2102_ == 0)
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
lean_del_object(v___x_2100_);
lean_dec(v_val_2098_);
lean_del_object(v___x_2096_);
v___x_2103_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2);
lean_inc_ref(v_e_2026_);
v___x_2104_ = l_Lean_indentExpr(v_e_2026_);
v___x_2105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2103_);
lean_ctor_set(v___x_2105_, 1, v___x_2104_);
v___x_2106_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4);
v___x_2107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2105_);
lean_ctor_set(v___x_2107_, 1, v___x_2106_);
v___x_2108_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_2032_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v_a_2109_; uint8_t v_verbose_2110_; 
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
lean_inc(v_a_2109_);
lean_dec_ref_known(v___x_2108_, 1);
v_verbose_2110_ = lean_ctor_get_uint8(v_a_2109_, 0);
lean_dec(v_a_2109_);
if (v_verbose_2110_ == 0)
{
lean_dec_ref_known(v___x_2107_, 2);
v___y_2040_ = v_a_2028_;
v___y_2041_ = v_a_2029_;
v___y_2042_ = v_a_2030_;
v___y_2043_ = v_a_2031_;
v___y_2044_ = v_a_2032_;
v___y_2045_ = v_a_2033_;
v___y_2046_ = v_a_2034_;
v___y_2047_ = v_a_2035_;
v___y_2048_ = v_a_2036_;
v___y_2049_ = v_a_2037_;
goto v___jp_2039_;
}
else
{
lean_object* v___x_2111_; 
v___x_2111_ = l_Lean_Meta_Sym_reportIssue(v___x_2107_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_dec_ref_known(v___x_2111_, 1);
v___y_2040_ = v_a_2028_;
v___y_2041_ = v_a_2029_;
v___y_2042_ = v_a_2030_;
v___y_2043_ = v_a_2031_;
v___y_2044_ = v_a_2032_;
v___y_2045_ = v_a_2033_;
v___y_2046_ = v_a_2034_;
v___y_2047_ = v_a_2035_;
v___y_2048_ = v_a_2036_;
v___y_2049_ = v_a_2037_;
goto v___jp_2039_;
}
else
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
lean_dec_ref(v_p_2027_);
lean_dec_ref(v_e_2026_);
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2111_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2111_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
}
else
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
lean_dec_ref_known(v___x_2107_, 2);
lean_dec_ref(v_p_2027_);
lean_dec_ref(v_e_2026_);
v_a_2120_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2122_ = v___x_2108_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2108_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2123_ == 0)
{
v___x_2125_ = v___x_2122_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2120_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
else
{
lean_object* v___x_2129_; 
lean_dec_ref(v_p_2027_);
lean_dec_ref(v_e_2026_);
if (v_isShared_2101_ == 0)
{
lean_ctor_set_tag(v___x_2100_, 0);
v___x_2129_ = v___x_2100_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_val_2098_);
v___x_2129_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
lean_object* v___x_2131_; 
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 0, v___x_2129_);
v___x_2131_ = v___x_2096_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2129_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
}
}
else
{
lean_del_object(v___x_2096_);
lean_dec(v_a_2094_);
v___y_2040_ = v_a_2028_;
v___y_2041_ = v_a_2029_;
v___y_2042_ = v_a_2030_;
v___y_2043_ = v_a_2031_;
v___y_2044_ = v_a_2032_;
v___y_2045_ = v_a_2033_;
v___y_2046_ = v_a_2034_;
v___y_2047_ = v_a_2035_;
v___y_2048_ = v_a_2036_;
v___y_2049_ = v_a_2037_;
goto v___jp_2039_;
}
}
}
else
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
lean_dec_ref(v_p_2027_);
lean_dec_ref(v_e_2026_);
v_a_2136_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2138_ = v___x_2093_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2093_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2141_; 
if (v_isShared_2139_ == 0)
{
v___x_2141_ = v___x_2138_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_a_2136_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
}
else
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
lean_dec_ref(v_p_2027_);
lean_dec_ref(v_e_2026_);
v_a_2144_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2146_ = v___x_2070_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2070_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
if (v_isShared_2147_ == 0)
{
v___x_2149_ = v___x_2146_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_a_2144_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
v___jp_2039_:
{
lean_object* v___x_2050_; 
lean_inc(v___y_2049_);
lean_inc_ref(v___y_2048_);
lean_inc(v___y_2047_);
lean_inc_ref(v___y_2046_);
lean_inc(v___y_2045_);
lean_inc_ref(v___y_2044_);
lean_inc(v___y_2043_);
lean_inc_ref(v___y_2042_);
lean_inc(v___y_2041_);
lean_inc(v___y_2040_);
v___x_2050_ = lean_grind_cutsat_mk_var(v_e_2026_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2060_; 
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2053_ = v___x_2050_;
v_isShared_2054_ = v_isSharedCheck_2060_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2050_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2060_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2058_; 
v___x_2055_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0);
v___x_2056_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2055_);
lean_ctor_set(v___x_2056_, 1, v_a_2051_);
lean_ctor_set(v___x_2056_, 2, v_p_2027_);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 0, v___x_2056_);
v___x_2058_ = v___x_2053_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v___x_2056_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
else
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
lean_dec_ref(v_p_2027_);
v_a_2061_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_2050_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2050_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___boxed(lean_object* v_e_2152_, lean_object* v_p_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_){
_start:
{
lean_object* v_res_2165_; 
v_res_2165_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_e_2152_, v_p_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_);
lean_dec(v_a_2163_);
lean_dec_ref(v_a_2162_);
lean_dec(v_a_2161_);
lean_dec_ref(v_a_2160_);
lean_dec(v_a_2159_);
lean_dec_ref(v_a_2158_);
lean_dec(v_a_2157_);
lean_dec_ref(v_a_2156_);
lean_dec(v_a_2155_);
lean_dec(v_a_2154_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go(lean_object* v_e_2166_, lean_object* v_p_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_){
_start:
{
uint8_t v___x_2179_; lean_object* v___x_2180_; 
v___x_2179_ = 1;
lean_inc_ref(v_e_2166_);
v___x_2180_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_2166_, v___x_2179_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_a_2181_);
lean_dec_ref_known(v___x_2180_, 1);
if (lean_obj_tag(v_a_2181_) == 1)
{
lean_object* v_val_2182_; lean_object* v_fst_2183_; lean_object* v_snd_2184_; lean_object* v___x_2185_; 
lean_dec_ref(v_e_2166_);
v_val_2182_ = lean_ctor_get(v_a_2181_, 0);
lean_inc(v_val_2182_);
lean_dec_ref_known(v_a_2181_, 1);
v_fst_2183_ = lean_ctor_get(v_val_2182_, 0);
lean_inc(v_fst_2183_);
v_snd_2184_ = lean_ctor_get(v_val_2182_, 1);
lean_inc(v_snd_2184_);
lean_dec(v_val_2182_);
v___x_2185_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_snd_2184_, v_p_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_object* v_a_2186_; 
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
lean_inc(v_a_2186_);
lean_dec_ref_known(v___x_2185_, 1);
v_e_2166_ = v_fst_2183_;
v_p_2167_ = v_a_2186_;
goto _start;
}
else
{
lean_dec(v_fst_2183_);
return v___x_2185_;
}
}
else
{
lean_object* v___x_2188_; 
lean_dec(v_a_2181_);
v___x_2188_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_e_2166_, v_p_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_);
return v___x_2188_;
}
}
else
{
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2196_; 
lean_dec_ref(v_p_2167_);
lean_dec_ref(v_e_2166_);
v_a_2189_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2191_ = v___x_2180_;
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2180_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2194_; 
if (v_isShared_2192_ == 0)
{
v___x_2194_ = v___x_2191_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_a_2189_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go___boxed(lean_object* v_e_2197_, lean_object* v_p_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_){
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go(v_e_2197_, v_p_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_, v_a_2208_);
lean_dec(v_a_2208_);
lean_dec_ref(v_a_2207_);
lean_dec(v_a_2206_);
lean_dec_ref(v_a_2205_);
lean_dec(v_a_2204_);
lean_dec_ref(v_a_2203_);
lean_dec(v_a_2202_);
lean_dec_ref(v_a_2201_);
lean_dec(v_a_2200_);
lean_dec(v_a_2199_);
return v_res_2210_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0(void){
_start:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2211_ = lean_unsigned_to_nat(0u);
v___x_2212_ = lean_nat_to_int(v___x_2211_);
return v___x_2212_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1(void){
_start:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2213_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0);
v___x_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2213_);
return v___x_2214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly(lean_object* v_e_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_){
_start:
{
uint8_t v___x_2227_; lean_object* v___x_2228_; 
v___x_2227_ = 1;
lean_inc_ref(v_e_2215_);
v___x_2228_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_2215_, v___x_2227_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v_a_2229_; 
v_a_2229_ = lean_ctor_get(v___x_2228_, 0);
lean_inc(v_a_2229_);
lean_dec_ref_known(v___x_2228_, 1);
if (lean_obj_tag(v_a_2229_) == 1)
{
lean_object* v_val_2230_; lean_object* v_fst_2231_; lean_object* v_snd_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
lean_dec_ref(v_e_2215_);
v_val_2230_ = lean_ctor_get(v_a_2229_, 0);
lean_inc(v_val_2230_);
lean_dec_ref_known(v_a_2229_, 1);
v_fst_2231_ = lean_ctor_get(v_val_2230_, 0);
lean_inc(v_fst_2231_);
v_snd_2232_ = lean_ctor_get(v_val_2230_, 1);
lean_inc(v_snd_2232_);
lean_dec(v_val_2230_);
v___x_2233_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1);
v___x_2234_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_snd_2232_, v___x_2233_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_a_2235_; lean_object* v___x_2236_; 
v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
lean_inc(v_a_2235_);
lean_dec_ref_known(v___x_2234_, 1);
v___x_2236_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go(v_fst_2231_, v_a_2235_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
return v___x_2236_;
}
else
{
lean_dec(v_fst_2231_);
return v___x_2234_;
}
}
else
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
lean_dec(v_a_2229_);
v___x_2237_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1);
v___x_2238_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_e_2215_, v___x_2237_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
return v___x_2238_;
}
}
else
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
lean_dec_ref(v_e_2215_);
v_a_2239_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_2228_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2228_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2242_ == 0)
{
v___x_2244_ = v___x_2241_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2239_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly___boxed(lean_object* v_e_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_e_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_);
lean_dec(v_a_2257_);
lean_dec_ref(v_a_2256_);
lean_dec(v_a_2255_);
lean_dec_ref(v_a_2254_);
lean_dec(v_a_2253_);
lean_dec_ref(v_a_2252_);
lean_dec(v_a_2251_);
lean_dec_ref(v_a_2250_);
lean_dec(v_a_2249_);
lean_dec(v_a_2248_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg(lean_object* v_e_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_){
_start:
{
lean_object* v___x_2285_; 
lean_inc_ref(v_e_2275_);
v___x_2285_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2275_, v_a_2277_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v_a_2286_; lean_object* v___x_2287_; uint8_t v___x_2288_; 
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_a_2286_);
lean_dec_ref_known(v___x_2285_, 1);
v___x_2287_ = l_Lean_Expr_cleanupAnnotations(v_a_2286_);
lean_dec(v_a_2286_);
v___x_2288_ = l_Lean_Expr_isApp(v___x_2287_);
if (v___x_2288_ == 0)
{
lean_dec_ref(v___x_2287_);
lean_dec_ref(v_e_2275_);
goto v___jp_2281_;
}
else
{
lean_object* v___x_2289_; uint8_t v___x_2290_; 
v___x_2289_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2287_);
v___x_2290_ = l_Lean_Expr_isApp(v___x_2289_);
if (v___x_2290_ == 0)
{
lean_dec_ref(v___x_2289_);
lean_dec_ref(v___x_2287_);
lean_dec_ref(v_e_2275_);
goto v___jp_2281_;
}
else
{
lean_object* v___x_2291_; uint8_t v___x_2292_; 
v___x_2291_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2289_);
v___x_2292_ = l_Lean_Expr_isApp(v___x_2291_);
if (v___x_2292_ == 0)
{
lean_dec_ref(v___x_2291_);
lean_dec_ref(v___x_2289_);
lean_dec_ref(v___x_2287_);
lean_dec_ref(v_e_2275_);
goto v___jp_2281_;
}
else
{
lean_object* v_arg_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; uint8_t v___x_2296_; 
v_arg_2293_ = lean_ctor_get(v___x_2289_, 1);
lean_inc_ref(v_arg_2293_);
lean_dec_ref(v___x_2289_);
v___x_2294_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2291_);
v___x_2295_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__2));
v___x_2296_ = l_Lean_Expr_isConstOf(v___x_2294_, v___x_2295_);
if (v___x_2296_ == 0)
{
lean_object* v___x_2297_; uint8_t v___x_2298_; 
v___x_2297_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__5));
v___x_2298_ = l_Lean_Expr_isConstOf(v___x_2294_, v___x_2297_);
if (v___x_2298_ == 0)
{
uint8_t v___x_2299_; 
lean_dec_ref(v_e_2275_);
v___x_2299_ = l_Lean_Expr_isApp(v___x_2294_);
if (v___x_2299_ == 0)
{
lean_dec_ref(v___x_2294_);
lean_dec_ref(v_arg_2293_);
lean_dec_ref(v___x_2291_);
lean_dec_ref(v___x_2287_);
goto v___jp_2281_;
}
else
{
lean_object* v___x_2300_; uint8_t v___x_2301_; 
v___x_2300_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2294_);
lean_dec_ref(v___x_2294_);
v___x_2301_ = l_Lean_Expr_isApp(v___x_2300_);
if (v___x_2301_ == 0)
{
lean_dec_ref(v___x_2300_);
lean_dec_ref(v_arg_2293_);
lean_dec_ref(v___x_2291_);
lean_dec_ref(v___x_2287_);
goto v___jp_2281_;
}
else
{
lean_object* v___x_2302_; uint8_t v___x_2303_; 
v___x_2302_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2300_);
lean_dec_ref(v___x_2300_);
v___x_2303_ = l_Lean_Expr_isApp(v___x_2302_);
if (v___x_2303_ == 0)
{
lean_dec_ref(v___x_2302_);
lean_dec_ref(v_arg_2293_);
lean_dec_ref(v___x_2291_);
lean_dec_ref(v___x_2287_);
goto v___jp_2281_;
}
else
{
lean_object* v_arg_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; uint8_t v___x_2307_; 
v_arg_2304_ = lean_ctor_get(v___x_2291_, 1);
lean_inc_ref(v_arg_2304_);
lean_dec_ref(v___x_2291_);
v___x_2305_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2302_);
lean_dec_ref(v___x_2302_);
v___x_2306_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11));
v___x_2307_ = l_Lean_Expr_isConstOf(v___x_2305_, v___x_2306_);
if (v___x_2307_ == 0)
{
lean_object* v___x_2308_; uint8_t v___x_2309_; 
lean_dec_ref(v_arg_2293_);
lean_dec_ref(v___x_2287_);
v___x_2308_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___closed__8));
v___x_2309_ = l_Lean_Expr_isConstOf(v___x_2305_, v___x_2308_);
if (v___x_2309_ == 0)
{
lean_object* v___x_2310_; uint8_t v___x_2311_; 
v___x_2310_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__2));
v___x_2311_ = l_Lean_Expr_isConstOf(v___x_2305_, v___x_2310_);
lean_dec_ref(v___x_2305_);
if (v___x_2311_ == 0)
{
lean_dec_ref(v_arg_2304_);
goto v___jp_2281_;
}
else
{
lean_object* v___x_2312_; 
v___x_2312_ = l_Lean_Meta_Structural_isInstHAddInt___redArg(v_arg_2304_, v_a_2277_);
return v___x_2312_;
}
}
else
{
lean_object* v___x_2313_; 
lean_dec_ref(v___x_2305_);
v___x_2313_ = l_Lean_Meta_Structural_isInstHSubInt___redArg(v_arg_2304_, v_a_2277_);
return v___x_2313_;
}
}
else
{
lean_object* v_arg_2314_; lean_object* v___x_2315_; 
lean_dec_ref(v___x_2305_);
v_arg_2314_ = lean_ctor_get(v___x_2287_, 1);
lean_inc_ref(v_arg_2314_);
lean_dec_ref(v___x_2287_);
v___x_2315_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_2304_, v_a_2277_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; uint8_t v___x_2317_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
v___x_2317_ = lean_unbox(v_a_2316_);
if (v___x_2317_ == 0)
{
lean_dec_ref(v_arg_2314_);
lean_dec_ref(v_arg_2293_);
return v___x_2315_;
}
else
{
lean_object* v___x_2318_; 
lean_dec_ref_known(v___x_2315_, 1);
v___x_2318_ = l_Lean_Meta_isIntValue(v_arg_2293_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; uint8_t v___x_2320_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
v___x_2320_ = lean_unbox(v_a_2319_);
if (v___x_2320_ == 0)
{
lean_object* v___x_2321_; 
lean_dec_ref_known(v___x_2318_, 1);
v___x_2321_ = l_Lean_Meta_isIntValue(v_arg_2314_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_);
return v___x_2321_;
}
else
{
lean_dec_ref(v_arg_2314_);
return v___x_2318_;
}
}
else
{
lean_dec_ref(v_arg_2314_);
return v___x_2318_;
}
}
}
else
{
lean_dec_ref(v_arg_2314_);
lean_dec_ref(v_arg_2293_);
return v___x_2315_;
}
}
}
}
}
}
else
{
lean_object* v___x_2322_; 
lean_dec_ref(v___x_2294_);
lean_dec_ref(v_arg_2293_);
lean_dec_ref(v___x_2291_);
lean_dec_ref(v___x_2287_);
v___x_2322_ = l_Lean_Meta_isIntValue(v_e_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_);
return v___x_2322_;
}
}
else
{
lean_object* v___x_2323_; 
lean_dec_ref(v___x_2294_);
lean_dec_ref(v___x_2291_);
lean_dec_ref(v___x_2287_);
lean_dec_ref(v_e_2275_);
v___x_2323_ = l_Lean_Meta_Structural_isInstNegInt___redArg(v_arg_2293_, v_a_2277_);
return v___x_2323_;
}
}
}
}
}
else
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2331_; 
lean_dec_ref(v_e_2275_);
v_a_2324_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2326_ = v___x_2285_;
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2285_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2329_; 
if (v_isShared_2327_ == 0)
{
v___x_2329_ = v___x_2326_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_a_2324_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
v___jp_2281_:
{
uint8_t v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2282_ = 0;
v___x_2283_ = lean_box(v___x_2282_);
v___x_2284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2283_);
return v___x_2284_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg___boxed(lean_object* v_e_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_){
_start:
{
lean_object* v_res_2338_; 
v_res_2338_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg(v_e_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_);
lean_dec(v_a_2336_);
lean_dec_ref(v_a_2335_);
lean_dec(v_a_2334_);
lean_dec_ref(v_a_2333_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith(lean_object* v_e_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_){
_start:
{
lean_object* v___x_2351_; 
v___x_2351_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg(v_e_2339_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_);
return v___x_2351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___boxed(lean_object* v_e_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_){
_start:
{
lean_object* v_res_2364_; 
v_res_2364_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith(v_e_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
lean_dec(v_a_2356_);
lean_dec_ref(v_a_2355_);
lean_dec(v_a_2354_);
lean_dec(v_a_2353_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_x3f_monomial_x3f(lean_object* v_e_2365_, lean_object* v_p_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_){
_start:
{
uint8_t v___x_2378_; lean_object* v___x_2379_; 
v___x_2378_ = 1;
lean_inc_ref(v_e_2365_);
v___x_2379_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_2365_, v___x_2378_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_object* v_a_2380_; 
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
lean_inc(v_a_2380_);
lean_dec_ref_known(v___x_2379_, 1);
if (lean_obj_tag(v_a_2380_) == 1)
{
lean_object* v_val_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2432_; 
lean_dec_ref(v_e_2365_);
v_val_2381_ = lean_ctor_get(v_a_2380_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v_a_2380_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2383_ = v_a_2380_;
v_isShared_2384_ = v_isSharedCheck_2432_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_val_2381_);
lean_dec(v_a_2380_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2432_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v_fst_2385_; lean_object* v_snd_2386_; lean_object* v___x_2387_; 
v_fst_2385_ = lean_ctor_get(v_val_2381_, 0);
lean_inc(v_fst_2385_);
v_snd_2386_ = lean_ctor_get(v_val_2381_, 1);
lean_inc_n(v_snd_2386_, 2);
lean_dec(v_val_2381_);
v___x_2387_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg(v_snd_2386_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_object* v_a_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2423_; 
v_a_2388_ = lean_ctor_get(v___x_2387_, 0);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2390_ = v___x_2387_;
v_isShared_2391_ = v_isSharedCheck_2423_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_a_2388_);
lean_dec(v___x_2387_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2423_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2397_; uint8_t v___x_2398_; 
v___x_2397_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0);
v___x_2398_ = lean_int_dec_eq(v_fst_2385_, v___x_2397_);
if (v___x_2398_ == 0)
{
lean_object* v___x_2399_; uint8_t v___x_2400_; 
v___x_2399_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0);
v___x_2400_ = lean_int_dec_eq(v_fst_2385_, v___x_2399_);
if (v___x_2400_ == 0)
{
uint8_t v___x_2401_; 
v___x_2401_ = lean_unbox(v_a_2388_);
lean_dec(v_a_2388_);
if (v___x_2401_ == 0)
{
lean_object* v___x_2402_; 
lean_del_object(v___x_2390_);
lean_inc(v_a_2376_);
lean_inc_ref(v_a_2375_);
lean_inc(v_a_2374_);
lean_inc_ref(v_a_2373_);
lean_inc(v_a_2372_);
lean_inc_ref(v_a_2371_);
lean_inc(v_a_2370_);
lean_inc_ref(v_a_2369_);
lean_inc(v_a_2368_);
lean_inc(v_a_2367_);
v___x_2402_ = lean_grind_cutsat_mk_var(v_snd_2386_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v_a_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2414_; 
v_a_2403_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2405_ = v___x_2402_;
v_isShared_2406_ = v_isSharedCheck_2414_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_a_2403_);
lean_dec(v___x_2402_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2414_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2407_; lean_object* v___x_2409_; 
v___x_2407_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2407_, 0, v_fst_2385_);
lean_ctor_set(v___x_2407_, 1, v_a_2403_);
lean_ctor_set(v___x_2407_, 2, v_p_2366_);
if (v_isShared_2384_ == 0)
{
lean_ctor_set(v___x_2383_, 0, v___x_2407_);
v___x_2409_ = v___x_2383_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v___x_2407_);
v___x_2409_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
lean_object* v___x_2411_; 
if (v_isShared_2406_ == 0)
{
lean_ctor_set(v___x_2405_, 0, v___x_2409_);
v___x_2411_ = v___x_2405_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v___x_2409_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
}
else
{
lean_object* v_a_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2422_; 
lean_dec(v_fst_2385_);
lean_del_object(v___x_2383_);
lean_dec_ref(v_p_2366_);
v_a_2415_ = lean_ctor_get(v___x_2402_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2417_ = v___x_2402_;
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_a_2415_);
lean_dec(v___x_2402_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2420_; 
if (v_isShared_2418_ == 0)
{
v___x_2420_ = v___x_2417_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_a_2415_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
}
}
}
}
else
{
lean_dec(v_snd_2386_);
lean_dec(v_fst_2385_);
lean_del_object(v___x_2383_);
lean_dec_ref(v_p_2366_);
goto v___jp_2392_;
}
}
else
{
lean_dec(v_a_2388_);
lean_dec(v_snd_2386_);
lean_dec(v_fst_2385_);
lean_del_object(v___x_2383_);
lean_dec_ref(v_p_2366_);
goto v___jp_2392_;
}
}
else
{
lean_dec(v_a_2388_);
lean_dec(v_snd_2386_);
lean_dec(v_fst_2385_);
lean_del_object(v___x_2383_);
lean_dec_ref(v_p_2366_);
goto v___jp_2392_;
}
v___jp_2392_:
{
lean_object* v___x_2393_; lean_object* v___x_2395_; 
v___x_2393_ = lean_box(0);
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 0, v___x_2393_);
v___x_2395_ = v___x_2390_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2393_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
}
else
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2431_; 
lean_dec(v_snd_2386_);
lean_dec(v_fst_2385_);
lean_del_object(v___x_2383_);
lean_dec_ref(v_p_2366_);
v_a_2424_ = lean_ctor_get(v___x_2387_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2426_ = v___x_2387_;
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___x_2387_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2429_; 
if (v_isShared_2427_ == 0)
{
v___x_2429_ = v___x_2426_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_a_2424_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
}
else
{
lean_object* v___x_2433_; 
lean_dec(v_a_2380_);
lean_inc_ref(v_e_2365_);
v___x_2433_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isLinearArith___redArg(v_e_2365_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
if (lean_obj_tag(v___x_2433_) == 0)
{
lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2463_; 
v_a_2434_ = lean_ctor_get(v___x_2433_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2436_ = v___x_2433_;
v_isShared_2437_ = v_isSharedCheck_2463_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v___x_2433_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2463_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
uint8_t v___x_2438_; 
v___x_2438_ = lean_unbox(v_a_2434_);
lean_dec(v_a_2434_);
if (v___x_2438_ == 0)
{
lean_object* v___x_2439_; 
lean_del_object(v___x_2436_);
lean_inc(v_a_2376_);
lean_inc_ref(v_a_2375_);
lean_inc(v_a_2374_);
lean_inc_ref(v_a_2373_);
lean_inc(v_a_2372_);
lean_inc_ref(v_a_2371_);
lean_inc(v_a_2370_);
lean_inc_ref(v_a_2369_);
lean_inc(v_a_2368_);
lean_inc(v_a_2367_);
v___x_2439_ = lean_grind_cutsat_mk_var(v_e_2365_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
if (lean_obj_tag(v___x_2439_) == 0)
{
lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2450_; 
v_a_2440_ = lean_ctor_get(v___x_2439_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2439_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2442_ = v___x_2439_;
v_isShared_2443_ = v_isSharedCheck_2450_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v___x_2439_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2450_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2448_; 
v___x_2444_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0);
v___x_2445_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2444_);
lean_ctor_set(v___x_2445_, 1, v_a_2440_);
lean_ctor_set(v___x_2445_, 2, v_p_2366_);
v___x_2446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2445_);
if (v_isShared_2443_ == 0)
{
lean_ctor_set(v___x_2442_, 0, v___x_2446_);
v___x_2448_ = v___x_2442_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v___x_2446_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
else
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2458_; 
lean_dec_ref(v_p_2366_);
v_a_2451_ = lean_ctor_get(v___x_2439_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2439_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2453_ = v___x_2439_;
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2439_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2456_; 
if (v_isShared_2454_ == 0)
{
v___x_2456_ = v___x_2453_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_a_2451_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
}
else
{
lean_object* v___x_2459_; lean_object* v___x_2461_; 
lean_dec_ref(v_p_2366_);
lean_dec_ref(v_e_2365_);
v___x_2459_ = lean_box(0);
if (v_isShared_2437_ == 0)
{
lean_ctor_set(v___x_2436_, 0, v___x_2459_);
v___x_2461_ = v___x_2436_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v___x_2459_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
}
else
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2471_; 
lean_dec_ref(v_p_2366_);
lean_dec_ref(v_e_2365_);
v_a_2464_ = lean_ctor_get(v___x_2433_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2466_ = v___x_2433_;
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2433_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2469_; 
if (v_isShared_2467_ == 0)
{
v___x_2469_ = v___x_2466_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2464_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
}
}
else
{
lean_object* v_a_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2479_; 
lean_dec_ref(v_p_2366_);
lean_dec_ref(v_e_2365_);
v_a_2472_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2474_ = v___x_2379_;
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_a_2472_);
lean_dec(v___x_2379_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2477_; 
if (v_isShared_2475_ == 0)
{
v___x_2477_ = v___x_2474_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_a_2472_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_x3f_monomial_x3f___boxed(lean_object* v_e_2480_, lean_object* v_p_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_){
_start:
{
lean_object* v_res_2493_; 
v_res_2493_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_x3f_monomial_x3f(v_e_2480_, v_p_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_);
lean_dec(v_a_2491_);
lean_dec_ref(v_a_2490_);
lean_dec(v_a_2489_);
lean_dec_ref(v_a_2488_);
lean_dec(v_a_2487_);
lean_dec_ref(v_a_2486_);
lean_dec(v_a_2485_);
lean_dec_ref(v_a_2484_);
lean_dec(v_a_2483_);
lean_dec(v_a_2482_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_x3f_go(lean_object* v_e_2494_, lean_object* v_p_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_){
_start:
{
uint8_t v___x_2507_; lean_object* v___x_2508_; 
v___x_2507_ = 1;
lean_inc_ref(v_e_2494_);
v___x_2508_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_2494_, v___x_2507_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v_a_2509_; 
v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
lean_inc(v_a_2509_);
lean_dec_ref_known(v___x_2508_, 1);
if (lean_obj_tag(v_a_2509_) == 1)
{
lean_object* v_val_2510_; lean_object* v_fst_2511_; lean_object* v_snd_2512_; lean_object* v___x_2513_; 
lean_dec_ref(v_e_2494_);
v_val_2510_ = lean_ctor_get(v_a_2509_, 0);
lean_inc(v_val_2510_);
lean_dec_ref_known(v_a_2509_, 1);
v_fst_2511_ = lean_ctor_get(v_val_2510_, 0);
lean_inc(v_fst_2511_);
v_snd_2512_ = lean_ctor_get(v_val_2510_, 1);
lean_inc(v_snd_2512_);
lean_dec(v_val_2510_);
v___x_2513_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_x3f_monomial_x3f(v_snd_2512_, v_p_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_);
if (lean_obj_tag(v___x_2513_) == 0)
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2524_; 
v_a_2514_ = lean_ctor_get(v___x_2513_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2516_ = v___x_2513_;
v_isShared_2517_ = v_isSharedCheck_2524_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2513_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2524_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
if (lean_obj_tag(v_a_2514_) == 1)
{
lean_object* v_val_2518_; 
lean_del_object(v___x_2516_);
v_val_2518_ = lean_ctor_get(v_a_2514_, 0);
lean_inc(v_val_2518_);
lean_dec_ref_known(v_a_2514_, 1);
v_e_2494_ = v_fst_2511_;
v_p_2495_ = v_val_2518_;
goto _start;
}
else
{
lean_object* v___x_2520_; lean_object* v___x_2522_; 
lean_dec(v_a_2514_);
lean_dec(v_fst_2511_);
v___x_2520_ = lean_box(0);
if (v_isShared_2517_ == 0)
{
lean_ctor_set(v___x_2516_, 0, v___x_2520_);
v___x_2522_ = v___x_2516_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v___x_2520_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
return v___x_2522_;
}
}
}
}
else
{
lean_dec(v_fst_2511_);
return v___x_2513_;
}
}
else
{
lean_object* v___x_2525_; 
lean_dec(v_a_2509_);
v___x_2525_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_x3f_monomial_x3f(v_e_2494_, v_p_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_);
return v___x_2525_;
}
}
else
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
lean_dec_ref(v_p_2495_);
lean_dec_ref(v_e_2494_);
v_a_2526_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2528_ = v___x_2508_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2508_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2529_ == 0)
{
v___x_2531_ = v___x_2528_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_a_2526_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_x3f_go___boxed(lean_object* v_e_2534_, lean_object* v_p_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_){
_start:
{
lean_object* v_res_2547_; 
v_res_2547_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_x3f_go(v_e_2534_, v_p_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_);
lean_dec(v_a_2545_);
lean_dec_ref(v_a_2544_);
lean_dec(v_a_2543_);
lean_dec_ref(v_a_2542_);
lean_dec(v_a_2541_);
lean_dec_ref(v_a_2540_);
lean_dec(v_a_2539_);
lean_dec_ref(v_a_2538_);
lean_dec(v_a_2537_);
lean_dec(v_a_2536_);
return v_res_2547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly_x3f(lean_object* v_e_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_){
_start:
{
lean_object* v___x_2560_; 
lean_inc_ref(v_e_2548_);
v___x_2560_ = l_Lean_Meta_getIntValue_x3f(v_e_2548_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_);
if (lean_obj_tag(v___x_2560_) == 0)
{
lean_object* v_a_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2635_; 
v_a_2561_ = lean_ctor_get(v___x_2560_, 0);
v_isSharedCheck_2635_ = !lean_is_exclusive(v___x_2560_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2563_ = v___x_2560_;
v_isShared_2564_ = v_isSharedCheck_2635_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_a_2561_);
lean_dec(v___x_2560_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2635_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
if (lean_obj_tag(v_a_2561_) == 1)
{
lean_object* v_val_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2576_; 
lean_dec_ref(v_e_2548_);
v_val_2565_ = lean_ctor_get(v_a_2561_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v_a_2561_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2567_ = v_a_2561_;
v_isShared_2568_ = v_isSharedCheck_2576_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_val_2565_);
lean_dec(v_a_2561_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2576_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2569_; lean_object* v___x_2571_; 
v___x_2569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2569_, 0, v_val_2565_);
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 0, v___x_2569_);
v___x_2571_ = v___x_2567_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v___x_2569_);
v___x_2571_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
lean_object* v___x_2573_; 
if (v_isShared_2564_ == 0)
{
lean_ctor_set(v___x_2563_, 0, v___x_2571_);
v___x_2573_ = v___x_2563_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v___x_2571_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
}
else
{
uint8_t v___x_2577_; lean_object* v___x_2578_; 
lean_del_object(v___x_2563_);
lean_dec(v_a_2561_);
v___x_2577_ = 1;
lean_inc_ref(v_e_2548_);
v___x_2578_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_2548_, v___x_2577_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_);
if (lean_obj_tag(v___x_2578_) == 0)
{
lean_object* v_a_2579_; 
v_a_2579_ = lean_ctor_get(v___x_2578_, 0);
lean_inc(v_a_2579_);
lean_dec_ref_known(v___x_2578_, 1);
if (lean_obj_tag(v_a_2579_) == 1)
{
lean_object* v_val_2580_; lean_object* v_fst_2581_; lean_object* v_snd_2582_; lean_object* v___x_2583_; 
lean_dec_ref(v_e_2548_);
v_val_2580_ = lean_ctor_get(v_a_2579_, 0);
lean_inc(v_val_2580_);
lean_dec_ref_known(v_a_2579_, 1);
v_fst_2581_ = lean_ctor_get(v_val_2580_, 0);
lean_inc(v_fst_2581_);
v_snd_2582_ = lean_ctor_get(v_val_2580_, 1);
lean_inc_n(v_snd_2582_, 2);
lean_dec(v_val_2580_);
v___x_2583_ = l_Lean_Meta_getIntValue_x3f(v_snd_2582_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v_a_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2616_; 
v_a_2584_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2586_ = v___x_2583_;
v_isShared_2587_ = v_isSharedCheck_2616_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_a_2584_);
lean_dec(v___x_2583_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2616_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
if (lean_obj_tag(v_a_2584_) == 1)
{
lean_object* v_val_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2602_; 
lean_dec(v_snd_2582_);
v_val_2588_ = lean_ctor_get(v_a_2584_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v_a_2584_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2590_ = v_a_2584_;
v_isShared_2591_ = v_isSharedCheck_2602_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_val_2588_);
lean_dec(v_a_2584_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2602_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2592_; uint8_t v___x_2593_; 
v___x_2592_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0);
v___x_2593_ = lean_int_dec_eq(v_val_2588_, v___x_2592_);
if (v___x_2593_ == 0)
{
lean_object* v___x_2595_; 
lean_del_object(v___x_2586_);
if (v_isShared_2591_ == 0)
{
lean_ctor_set_tag(v___x_2590_, 0);
v___x_2595_ = v___x_2590_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_val_2588_);
v___x_2595_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
lean_object* v___x_2596_; 
v___x_2596_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_x3f_go(v_fst_2581_, v___x_2595_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_);
return v___x_2596_;
}
}
else
{
lean_object* v___x_2598_; lean_object* v___x_2600_; 
lean_del_object(v___x_2590_);
lean_dec(v_val_2588_);
lean_dec(v_fst_2581_);
v___x_2598_ = lean_box(0);
if (v_isShared_2587_ == 0)
{
lean_ctor_set(v___x_2586_, 0, v___x_2598_);
v___x_2600_ = v___x_2586_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v___x_2598_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
else
{
lean_object* v___x_2603_; lean_object* v___x_2604_; 
lean_del_object(v___x_2586_);
lean_dec(v_a_2584_);
v___x_2603_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1);
v___x_2604_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_x3f_monomial_x3f(v_snd_2582_, v___x_2603_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v_a_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2615_; 
v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2607_ = v___x_2604_;
v_isShared_2608_ = v_isSharedCheck_2615_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_a_2605_);
lean_dec(v___x_2604_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2615_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
if (lean_obj_tag(v_a_2605_) == 1)
{
lean_object* v_val_2609_; lean_object* v___x_2610_; 
lean_del_object(v___x_2607_);
v_val_2609_ = lean_ctor_get(v_a_2605_, 0);
lean_inc(v_val_2609_);
lean_dec_ref_known(v_a_2605_, 1);
v___x_2610_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_x3f_go(v_fst_2581_, v_val_2609_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_);
return v___x_2610_;
}
else
{
lean_object* v___x_2611_; lean_object* v___x_2613_; 
lean_dec(v_a_2605_);
lean_dec(v_fst_2581_);
v___x_2611_ = lean_box(0);
if (v_isShared_2608_ == 0)
{
lean_ctor_set(v___x_2607_, 0, v___x_2611_);
v___x_2613_ = v___x_2607_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v___x_2611_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
else
{
lean_dec(v_fst_2581_);
return v___x_2604_;
}
}
}
}
else
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
lean_dec(v_snd_2582_);
lean_dec(v_fst_2581_);
v_a_2617_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2619_ = v___x_2583_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2583_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2622_; 
if (v_isShared_2620_ == 0)
{
v___x_2622_ = v___x_2619_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_a_2617_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
else
{
lean_object* v___x_2625_; lean_object* v___x_2626_; 
lean_dec(v_a_2579_);
v___x_2625_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1);
v___x_2626_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_x3f_monomial_x3f(v_e_2548_, v___x_2625_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_);
return v___x_2626_;
}
}
else
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2634_; 
lean_dec_ref(v_e_2548_);
v_a_2627_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2629_ = v___x_2578_;
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2578_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2632_; 
if (v_isShared_2630_ == 0)
{
v___x_2632_ = v___x_2629_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2627_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
}
}
}
}
else
{
lean_object* v_a_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2643_; 
lean_dec_ref(v_e_2548_);
v_a_2636_ = lean_ctor_get(v___x_2560_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2560_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2638_ = v___x_2560_;
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_a_2636_);
lean_dec(v___x_2560_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v___x_2641_; 
if (v_isShared_2639_ == 0)
{
v___x_2641_ = v___x_2638_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_a_2636_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly_x3f___boxed(lean_object* v_e_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly_x3f(v_e_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_);
lean_dec(v_a_2654_);
lean_dec_ref(v_a_2653_);
lean_dec(v_a_2652_);
lean_dec_ref(v_a_2651_);
lean_dec(v_a_2650_);
lean_dec_ref(v_a_2649_);
lean_dec(v_a_2648_);
lean_dec_ref(v_a_2647_);
lean_dec(v_a_2646_);
lean_dec(v_a_2645_);
return v_res_2656_;
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
