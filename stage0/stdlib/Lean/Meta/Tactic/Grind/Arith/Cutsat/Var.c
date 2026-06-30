// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.Var
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Types import Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat import Lean.Meta.Tactic.Grind.Arith.Cutsat.ToInt import Lean.Meta.IntInstTesters
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t l_Int_Linear_Poly_isZero(lean_object*);
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
size_t v_x_9034__boxed_329_; size_t v_x_9035__boxed_330_; lean_object* v_res_331_; 
v_x_9034__boxed_329_ = lean_unbox_usize(v_x_325_);
lean_dec(v_x_325_);
v_x_9035__boxed_330_ = lean_unbox_usize(v_x_326_);
lean_dec(v_x_326_);
v_res_331_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_x_324_, v_x_9034__boxed_329_, v_x_9035__boxed_330_, v_x_327_, v_x_328_);
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
lean_object* v_vars_343_; lean_object* v_varMap_344_; lean_object* v_vars_x27_345_; lean_object* v_varMap_x27_346_; lean_object* v_natToIntMap_347_; lean_object* v_natDef_348_; lean_object* v_dvds_349_; lean_object* v_lowers_350_; lean_object* v_uppers_351_; lean_object* v_diseqs_352_; lean_object* v_elimEqs_353_; lean_object* v_elimStack_354_; lean_object* v_occurs_355_; lean_object* v_assignment_356_; lean_object* v_nextCnstrId_357_; uint8_t v_caseSplits_358_; lean_object* v_conflict_x3f_359_; lean_object* v_diseqSplits_360_; lean_object* v_divMod_361_; lean_object* v_toIntIds_362_; lean_object* v_toIntInfos_363_; lean_object* v_toIntTermMap_364_; lean_object* v_toIntVarMap_365_; uint8_t v_usedCommRing_366_; lean_object* v_nonlinearOccs_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_376_; 
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
v_caseSplits_358_ = lean_ctor_get_uint8(v_s_342_, sizeof(void*)*23);
v_conflict_x3f_359_ = lean_ctor_get(v_s_342_, 15);
v_diseqSplits_360_ = lean_ctor_get(v_s_342_, 16);
v_divMod_361_ = lean_ctor_get(v_s_342_, 17);
v_toIntIds_362_ = lean_ctor_get(v_s_342_, 18);
v_toIntInfos_363_ = lean_ctor_get(v_s_342_, 19);
v_toIntTermMap_364_ = lean_ctor_get(v_s_342_, 20);
v_toIntVarMap_365_ = lean_ctor_get(v_s_342_, 21);
v_usedCommRing_366_ = lean_ctor_get_uint8(v_s_342_, sizeof(void*)*23 + 1);
v_nonlinearOccs_367_ = lean_ctor_get(v_s_342_, 22);
v_isSharedCheck_376_ = !lean_is_exclusive(v_s_342_);
if (v_isSharedCheck_376_ == 0)
{
v___x_369_ = v_s_342_;
v_isShared_370_ = v_isSharedCheck_376_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_nonlinearOccs_367_);
lean_inc(v_toIntVarMap_365_);
lean_inc(v_toIntTermMap_364_);
lean_inc(v_toIntInfos_363_);
lean_inc(v_toIntIds_362_);
lean_inc(v_divMod_361_);
lean_inc(v_diseqSplits_360_);
lean_inc(v_conflict_x3f_359_);
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
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_376_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_374_; 
v___x_371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_371_, 0, v_x_339_);
lean_ctor_set(v___x_371_, 1, v___y_340_);
v___x_372_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0___redArg(v_nonlinearOccs_367_, v_a_341_, v___x_371_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 22, v___x_372_);
v___x_374_ = v___x_369_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_vars_343_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v_varMap_344_);
lean_ctor_set(v_reuseFailAlloc_375_, 2, v_vars_x27_345_);
lean_ctor_set(v_reuseFailAlloc_375_, 3, v_varMap_x27_346_);
lean_ctor_set(v_reuseFailAlloc_375_, 4, v_natToIntMap_347_);
lean_ctor_set(v_reuseFailAlloc_375_, 5, v_natDef_348_);
lean_ctor_set(v_reuseFailAlloc_375_, 6, v_dvds_349_);
lean_ctor_set(v_reuseFailAlloc_375_, 7, v_lowers_350_);
lean_ctor_set(v_reuseFailAlloc_375_, 8, v_uppers_351_);
lean_ctor_set(v_reuseFailAlloc_375_, 9, v_diseqs_352_);
lean_ctor_set(v_reuseFailAlloc_375_, 10, v_elimEqs_353_);
lean_ctor_set(v_reuseFailAlloc_375_, 11, v_elimStack_354_);
lean_ctor_set(v_reuseFailAlloc_375_, 12, v_occurs_355_);
lean_ctor_set(v_reuseFailAlloc_375_, 13, v_assignment_356_);
lean_ctor_set(v_reuseFailAlloc_375_, 14, v_nextCnstrId_357_);
lean_ctor_set(v_reuseFailAlloc_375_, 15, v_conflict_x3f_359_);
lean_ctor_set(v_reuseFailAlloc_375_, 16, v_diseqSplits_360_);
lean_ctor_set(v_reuseFailAlloc_375_, 17, v_divMod_361_);
lean_ctor_set(v_reuseFailAlloc_375_, 18, v_toIntIds_362_);
lean_ctor_set(v_reuseFailAlloc_375_, 19, v_toIntInfos_363_);
lean_ctor_set(v_reuseFailAlloc_375_, 20, v_toIntTermMap_364_);
lean_ctor_set(v_reuseFailAlloc_375_, 21, v_toIntVarMap_365_);
lean_ctor_set(v_reuseFailAlloc_375_, 22, v___x_372_);
lean_ctor_set_uint8(v_reuseFailAlloc_375_, sizeof(void*)*23, v_caseSplits_358_);
lean_ctor_set_uint8(v_reuseFailAlloc_375_, sizeof(void*)*23 + 1, v_usedCommRing_366_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5___redArg(lean_object* v_keys_377_, lean_object* v_vals_378_, lean_object* v_i_379_, lean_object* v_k_380_){
_start:
{
lean_object* v___x_381_; uint8_t v___x_382_; 
v___x_381_ = lean_array_get_size(v_keys_377_);
v___x_382_ = lean_nat_dec_lt(v_i_379_, v___x_381_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; 
lean_dec(v_i_379_);
v___x_383_ = lean_box(0);
return v___x_383_;
}
else
{
lean_object* v_k_x27_384_; uint8_t v___x_385_; 
v_k_x27_384_ = lean_array_fget_borrowed(v_keys_377_, v_i_379_);
v___x_385_ = lean_nat_dec_eq(v_k_380_, v_k_x27_384_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_386_ = lean_unsigned_to_nat(1u);
v___x_387_ = lean_nat_add(v_i_379_, v___x_386_);
lean_dec(v_i_379_);
v_i_379_ = v___x_387_;
goto _start;
}
else
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = lean_array_fget_borrowed(v_vals_378_, v_i_379_);
lean_dec(v_i_379_);
lean_inc(v___x_389_);
v___x_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
return v___x_390_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_keys_391_, lean_object* v_vals_392_, lean_object* v_i_393_, lean_object* v_k_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5___redArg(v_keys_391_, v_vals_392_, v_i_393_, v_k_394_);
lean_dec(v_k_394_);
lean_dec_ref(v_vals_392_);
lean_dec_ref(v_keys_391_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2___redArg(lean_object* v_x_396_, size_t v_x_397_, lean_object* v_x_398_){
_start:
{
if (lean_obj_tag(v_x_396_) == 0)
{
lean_object* v_es_399_; lean_object* v___x_400_; size_t v___x_401_; size_t v___x_402_; lean_object* v_j_403_; lean_object* v___x_404_; 
v_es_399_ = lean_ctor_get(v_x_396_, 0);
v___x_400_ = lean_box(2);
v___x_401_ = ((size_t)31ULL);
v___x_402_ = lean_usize_land(v_x_397_, v___x_401_);
v_j_403_ = lean_usize_to_nat(v___x_402_);
v___x_404_ = lean_array_get_borrowed(v___x_400_, v_es_399_, v_j_403_);
lean_dec(v_j_403_);
switch(lean_obj_tag(v___x_404_))
{
case 0:
{
lean_object* v_key_405_; lean_object* v_val_406_; uint8_t v___x_407_; 
v_key_405_ = lean_ctor_get(v___x_404_, 0);
v_val_406_ = lean_ctor_get(v___x_404_, 1);
v___x_407_ = lean_nat_dec_eq(v_x_398_, v_key_405_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; 
v___x_408_ = lean_box(0);
return v___x_408_;
}
else
{
lean_object* v___x_409_; 
lean_inc(v_val_406_);
v___x_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_409_, 0, v_val_406_);
return v___x_409_;
}
}
case 1:
{
lean_object* v_node_410_; size_t v___x_411_; size_t v___x_412_; 
v_node_410_ = lean_ctor_get(v___x_404_, 0);
v___x_411_ = ((size_t)5ULL);
v___x_412_ = lean_usize_shift_right(v_x_397_, v___x_411_);
v_x_396_ = v_node_410_;
v_x_397_ = v___x_412_;
goto _start;
}
default: 
{
lean_object* v___x_414_; 
v___x_414_ = lean_box(0);
return v___x_414_;
}
}
}
else
{
lean_object* v_ks_415_; lean_object* v_vs_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v_ks_415_ = lean_ctor_get(v_x_396_, 0);
v_vs_416_ = lean_ctor_get(v_x_396_, 1);
v___x_417_ = lean_unsigned_to_nat(0u);
v___x_418_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5___redArg(v_ks_415_, v_vs_416_, v___x_417_, v_x_398_);
return v___x_418_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2___redArg___boxed(lean_object* v_x_419_, lean_object* v_x_420_, lean_object* v_x_421_){
_start:
{
size_t v_x_9244__boxed_422_; lean_object* v_res_423_; 
v_x_9244__boxed_422_ = lean_unbox_usize(v_x_420_);
lean_dec(v_x_420_);
v_res_423_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2___redArg(v_x_419_, v_x_9244__boxed_422_, v_x_421_);
lean_dec(v_x_421_);
lean_dec_ref(v_x_419_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___redArg(lean_object* v_x_424_, lean_object* v_x_425_){
_start:
{
uint64_t v___x_426_; size_t v___x_427_; lean_object* v___x_428_; 
v___x_426_ = lean_uint64_of_nat(v_x_425_);
v___x_427_ = lean_uint64_to_usize(v___x_426_);
v___x_428_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2___redArg(v_x_424_, v___x_427_, v_x_425_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___redArg___boxed(lean_object* v_x_429_, lean_object* v_x_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___redArg(v_x_429_, v_x_430_);
lean_dec(v_x_430_);
lean_dec_ref(v_x_429_);
return v_res_431_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___closed__0(void){
_start:
{
lean_object* v___x_432_; lean_object* v___f_433_; 
v___x_432_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_433_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_433_, 0, v___x_432_);
return v___f_433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(lean_object* v_arg_434_, lean_object* v_x_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_){
_start:
{
lean_object* v___x_447_; 
lean_inc(v_a_445_);
lean_inc_ref(v_a_444_);
lean_inc(v_a_443_);
lean_inc_ref(v_a_442_);
lean_inc(v_a_441_);
lean_inc_ref(v_a_440_);
lean_inc(v_a_439_);
lean_inc_ref(v_a_438_);
lean_inc(v_a_437_);
lean_inc(v_a_436_);
v___x_447_ = lean_grind_cutsat_mk_var(v_arg_434_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_519_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_519_ == 0)
{
v___x_450_ = v___x_447_;
v_isShared_451_ = v_isSharedCheck_519_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_447_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_519_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___y_453_; lean_object* v___y_454_; lean_object* v___y_455_; lean_object* v___y_465_; lean_object* v___y_466_; lean_object* v___x_482_; 
v___x_482_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_436_, v_a_444_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; lean_object* v___y_485_; lean_object* v_elimEqs_505_; lean_object* v_size_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
lean_inc(v_a_483_);
lean_dec_ref_known(v___x_482_, 1);
v_elimEqs_505_ = lean_ctor_get(v_a_483_, 10);
lean_inc_ref(v_elimEqs_505_);
lean_dec(v_a_483_);
v_size_506_ = lean_ctor_get(v_elimEqs_505_, 2);
v___x_507_ = lean_box(0);
v___x_508_ = lean_nat_dec_lt(v_a_448_, v_size_506_);
if (v___x_508_ == 0)
{
lean_object* v___x_509_; 
lean_dec_ref(v_elimEqs_505_);
v___x_509_ = l_outOfBounds___redArg(v___x_507_);
v___y_485_ = v___x_509_;
goto v___jp_484_;
}
else
{
lean_object* v___x_510_; 
v___x_510_ = l_Lean_PersistentArray_get_x21___redArg(v___x_507_, v_elimEqs_505_, v_a_448_);
lean_dec_ref(v_elimEqs_505_);
v___y_485_ = v___x_510_;
goto v___jp_484_;
}
v___jp_484_:
{
if (lean_obj_tag(v___y_485_) == 0)
{
v___y_465_ = v_a_436_;
v___y_466_ = v_a_444_;
goto v___jp_464_;
}
else
{
lean_object* v___x_486_; 
lean_dec_ref_known(v___y_485_, 1);
lean_inc(v_a_445_);
lean_inc_ref(v_a_444_);
lean_inc(v_a_443_);
lean_inc_ref(v_a_442_);
lean_inc(v_a_441_);
lean_inc_ref(v_a_440_);
lean_inc(v_a_439_);
lean_inc_ref(v_a_438_);
lean_inc(v_a_437_);
lean_inc(v_a_436_);
lean_inc(v_x_435_);
lean_inc(v_a_448_);
v___x_486_ = lean_cutsat_propagate_nonlinear(v_a_448_, v_x_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_);
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
v___y_465_ = v_a_436_;
v___y_466_ = v_a_444_;
goto v___jp_464_;
}
else
{
lean_object* v___x_492_; lean_object* v___x_494_; 
lean_del_object(v___x_450_);
lean_dec(v_a_448_);
lean_dec(v_x_435_);
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
lean_del_object(v___x_450_);
lean_dec(v_a_448_);
lean_dec(v_x_435_);
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
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
lean_del_object(v___x_450_);
lean_dec(v_a_448_);
lean_dec(v_x_435_);
v_a_511_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_518_ == 0)
{
v___x_513_ = v___x_482_;
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_482_);
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
v___jp_452_:
{
uint8_t v___x_456_; 
lean_inc(v___y_455_);
lean_inc(v_x_435_);
lean_inc_ref(v___y_454_);
v___x_456_ = l_List_elem___redArg(v___y_454_, v_x_435_, v___y_455_);
if (v___x_456_ == 0)
{
lean_object* v___f_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
lean_del_object(v___x_450_);
v___f_457_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___lam__0), 4, 3);
lean_closure_set(v___f_457_, 0, v_x_435_);
lean_closure_set(v___f_457_, 1, v___y_455_);
lean_closure_set(v___f_457_, 2, v_a_448_);
v___x_458_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_459_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_458_, v___f_457_, v___y_453_);
return v___x_459_;
}
else
{
lean_object* v___x_460_; lean_object* v___x_462_; 
lean_dec(v___y_455_);
lean_dec(v_a_448_);
lean_dec(v_x_435_);
v___x_460_ = lean_box(0);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v___x_460_);
v___x_462_ = v___x_450_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_460_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
v___jp_464_:
{
lean_object* v___x_467_; 
v___x_467_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v___y_465_, v___y_466_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v_a_468_; lean_object* v_nonlinearOccs_469_; lean_object* v___f_470_; lean_object* v___x_471_; 
v_a_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_a_468_);
lean_dec_ref_known(v___x_467_, 1);
v_nonlinearOccs_469_ = lean_ctor_get(v_a_468_, 22);
lean_inc_ref(v_nonlinearOccs_469_);
lean_dec(v_a_468_);
v___f_470_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___closed__0);
v___x_471_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___redArg(v_nonlinearOccs_469_, v_a_448_);
lean_dec_ref(v_nonlinearOccs_469_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v___x_472_; 
v___x_472_ = lean_box(0);
v___y_453_ = v___y_465_;
v___y_454_ = v___f_470_;
v___y_455_ = v___x_472_;
goto v___jp_452_;
}
else
{
lean_object* v_val_473_; 
v_val_473_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_val_473_);
lean_dec_ref_known(v___x_471_, 1);
v___y_453_ = v___y_465_;
v___y_454_ = v___f_470_;
v___y_455_ = v_val_473_;
goto v___jp_452_;
}
}
else
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_481_; 
lean_del_object(v___x_450_);
lean_dec(v_a_448_);
lean_dec(v_x_435_);
v_a_474_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_481_ == 0)
{
v___x_476_ = v___x_467_;
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_467_);
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
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_527_; 
lean_dec(v_x_435_);
v_a_520_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_527_ == 0)
{
v___x_522_ = v___x_447_;
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_447_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1(lean_object* v_00_u03b2_547_, lean_object* v_x_548_, lean_object* v_x_549_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___redArg(v_x_548_, v_x_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___boxed(lean_object* v_00_u03b2_551_, lean_object* v_x_552_, lean_object* v_x_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1(v_00_u03b2_551_, v_x_552_, v_x_553_);
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
size_t v_x_9485__boxed_568_; size_t v_x_9486__boxed_569_; lean_object* v_res_570_; 
v_x_9485__boxed_568_ = lean_unbox_usize(v_x_564_);
lean_dec(v_x_564_);
v_x_9486__boxed_569_ = lean_unbox_usize(v_x_565_);
lean_dec(v_x_565_);
v_res_570_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0(v_00_u03b2_562_, v_x_563_, v_x_9485__boxed_568_, v_x_9486__boxed_569_, v_x_566_, v_x_567_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2(lean_object* v_00_u03b2_571_, lean_object* v_x_572_, size_t v_x_573_, lean_object* v_x_574_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2___redArg(v_x_572_, v_x_573_, v_x_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2___boxed(lean_object* v_00_u03b2_576_, lean_object* v_x_577_, lean_object* v_x_578_, lean_object* v_x_579_){
_start:
{
size_t v_x_9502__boxed_580_; lean_object* v_res_581_; 
v_x_9502__boxed_580_ = lean_unbox_usize(v_x_578_);
lean_dec(v_x_578_);
v_res_581_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2(v_00_u03b2_576_, v_x_577_, v_x_9502__boxed_580_, v_x_579_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_604_, lean_object* v_keys_605_, lean_object* v_vals_606_, lean_object* v_heq_607_, lean_object* v_i_608_, lean_object* v_k_609_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5___redArg(v_keys_605_, v_vals_606_, v_i_608_, v_k_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_611_, lean_object* v_keys_612_, lean_object* v_vals_613_, lean_object* v_heq_614_, lean_object* v_i_615_, lean_object* v_k_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5(v_00_u03b2_611_, v_keys_612_, v_vals_613_, v_heq_614_, v_i_615_, v_k_616_);
lean_dec(v_k_616_);
lean_dec_ref(v_vals_613_);
lean_dec_ref(v_keys_612_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_618_, lean_object* v_x_619_, lean_object* v_x_620_, lean_object* v_x_621_, lean_object* v_x_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__3___redArg(v_x_619_, v_x_620_, v_x_621_, v_x_622_);
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
lean_object* v___x_716_; 
v___x_716_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_700_, v_a_709_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_819_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_819_ == 0)
{
v___x_719_ = v___x_716_;
v_isShared_720_ = v_isSharedCheck_819_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_716_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_819_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_726_ = l_Lean_Expr_cleanupAnnotations(v_a_717_);
v___x_727_ = l_Lean_Expr_isApp(v___x_726_);
if (v___x_727_ == 0)
{
lean_dec_ref(v___x_726_);
lean_dec(v_x_701_);
goto v___jp_721_;
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
lean_dec(v_x_701_);
goto v___jp_721_;
}
else
{
lean_object* v_arg_731_; lean_object* v___x_732_; uint8_t v___x_733_; 
v_arg_731_ = lean_ctor_get(v___x_729_, 1);
lean_inc_ref(v_arg_731_);
v___x_732_ = l_Lean_Expr_appFnCleanup___redArg(v___x_729_);
v___x_733_ = l_Lean_Expr_isApp(v___x_732_);
if (v___x_733_ == 0)
{
lean_dec_ref(v___x_732_);
lean_dec_ref(v_arg_731_);
lean_dec_ref(v_arg_728_);
lean_dec(v_x_701_);
goto v___jp_721_;
}
else
{
lean_object* v___x_734_; uint8_t v___x_735_; 
v___x_734_ = l_Lean_Expr_appFnCleanup___redArg(v___x_732_);
v___x_735_ = l_Lean_Expr_isApp(v___x_734_);
if (v___x_735_ == 0)
{
lean_dec_ref(v___x_734_);
lean_dec_ref(v_arg_731_);
lean_dec_ref(v_arg_728_);
lean_dec(v_x_701_);
goto v___jp_721_;
}
else
{
lean_object* v___x_736_; uint8_t v___x_737_; 
v___x_736_ = l_Lean_Expr_appFnCleanup___redArg(v___x_734_);
v___x_737_ = l_Lean_Expr_isApp(v___x_736_);
if (v___x_737_ == 0)
{
lean_dec_ref(v___x_736_);
lean_dec_ref(v_arg_731_);
lean_dec_ref(v_arg_728_);
lean_dec(v_x_701_);
goto v___jp_721_;
}
else
{
lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_738_ = l_Lean_Expr_appFnCleanup___redArg(v___x_736_);
v___x_739_ = l_Lean_Expr_isApp(v___x_738_);
if (v___x_739_ == 0)
{
lean_dec_ref(v___x_738_);
lean_dec_ref(v_arg_731_);
lean_dec_ref(v_arg_728_);
lean_dec(v_x_701_);
goto v___jp_721_;
}
else
{
lean_object* v___x_740_; lean_object* v___x_741_; uint8_t v___x_742_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; 
v___x_740_ = l_Lean_Expr_appFnCleanup___redArg(v___x_738_);
v___x_741_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__2));
v___x_742_ = l_Lean_Expr_isConstOf(v___x_740_, v___x_741_);
if (v___x_742_ == 0)
{
lean_object* v___x_798_; uint8_t v___x_799_; 
v___x_798_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__5));
v___x_799_ = l_Lean_Expr_isConstOf(v___x_740_, v___x_798_);
if (v___x_799_ == 0)
{
lean_object* v___x_800_; uint8_t v___x_801_; 
v___x_800_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__8));
v___x_801_ = l_Lean_Expr_isConstOf(v___x_740_, v___x_800_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; uint8_t v___x_803_; 
v___x_802_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11));
v___x_803_ = l_Lean_Expr_isConstOf(v___x_740_, v___x_802_);
lean_dec_ref(v___x_740_);
if (v___x_803_ == 0)
{
lean_dec_ref(v_arg_731_);
lean_dec_ref(v_arg_728_);
lean_dec(v_x_701_);
goto v___jp_721_;
}
else
{
lean_object* v___x_804_; 
lean_del_object(v___x_719_);
lean_inc(v_x_701_);
v___x_804_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(v_x_701_, v_arg_731_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_object* v___x_805_; 
lean_dec_ref_known(v___x_804_, 1);
v___x_805_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(v_x_701_, v_arg_728_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
return v___x_805_;
}
else
{
lean_dec_ref(v_arg_728_);
lean_dec(v_x_701_);
return v___x_804_;
}
}
}
else
{
lean_object* v___x_806_; 
lean_dec_ref(v___x_740_);
lean_dec_ref(v_arg_731_);
lean_del_object(v___x_719_);
v___x_806_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_arg_728_, v_x_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
return v___x_806_;
}
}
else
{
lean_object* v___x_807_; 
lean_dec_ref(v___x_740_);
lean_dec_ref(v_arg_731_);
lean_del_object(v___x_719_);
v___x_807_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_arg_728_, v_x_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
return v___x_807_;
}
}
else
{
lean_object* v___x_808_; 
lean_dec_ref(v___x_740_);
lean_del_object(v___x_719_);
lean_inc_ref(v_arg_731_);
v___x_808_ = l_Lean_Meta_getIntValue_x3f(v_arg_731_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_a_809_);
lean_dec_ref_known(v___x_808_, 1);
if (lean_obj_tag(v_a_809_) == 0)
{
if (v___x_742_ == 0)
{
lean_dec_ref(v_arg_731_);
v___y_744_ = v_a_702_;
v___y_745_ = v_a_703_;
v___y_746_ = v_a_704_;
v___y_747_ = v_a_705_;
v___y_748_ = v_a_706_;
v___y_749_ = v_a_707_;
v___y_750_ = v_a_708_;
v___y_751_ = v_a_709_;
v___y_752_ = v_a_710_;
v___y_753_ = v_a_711_;
goto v___jp_743_;
}
else
{
lean_object* v___x_810_; 
lean_inc(v_x_701_);
v___x_810_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_arg_731_, v_x_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_dec_ref_known(v___x_810_, 1);
v___y_744_ = v_a_702_;
v___y_745_ = v_a_703_;
v___y_746_ = v_a_704_;
v___y_747_ = v_a_705_;
v___y_748_ = v_a_706_;
v___y_749_ = v_a_707_;
v___y_750_ = v_a_708_;
v___y_751_ = v_a_709_;
v___y_752_ = v_a_710_;
v___y_753_ = v_a_711_;
goto v___jp_743_;
}
else
{
lean_dec_ref(v_arg_728_);
lean_dec(v_x_701_);
return v___x_810_;
}
}
}
else
{
lean_dec_ref_known(v_a_809_, 1);
lean_dec_ref(v_arg_731_);
v___y_744_ = v_a_702_;
v___y_745_ = v_a_703_;
v___y_746_ = v_a_704_;
v___y_747_ = v_a_705_;
v___y_748_ = v_a_706_;
v___y_749_ = v_a_707_;
v___y_750_ = v_a_708_;
v___y_751_ = v_a_709_;
v___y_752_ = v_a_710_;
v___y_753_ = v_a_711_;
goto v___jp_743_;
}
}
else
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_818_; 
lean_dec_ref(v_arg_731_);
lean_dec_ref(v_arg_728_);
lean_dec(v_x_701_);
v_a_811_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_818_ == 0)
{
v___x_813_ = v___x_808_;
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_808_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_a_811_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
v___jp_743_:
{
lean_object* v___x_754_; 
lean_inc_ref(v_arg_728_);
v___x_754_ = l_Lean_Meta_getIntValue_x3f(v_arg_728_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v_a_755_; lean_object* v___x_756_; 
v_a_755_ = lean_ctor_get(v___x_754_, 0);
lean_inc(v_a_755_);
lean_dec_ref_known(v___x_754_, 1);
v___x_756_ = l_Lean_Meta_getNatValue_x3f(v_arg_728_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
if (lean_obj_tag(v___x_756_) == 0)
{
if (lean_obj_tag(v_a_755_) == 0)
{
if (v___x_742_ == 0)
{
lean_dec_ref_known(v___x_756_, 1);
lean_dec_ref(v_arg_728_);
lean_dec(v_x_701_);
goto v___jp_713_;
}
else
{
lean_object* v_a_757_; 
v_a_757_ = lean_ctor_get(v___x_756_, 0);
lean_inc(v_a_757_);
lean_dec_ref_known(v___x_756_, 1);
if (lean_obj_tag(v_a_757_) == 0)
{
lean_object* v___x_758_; 
lean_inc_ref(v_arg_728_);
v___x_758_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_arg_728_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; lean_object* v_fst_760_; lean_object* v___x_761_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_a_759_);
lean_dec_ref_known(v___x_758_, 1);
v_fst_760_ = lean_ctor_get(v_a_759_, 0);
lean_inc(v_fst_760_);
lean_dec(v_a_759_);
v___x_761_ = l_Lean_Meta_Grind_getGeneration___redArg(v_arg_728_, v___y_744_);
lean_dec_ref(v_arg_728_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_a_762_);
lean_dec_ref_known(v___x_761_, 1);
v___x_763_ = lean_box(0);
lean_inc(v___y_753_);
lean_inc_ref(v___y_752_);
lean_inc(v___y_751_);
lean_inc_ref(v___y_750_);
lean_inc(v___y_749_);
lean_inc_ref(v___y_748_);
lean_inc(v___y_747_);
lean_inc_ref(v___y_746_);
lean_inc(v___y_745_);
lean_inc(v___y_744_);
lean_inc(v_fst_760_);
v___x_764_ = lean_grind_internalize(v_fst_760_, v_a_762_, v___x_763_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v___x_765_; 
lean_dec_ref_known(v___x_764_, 1);
v___x_765_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_fst_760_, v_x_701_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
return v___x_765_;
}
else
{
lean_dec(v_fst_760_);
lean_dec(v_x_701_);
return v___x_764_;
}
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_dec(v_fst_760_);
lean_dec(v_x_701_);
v_a_766_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_761_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_761_);
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
else
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
lean_dec_ref(v_arg_728_);
lean_dec(v_x_701_);
v_a_774_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_781_ == 0)
{
v___x_776_ = v___x_758_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_758_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_774_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_757_, 1);
lean_dec_ref(v_arg_728_);
lean_dec(v_x_701_);
goto v___jp_713_;
}
}
}
else
{
lean_dec_ref_known(v_a_755_, 1);
lean_dec_ref_known(v___x_756_, 1);
lean_dec_ref(v_arg_728_);
lean_dec(v_x_701_);
goto v___jp_713_;
}
}
else
{
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_789_; 
lean_dec(v_a_755_);
lean_dec_ref(v_arg_728_);
lean_dec(v_x_701_);
v_a_782_ = lean_ctor_get(v___x_756_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_789_ == 0)
{
v___x_784_ = v___x_756_;
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___x_756_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_787_; 
if (v_isShared_785_ == 0)
{
v___x_787_ = v___x_784_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_a_782_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
else
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
lean_dec_ref(v_arg_728_);
lean_dec(v_x_701_);
v_a_790_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_754_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_754_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
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
v___jp_721_:
{
lean_object* v___x_722_; lean_object* v___x_724_; 
v___x_722_ = lean_box(0);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 0, v___x_722_);
v___x_724_ = v___x_719_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_722_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
else
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
lean_dec(v_x_701_);
v_a_820_ = lean_ctor_get(v___x_716_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_827_ == 0)
{
v___x_822_ = v___x_716_;
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_716_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_a_820_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt___boxed(lean_object* v_e_828_, lean_object* v_x_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt(v_e_828_, v_x_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_);
lean_dec(v_a_839_);
lean_dec_ref(v_a_838_);
lean_dec(v_a_837_);
lean_dec_ref(v_a_836_);
lean_dec(v_a_835_);
lean_dec_ref(v_a_834_);
lean_dec(v_a_833_);
lean_dec_ref(v_a_832_);
lean_dec(v_a_831_);
lean_dec(v_a_830_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_x_842_, lean_object* v_x_843_, lean_object* v_x_844_, lean_object* v_x_845_){
_start:
{
lean_object* v_ks_846_; lean_object* v_vs_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_871_; 
v_ks_846_ = lean_ctor_get(v_x_842_, 0);
v_vs_847_ = lean_ctor_get(v_x_842_, 1);
v_isSharedCheck_871_ = !lean_is_exclusive(v_x_842_);
if (v_isSharedCheck_871_ == 0)
{
v___x_849_ = v_x_842_;
v_isShared_850_ = v_isSharedCheck_871_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_vs_847_);
lean_inc(v_ks_846_);
lean_dec(v_x_842_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_871_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_851_; uint8_t v___x_852_; 
v___x_851_ = lean_array_get_size(v_ks_846_);
v___x_852_ = lean_nat_dec_lt(v_x_843_, v___x_851_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_856_; 
lean_dec(v_x_843_);
v___x_853_ = lean_array_push(v_ks_846_, v_x_844_);
v___x_854_ = lean_array_push(v_vs_847_, v_x_845_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 1, v___x_854_);
lean_ctor_set(v___x_849_, 0, v___x_853_);
v___x_856_ = v___x_849_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_853_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v___x_854_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
else
{
lean_object* v_k_x27_858_; uint8_t v___x_859_; 
v_k_x27_858_ = lean_array_fget_borrowed(v_ks_846_, v_x_843_);
v___x_859_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_844_, v_k_x27_858_);
if (v___x_859_ == 0)
{
lean_object* v___x_861_; 
if (v_isShared_850_ == 0)
{
v___x_861_ = v___x_849_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_ks_846_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_vs_847_);
v___x_861_ = v_reuseFailAlloc_865_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = lean_unsigned_to_nat(1u);
v___x_863_ = lean_nat_add(v_x_843_, v___x_862_);
lean_dec(v_x_843_);
v_x_842_ = v___x_861_;
v_x_843_ = v___x_863_;
goto _start;
}
}
else
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_869_; 
v___x_866_ = lean_array_fset(v_ks_846_, v_x_843_, v_x_844_);
v___x_867_ = lean_array_fset(v_vs_847_, v_x_843_, v_x_845_);
lean_dec(v_x_843_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 1, v___x_867_);
lean_ctor_set(v___x_849_, 0, v___x_866_);
v___x_869_ = v___x_849_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_866_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v___x_867_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4___redArg(lean_object* v_n_872_, lean_object* v_k_873_, lean_object* v_v_874_){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = lean_unsigned_to_nat(0u);
v___x_876_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7___redArg(v_n_872_, v___x_875_, v_k_873_, v_v_874_);
return v___x_876_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(lean_object* v_x_878_, size_t v_x_879_, size_t v_x_880_, lean_object* v_x_881_, lean_object* v_x_882_){
_start:
{
if (lean_obj_tag(v_x_878_) == 0)
{
lean_object* v_es_883_; size_t v___x_884_; size_t v___x_885_; lean_object* v_j_886_; lean_object* v___x_887_; uint8_t v___x_888_; 
v_es_883_ = lean_ctor_get(v_x_878_, 0);
v___x_884_ = ((size_t)31ULL);
v___x_885_ = lean_usize_land(v_x_879_, v___x_884_);
v_j_886_ = lean_usize_to_nat(v___x_885_);
v___x_887_ = lean_array_get_size(v_es_883_);
v___x_888_ = lean_nat_dec_lt(v_j_886_, v___x_887_);
if (v___x_888_ == 0)
{
lean_dec(v_j_886_);
lean_dec(v_x_882_);
lean_dec_ref(v_x_881_);
return v_x_878_;
}
else
{
lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_927_; 
lean_inc_ref(v_es_883_);
v_isSharedCheck_927_ = !lean_is_exclusive(v_x_878_);
if (v_isSharedCheck_927_ == 0)
{
lean_object* v_unused_928_; 
v_unused_928_ = lean_ctor_get(v_x_878_, 0);
lean_dec(v_unused_928_);
v___x_890_ = v_x_878_;
v_isShared_891_ = v_isSharedCheck_927_;
goto v_resetjp_889_;
}
else
{
lean_dec(v_x_878_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_927_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v_v_892_; lean_object* v___x_893_; lean_object* v_xs_x27_894_; lean_object* v___y_896_; 
v_v_892_ = lean_array_fget(v_es_883_, v_j_886_);
v___x_893_ = lean_box(0);
v_xs_x27_894_ = lean_array_fset(v_es_883_, v_j_886_, v___x_893_);
switch(lean_obj_tag(v_v_892_))
{
case 0:
{
lean_object* v_key_901_; lean_object* v_val_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_912_; 
v_key_901_ = lean_ctor_get(v_v_892_, 0);
v_val_902_ = lean_ctor_get(v_v_892_, 1);
v_isSharedCheck_912_ = !lean_is_exclusive(v_v_892_);
if (v_isSharedCheck_912_ == 0)
{
v___x_904_ = v_v_892_;
v_isShared_905_ = v_isSharedCheck_912_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_val_902_);
lean_inc(v_key_901_);
lean_dec(v_v_892_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_912_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
uint8_t v___x_906_; 
v___x_906_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_881_, v_key_901_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; lean_object* v___x_908_; 
lean_del_object(v___x_904_);
v___x_907_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_901_, v_val_902_, v_x_881_, v_x_882_);
v___x_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_908_, 0, v___x_907_);
v___y_896_ = v___x_908_;
goto v___jp_895_;
}
else
{
lean_object* v___x_910_; 
lean_dec(v_val_902_);
lean_dec(v_key_901_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 1, v_x_882_);
lean_ctor_set(v___x_904_, 0, v_x_881_);
v___x_910_ = v___x_904_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_x_881_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v_x_882_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
v___y_896_ = v___x_910_;
goto v___jp_895_;
}
}
}
}
case 1:
{
lean_object* v_node_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_925_; 
v_node_913_ = lean_ctor_get(v_v_892_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v_v_892_);
if (v_isSharedCheck_925_ == 0)
{
v___x_915_ = v_v_892_;
v_isShared_916_ = v_isSharedCheck_925_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_node_913_);
lean_dec(v_v_892_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_925_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
size_t v___x_917_; size_t v___x_918_; size_t v___x_919_; size_t v___x_920_; lean_object* v___x_921_; lean_object* v___x_923_; 
v___x_917_ = ((size_t)5ULL);
v___x_918_ = lean_usize_shift_right(v_x_879_, v___x_917_);
v___x_919_ = ((size_t)1ULL);
v___x_920_ = lean_usize_add(v_x_880_, v___x_919_);
v___x_921_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_node_913_, v___x_918_, v___x_920_, v_x_881_, v_x_882_);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 0, v___x_921_);
v___x_923_ = v___x_915_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
v___y_896_ = v___x_923_;
goto v___jp_895_;
}
}
}
default: 
{
lean_object* v___x_926_; 
v___x_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_926_, 0, v_x_881_);
lean_ctor_set(v___x_926_, 1, v_x_882_);
v___y_896_ = v___x_926_;
goto v___jp_895_;
}
}
v___jp_895_:
{
lean_object* v___x_897_; lean_object* v___x_899_; 
v___x_897_ = lean_array_fset(v_xs_x27_894_, v_j_886_, v___y_896_);
lean_dec(v_j_886_);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 0, v___x_897_);
v___x_899_ = v___x_890_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_897_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
}
else
{
lean_object* v_ks_929_; lean_object* v_vs_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_950_; 
v_ks_929_ = lean_ctor_get(v_x_878_, 0);
v_vs_930_ = lean_ctor_get(v_x_878_, 1);
v_isSharedCheck_950_ = !lean_is_exclusive(v_x_878_);
if (v_isSharedCheck_950_ == 0)
{
v___x_932_ = v_x_878_;
v_isShared_933_ = v_isSharedCheck_950_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_vs_930_);
lean_inc(v_ks_929_);
lean_dec(v_x_878_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_950_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
if (v_isShared_933_ == 0)
{
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_ks_929_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_vs_930_);
v___x_935_ = v_reuseFailAlloc_949_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
lean_object* v_newNode_936_; uint8_t v___y_938_; size_t v___x_944_; uint8_t v___x_945_; 
v_newNode_936_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4___redArg(v___x_935_, v_x_881_, v_x_882_);
v___x_944_ = ((size_t)7ULL);
v___x_945_ = lean_usize_dec_le(v___x_944_, v_x_880_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; lean_object* v___x_947_; uint8_t v___x_948_; 
v___x_946_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_936_);
v___x_947_ = lean_unsigned_to_nat(4u);
v___x_948_ = lean_nat_dec_lt(v___x_946_, v___x_947_);
lean_dec(v___x_946_);
v___y_938_ = v___x_948_;
goto v___jp_937_;
}
else
{
v___y_938_ = v___x_945_;
goto v___jp_937_;
}
v___jp_937_:
{
if (v___y_938_ == 0)
{
lean_object* v_ks_939_; lean_object* v_vs_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v_ks_939_ = lean_ctor_get(v_newNode_936_, 0);
lean_inc_ref(v_ks_939_);
v_vs_940_ = lean_ctor_get(v_newNode_936_, 1);
lean_inc_ref(v_vs_940_);
lean_dec_ref(v_newNode_936_);
v___x_941_ = lean_unsigned_to_nat(0u);
v___x_942_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg___closed__0);
v___x_943_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(v_x_880_, v_ks_939_, v_vs_940_, v___x_941_, v___x_942_);
lean_dec_ref(v_vs_940_);
lean_dec_ref(v_ks_939_);
return v___x_943_;
}
else
{
return v_newNode_936_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(size_t v_depth_951_, lean_object* v_keys_952_, lean_object* v_vals_953_, lean_object* v_i_954_, lean_object* v_entries_955_){
_start:
{
lean_object* v___x_956_; uint8_t v___x_957_; 
v___x_956_ = lean_array_get_size(v_keys_952_);
v___x_957_ = lean_nat_dec_lt(v_i_954_, v___x_956_);
if (v___x_957_ == 0)
{
lean_dec(v_i_954_);
return v_entries_955_;
}
else
{
lean_object* v_k_958_; lean_object* v_v_959_; uint64_t v___x_960_; size_t v_h_961_; size_t v___x_962_; lean_object* v___x_963_; size_t v___x_964_; size_t v___x_965_; size_t v___x_966_; size_t v_h_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v_k_958_ = lean_array_fget_borrowed(v_keys_952_, v_i_954_);
v_v_959_ = lean_array_fget_borrowed(v_vals_953_, v_i_954_);
v___x_960_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_958_);
v_h_961_ = lean_uint64_to_usize(v___x_960_);
v___x_962_ = ((size_t)5ULL);
v___x_963_ = lean_unsigned_to_nat(1u);
v___x_964_ = ((size_t)1ULL);
v___x_965_ = lean_usize_sub(v_depth_951_, v___x_964_);
v___x_966_ = lean_usize_mul(v___x_962_, v___x_965_);
v_h_967_ = lean_usize_shift_right(v_h_961_, v___x_966_);
v___x_968_ = lean_nat_add(v_i_954_, v___x_963_);
lean_dec(v_i_954_);
lean_inc(v_v_959_);
lean_inc(v_k_958_);
v___x_969_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_entries_955_, v_h_967_, v_depth_951_, v_k_958_, v_v_959_);
v_i_954_ = v___x_968_;
v_entries_955_ = v___x_969_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_971_, lean_object* v_keys_972_, lean_object* v_vals_973_, lean_object* v_i_974_, lean_object* v_entries_975_){
_start:
{
size_t v_depth_boxed_976_; lean_object* v_res_977_; 
v_depth_boxed_976_ = lean_unbox_usize(v_depth_971_);
lean_dec(v_depth_971_);
v_res_977_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(v_depth_boxed_976_, v_keys_972_, v_vals_973_, v_i_974_, v_entries_975_);
lean_dec_ref(v_vals_973_);
lean_dec_ref(v_keys_972_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg___boxed(lean_object* v_x_978_, lean_object* v_x_979_, lean_object* v_x_980_, lean_object* v_x_981_, lean_object* v_x_982_){
_start:
{
size_t v_x_32812__boxed_983_; size_t v_x_32813__boxed_984_; lean_object* v_res_985_; 
v_x_32812__boxed_983_ = lean_unbox_usize(v_x_979_);
lean_dec(v_x_979_);
v_x_32813__boxed_984_ = lean_unbox_usize(v_x_980_);
lean_dec(v_x_980_);
v_res_985_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_x_978_, v_x_32812__boxed_983_, v_x_32813__boxed_984_, v_x_981_, v_x_982_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg(lean_object* v_x_986_, lean_object* v_x_987_, lean_object* v_x_988_){
_start:
{
uint64_t v___x_989_; size_t v___x_990_; size_t v___x_991_; lean_object* v___x_992_; 
v___x_989_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_987_);
v___x_990_ = lean_uint64_to_usize(v___x_989_);
v___x_991_ = ((size_t)1ULL);
v___x_992_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_x_986_, v___x_990_, v___x_991_, v_x_987_, v_x_988_);
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
lean_object* v_vars_1005_; lean_object* v_varMap_1006_; lean_object* v_vars_x27_1007_; lean_object* v_varMap_x27_1008_; lean_object* v_natToIntMap_1009_; lean_object* v_natDef_1010_; lean_object* v_dvds_1011_; lean_object* v_lowers_1012_; lean_object* v_uppers_1013_; lean_object* v_diseqs_1014_; lean_object* v_elimEqs_1015_; lean_object* v_elimStack_1016_; lean_object* v_occurs_1017_; lean_object* v_assignment_1018_; lean_object* v_nextCnstrId_1019_; uint8_t v_caseSplits_1020_; lean_object* v_conflict_x3f_1021_; lean_object* v_diseqSplits_1022_; lean_object* v_divMod_1023_; lean_object* v_toIntIds_1024_; lean_object* v_toIntInfos_1025_; lean_object* v_toIntTermMap_1026_; lean_object* v_toIntVarMap_1027_; uint8_t v_usedCommRing_1028_; lean_object* v_nonlinearOccs_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1047_; 
v_vars_1005_ = lean_ctor_get(v_s_1004_, 0);
v_varMap_1006_ = lean_ctor_get(v_s_1004_, 1);
v_vars_x27_1007_ = lean_ctor_get(v_s_1004_, 2);
v_varMap_x27_1008_ = lean_ctor_get(v_s_1004_, 3);
v_natToIntMap_1009_ = lean_ctor_get(v_s_1004_, 4);
v_natDef_1010_ = lean_ctor_get(v_s_1004_, 5);
v_dvds_1011_ = lean_ctor_get(v_s_1004_, 6);
v_lowers_1012_ = lean_ctor_get(v_s_1004_, 7);
v_uppers_1013_ = lean_ctor_get(v_s_1004_, 8);
v_diseqs_1014_ = lean_ctor_get(v_s_1004_, 9);
v_elimEqs_1015_ = lean_ctor_get(v_s_1004_, 10);
v_elimStack_1016_ = lean_ctor_get(v_s_1004_, 11);
v_occurs_1017_ = lean_ctor_get(v_s_1004_, 12);
v_assignment_1018_ = lean_ctor_get(v_s_1004_, 13);
v_nextCnstrId_1019_ = lean_ctor_get(v_s_1004_, 14);
v_caseSplits_1020_ = lean_ctor_get_uint8(v_s_1004_, sizeof(void*)*23);
v_conflict_x3f_1021_ = lean_ctor_get(v_s_1004_, 15);
v_diseqSplits_1022_ = lean_ctor_get(v_s_1004_, 16);
v_divMod_1023_ = lean_ctor_get(v_s_1004_, 17);
v_toIntIds_1024_ = lean_ctor_get(v_s_1004_, 18);
v_toIntInfos_1025_ = lean_ctor_get(v_s_1004_, 19);
v_toIntTermMap_1026_ = lean_ctor_get(v_s_1004_, 20);
v_toIntVarMap_1027_ = lean_ctor_get(v_s_1004_, 21);
v_usedCommRing_1028_ = lean_ctor_get_uint8(v_s_1004_, sizeof(void*)*23 + 1);
v_nonlinearOccs_1029_ = lean_ctor_get(v_s_1004_, 22);
v_isSharedCheck_1047_ = !lean_is_exclusive(v_s_1004_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1031_ = v_s_1004_;
v_isShared_1032_ = v_isSharedCheck_1047_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_nonlinearOccs_1029_);
lean_inc(v_toIntVarMap_1027_);
lean_inc(v_toIntTermMap_1026_);
lean_inc(v_toIntInfos_1025_);
lean_inc(v_toIntIds_1024_);
lean_inc(v_divMod_1023_);
lean_inc(v_diseqSplits_1022_);
lean_inc(v_conflict_x3f_1021_);
lean_inc(v_nextCnstrId_1019_);
lean_inc(v_assignment_1018_);
lean_inc(v_occurs_1017_);
lean_inc(v_elimStack_1016_);
lean_inc(v_elimEqs_1015_);
lean_inc(v_diseqs_1014_);
lean_inc(v_uppers_1013_);
lean_inc(v_lowers_1012_);
lean_inc(v_dvds_1011_);
lean_inc(v_natDef_1010_);
lean_inc(v_natToIntMap_1009_);
lean_inc(v_varMap_x27_1008_);
lean_inc(v_vars_x27_1007_);
lean_inc(v_varMap_1006_);
lean_inc(v_vars_1005_);
lean_dec(v_s_1004_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1047_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1045_; 
lean_inc_ref(v_expr_1002_);
v___x_1033_ = l_Lean_PersistentArray_push___redArg(v_vars_1005_, v_expr_1002_);
v___x_1034_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg(v_varMap_1006_, v_expr_1002_, v_size_1003_);
v___x_1035_ = lean_box(0);
v___x_1036_ = l_Lean_PersistentArray_push___redArg(v_dvds_1011_, v___x_1035_);
v___x_1037_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1);
v___x_1038_ = l_Lean_PersistentArray_push___redArg(v_lowers_1012_, v___x_1037_);
v___x_1039_ = l_Lean_PersistentArray_push___redArg(v_uppers_1013_, v___x_1037_);
v___x_1040_ = l_Lean_PersistentArray_push___redArg(v_diseqs_1014_, v___x_1037_);
v___x_1041_ = l_Lean_PersistentArray_push___redArg(v_elimEqs_1015_, v___x_1035_);
v___x_1042_ = lean_box(1);
v___x_1043_ = l_Lean_PersistentArray_push___redArg(v_occurs_1017_, v___x_1042_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 12, v___x_1043_);
lean_ctor_set(v___x_1031_, 10, v___x_1041_);
lean_ctor_set(v___x_1031_, 9, v___x_1040_);
lean_ctor_set(v___x_1031_, 8, v___x_1039_);
lean_ctor_set(v___x_1031_, 7, v___x_1038_);
lean_ctor_set(v___x_1031_, 6, v___x_1036_);
lean_ctor_set(v___x_1031_, 1, v___x_1034_);
lean_ctor_set(v___x_1031_, 0, v___x_1033_);
v___x_1045_ = v___x_1031_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_1033_);
lean_ctor_set(v_reuseFailAlloc_1046_, 1, v___x_1034_);
lean_ctor_set(v_reuseFailAlloc_1046_, 2, v_vars_x27_1007_);
lean_ctor_set(v_reuseFailAlloc_1046_, 3, v_varMap_x27_1008_);
lean_ctor_set(v_reuseFailAlloc_1046_, 4, v_natToIntMap_1009_);
lean_ctor_set(v_reuseFailAlloc_1046_, 5, v_natDef_1010_);
lean_ctor_set(v_reuseFailAlloc_1046_, 6, v___x_1036_);
lean_ctor_set(v_reuseFailAlloc_1046_, 7, v___x_1038_);
lean_ctor_set(v_reuseFailAlloc_1046_, 8, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1046_, 9, v___x_1040_);
lean_ctor_set(v_reuseFailAlloc_1046_, 10, v___x_1041_);
lean_ctor_set(v_reuseFailAlloc_1046_, 11, v_elimStack_1016_);
lean_ctor_set(v_reuseFailAlloc_1046_, 12, v___x_1043_);
lean_ctor_set(v_reuseFailAlloc_1046_, 13, v_assignment_1018_);
lean_ctor_set(v_reuseFailAlloc_1046_, 14, v_nextCnstrId_1019_);
lean_ctor_set(v_reuseFailAlloc_1046_, 15, v_conflict_x3f_1021_);
lean_ctor_set(v_reuseFailAlloc_1046_, 16, v_diseqSplits_1022_);
lean_ctor_set(v_reuseFailAlloc_1046_, 17, v_divMod_1023_);
lean_ctor_set(v_reuseFailAlloc_1046_, 18, v_toIntIds_1024_);
lean_ctor_set(v_reuseFailAlloc_1046_, 19, v_toIntInfos_1025_);
lean_ctor_set(v_reuseFailAlloc_1046_, 20, v_toIntTermMap_1026_);
lean_ctor_set(v_reuseFailAlloc_1046_, 21, v_toIntVarMap_1027_);
lean_ctor_set(v_reuseFailAlloc_1046_, 22, v_nonlinearOccs_1029_);
lean_ctor_set_uint8(v_reuseFailAlloc_1046_, sizeof(void*)*23, v_caseSplits_1020_);
lean_ctor_set_uint8(v_reuseFailAlloc_1046_, sizeof(void*)*23 + 1, v_usedCommRing_1028_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1048_, lean_object* v_vals_1049_, lean_object* v_i_1050_, lean_object* v_k_1051_){
_start:
{
lean_object* v___x_1052_; uint8_t v___x_1053_; 
v___x_1052_ = lean_array_get_size(v_keys_1048_);
v___x_1053_ = lean_nat_dec_lt(v_i_1050_, v___x_1052_);
if (v___x_1053_ == 0)
{
lean_object* v___x_1054_; 
lean_dec(v_i_1050_);
v___x_1054_ = lean_box(0);
return v___x_1054_;
}
else
{
lean_object* v_k_x27_1055_; uint8_t v___x_1056_; 
v_k_x27_1055_ = lean_array_fget_borrowed(v_keys_1048_, v_i_1050_);
v___x_1056_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_1051_, v_k_x27_1055_);
if (v___x_1056_ == 0)
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = lean_unsigned_to_nat(1u);
v___x_1058_ = lean_nat_add(v_i_1050_, v___x_1057_);
lean_dec(v_i_1050_);
v_i_1050_ = v___x_1058_;
goto _start;
}
else
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = lean_array_fget_borrowed(v_vals_1049_, v_i_1050_);
lean_dec(v_i_1050_);
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
lean_object* v_key_1076_; lean_object* v_val_1077_; uint8_t v___x_1078_; 
v_key_1076_ = lean_ctor_get(v___x_1075_, 0);
v_val_1077_ = lean_ctor_get(v___x_1075_, 1);
v___x_1078_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1069_, v_key_1076_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; 
v___x_1079_ = lean_box(0);
return v___x_1079_;
}
else
{
lean_object* v___x_1080_; 
lean_inc(v_val_1077_);
v___x_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1080_, 0, v_val_1077_);
return v___x_1080_;
}
}
case 1:
{
lean_object* v_node_1081_; size_t v___x_1082_; size_t v___x_1083_; 
v_node_1081_ = lean_ctor_get(v___x_1075_, 0);
v___x_1082_ = ((size_t)5ULL);
v___x_1083_ = lean_usize_shift_right(v_x_1068_, v___x_1082_);
v_x_1067_ = v_node_1081_;
v_x_1068_ = v___x_1083_;
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
v_ks_1086_ = lean_ctor_get(v_x_1067_, 0);
v_vs_1087_ = lean_ctor_get(v_x_1067_, 1);
v___x_1088_ = lean_unsigned_to_nat(0u);
v___x_1089_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(v_ks_1086_, v_vs_1087_, v___x_1088_, v_x_1069_);
return v___x_1089_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg___boxed(lean_object* v_x_1090_, lean_object* v_x_1091_, lean_object* v_x_1092_){
_start:
{
size_t v_x_33065__boxed_1093_; lean_object* v_res_1094_; 
v_x_33065__boxed_1093_ = lean_unbox_usize(v_x_1091_);
lean_dec(v_x_1091_);
v_res_1094_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(v_x_1090_, v_x_33065__boxed_1093_, v_x_1092_);
lean_dec_ref(v_x_1092_);
lean_dec_ref(v_x_1090_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(lean_object* v_x_1095_, lean_object* v_x_1096_){
_start:
{
uint64_t v___x_1097_; size_t v___x_1098_; lean_object* v___x_1099_; 
v___x_1097_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1096_);
v___x_1098_ = lean_uint64_to_usize(v___x_1097_);
v___x_1099_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(v_x_1095_, v___x_1098_, v_x_1096_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg___boxed(lean_object* v_x_1100_, lean_object* v_x_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(v_x_1100_, v_x_1101_);
lean_dec_ref(v_x_1101_);
lean_dec_ref(v_x_1100_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4(lean_object* v_msgData_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v___x_1109_; lean_object* v_env_1110_; lean_object* v___x_1111_; lean_object* v_mctx_1112_; lean_object* v_lctx_1113_; lean_object* v_options_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1109_ = lean_st_ref_get(v___y_1107_);
v_env_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc_ref(v_env_1110_);
lean_dec(v___x_1109_);
v___x_1111_ = lean_st_ref_get(v___y_1105_);
v_mctx_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc_ref(v_mctx_1112_);
lean_dec(v___x_1111_);
v_lctx_1113_ = lean_ctor_get(v___y_1104_, 2);
v_options_1114_ = lean_ctor_get(v___y_1106_, 2);
lean_inc_ref(v_options_1114_);
lean_inc_ref(v_lctx_1113_);
v___x_1115_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1115_, 0, v_env_1110_);
lean_ctor_set(v___x_1115_, 1, v_mctx_1112_);
lean_ctor_set(v___x_1115_, 2, v_lctx_1113_);
lean_ctor_set(v___x_1115_, 3, v_options_1114_);
v___x_1116_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1115_);
lean_ctor_set(v___x_1116_, 1, v_msgData_1103_);
v___x_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4___boxed(lean_object* v_msgData_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4(v_msgData_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
return v_res_1124_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1125_; double v___x_1126_; 
v___x_1125_ = lean_unsigned_to_nat(0u);
v___x_1126_ = lean_float_of_nat(v___x_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(lean_object* v_cls_1130_, lean_object* v_msg_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v_ref_1137_; lean_object* v___x_1138_; lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1183_; 
v_ref_1137_ = lean_ctor_get(v___y_1134_, 5);
v___x_1138_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4(v_msg_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1141_ = v___x_1138_;
v_isShared_1142_ = v_isSharedCheck_1183_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1138_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1183_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1143_; lean_object* v_traceState_1144_; lean_object* v_env_1145_; lean_object* v_nextMacroScope_1146_; lean_object* v_ngen_1147_; lean_object* v_auxDeclNGen_1148_; lean_object* v_cache_1149_; lean_object* v_messages_1150_; lean_object* v_infoState_1151_; lean_object* v_snapshotTasks_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1182_; 
v___x_1143_ = lean_st_ref_take(v___y_1135_);
v_traceState_1144_ = lean_ctor_get(v___x_1143_, 4);
v_env_1145_ = lean_ctor_get(v___x_1143_, 0);
v_nextMacroScope_1146_ = lean_ctor_get(v___x_1143_, 1);
v_ngen_1147_ = lean_ctor_get(v___x_1143_, 2);
v_auxDeclNGen_1148_ = lean_ctor_get(v___x_1143_, 3);
v_cache_1149_ = lean_ctor_get(v___x_1143_, 5);
v_messages_1150_ = lean_ctor_get(v___x_1143_, 6);
v_infoState_1151_ = lean_ctor_get(v___x_1143_, 7);
v_snapshotTasks_1152_ = lean_ctor_get(v___x_1143_, 8);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1154_ = v___x_1143_;
v_isShared_1155_ = v_isSharedCheck_1182_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_snapshotTasks_1152_);
lean_inc(v_infoState_1151_);
lean_inc(v_messages_1150_);
lean_inc(v_cache_1149_);
lean_inc(v_traceState_1144_);
lean_inc(v_auxDeclNGen_1148_);
lean_inc(v_ngen_1147_);
lean_inc(v_nextMacroScope_1146_);
lean_inc(v_env_1145_);
lean_dec(v___x_1143_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1182_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
uint64_t v_tid_1156_; lean_object* v_traces_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1181_; 
v_tid_1156_ = lean_ctor_get_uint64(v_traceState_1144_, sizeof(void*)*1);
v_traces_1157_ = lean_ctor_get(v_traceState_1144_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v_traceState_1144_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1159_ = v_traceState_1144_;
v_isShared_1160_ = v_isSharedCheck_1181_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_traces_1157_);
lean_dec(v_traceState_1144_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1181_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1161_; double v___x_1162_; uint8_t v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1171_; 
v___x_1161_ = lean_box(0);
v___x_1162_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0);
v___x_1163_ = 0;
v___x_1164_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__1));
v___x_1165_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1165_, 0, v_cls_1130_);
lean_ctor_set(v___x_1165_, 1, v___x_1161_);
lean_ctor_set(v___x_1165_, 2, v___x_1164_);
lean_ctor_set_float(v___x_1165_, sizeof(void*)*3, v___x_1162_);
lean_ctor_set_float(v___x_1165_, sizeof(void*)*3 + 8, v___x_1162_);
lean_ctor_set_uint8(v___x_1165_, sizeof(void*)*3 + 16, v___x_1163_);
v___x_1166_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__2));
v___x_1167_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1165_);
lean_ctor_set(v___x_1167_, 1, v_a_1139_);
lean_ctor_set(v___x_1167_, 2, v___x_1166_);
lean_inc(v_ref_1137_);
v___x_1168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1168_, 0, v_ref_1137_);
lean_ctor_set(v___x_1168_, 1, v___x_1167_);
v___x_1169_ = l_Lean_PersistentArray_push___redArg(v_traces_1157_, v___x_1168_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v___x_1169_);
v___x_1171_ = v___x_1159_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1169_);
lean_ctor_set_uint64(v_reuseFailAlloc_1180_, sizeof(void*)*1, v_tid_1156_);
v___x_1171_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
lean_object* v___x_1173_; 
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 4, v___x_1171_);
v___x_1173_ = v___x_1154_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_env_1145_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v_nextMacroScope_1146_);
lean_ctor_set(v_reuseFailAlloc_1179_, 2, v_ngen_1147_);
lean_ctor_set(v_reuseFailAlloc_1179_, 3, v_auxDeclNGen_1148_);
lean_ctor_set(v_reuseFailAlloc_1179_, 4, v___x_1171_);
lean_ctor_set(v_reuseFailAlloc_1179_, 5, v_cache_1149_);
lean_ctor_set(v_reuseFailAlloc_1179_, 6, v_messages_1150_);
lean_ctor_set(v_reuseFailAlloc_1179_, 7, v_infoState_1151_);
lean_ctor_set(v_reuseFailAlloc_1179_, 8, v_snapshotTasks_1152_);
v___x_1173_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1174_ = lean_st_ref_set(v___y_1135_, v___x_1173_);
v___x_1175_ = lean_box(0);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 0, v___x_1175_);
v___x_1177_ = v___x_1141_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1175_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___boxed(lean_object* v_cls_1184_, lean_object* v_msg_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(v_cls_1184_, v_msg_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
return v_res_1191_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7(void){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1204_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4));
v___x_1205_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__6));
v___x_1206_ = l_Lean_Name_append(v___x_1205_, v___x_1204_);
return v___x_1206_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9(void){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__8));
v___x_1209_ = l_Lean_stringToMessageData(v___x_1208_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* lean_grind_cutsat_mk_var(lean_object* v_expr_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_){
_start:
{
lean_object* v___x_1222_; 
v___x_1222_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1211_, v_a_1219_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1360_; 
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1225_ = v___x_1222_;
v_isShared_1226_ = v_isSharedCheck_1360_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1222_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1360_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v_varMap_1227_; lean_object* v___x_1228_; 
v_varMap_1227_ = lean_ctor_get(v_a_1223_, 1);
lean_inc_ref(v_varMap_1227_);
lean_dec(v_a_1223_);
v___x_1228_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(v_varMap_1227_, v_expr_1210_);
lean_dec_ref(v_varMap_1227_);
if (lean_obj_tag(v___x_1228_) == 1)
{
lean_object* v_val_1229_; lean_object* v___x_1231_; 
lean_dec(v_a_1220_);
lean_dec_ref(v_a_1219_);
lean_dec(v_a_1218_);
lean_dec_ref(v_a_1217_);
lean_dec(v_a_1216_);
lean_dec_ref(v_a_1215_);
lean_dec(v_a_1214_);
lean_dec_ref(v_a_1213_);
lean_dec(v_a_1212_);
lean_dec(v_a_1211_);
lean_dec_ref(v_expr_1210_);
v_val_1229_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_val_1229_);
lean_dec_ref_known(v___x_1228_, 1);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 0, v_val_1229_);
v___x_1231_ = v___x_1225_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_val_1229_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
else
{
lean_object* v___x_1233_; 
lean_dec(v___x_1228_);
lean_del_object(v___x_1225_);
v___x_1233_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1211_, v_a_1219_);
if (lean_obj_tag(v___x_1233_) == 0)
{
lean_object* v_a_1234_; lean_object* v_vars_1235_; lean_object* v_options_1236_; lean_object* v_size_1237_; lean_object* v_inheritedTraceOptions_1238_; uint8_t v_hasTrace_1239_; lean_object* v___f_1240_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; 
v_a_1234_ = lean_ctor_get(v___x_1233_, 0);
lean_inc(v_a_1234_);
lean_dec_ref_known(v___x_1233_, 1);
v_vars_1235_ = lean_ctor_get(v_a_1234_, 0);
lean_inc_ref(v_vars_1235_);
lean_dec(v_a_1234_);
v_options_1236_ = lean_ctor_get(v_a_1219_, 2);
v_size_1237_ = lean_ctor_get(v_vars_1235_, 2);
lean_inc_n(v_size_1237_, 2);
lean_dec_ref(v_vars_1235_);
v_inheritedTraceOptions_1238_ = lean_ctor_get(v_a_1219_, 13);
v_hasTrace_1239_ = lean_ctor_get_uint8(v_options_1236_, sizeof(void*)*1);
lean_inc_ref(v_expr_1210_);
v___f_1240_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0), 3, 2);
lean_closure_set(v___f_1240_, 0, v_expr_1210_);
lean_closure_set(v___f_1240_, 1, v_size_1237_);
if (v_hasTrace_1239_ == 0)
{
v___y_1242_ = v_a_1211_;
v___y_1243_ = v_a_1212_;
v___y_1244_ = v_a_1213_;
v___y_1245_ = v_a_1214_;
v___y_1246_ = v_a_1215_;
v___y_1247_ = v_a_1216_;
v___y_1248_ = v_a_1217_;
v___y_1249_ = v_a_1218_;
v___y_1250_ = v_a_1219_;
v___y_1251_ = v_a_1220_;
goto v___jp_1241_;
}
else
{
lean_object* v___x_1333_; lean_object* v___x_1334_; uint8_t v___x_1335_; 
v___x_1333_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4));
v___x_1334_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7);
v___x_1335_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1238_, v_options_1236_, v___x_1334_);
if (v___x_1335_ == 0)
{
v___y_1242_ = v_a_1211_;
v___y_1243_ = v_a_1212_;
v___y_1244_ = v_a_1213_;
v___y_1245_ = v_a_1214_;
v___y_1246_ = v_a_1215_;
v___y_1247_ = v_a_1216_;
v___y_1248_ = v_a_1217_;
v___y_1249_ = v_a_1218_;
v___y_1250_ = v_a_1219_;
v___y_1251_ = v_a_1220_;
goto v___jp_1241_;
}
else
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
lean_inc_ref(v_expr_1210_);
v___x_1336_ = l_Lean_MessageData_ofExpr(v_expr_1210_);
v___x_1337_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9);
v___x_1338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1336_);
lean_ctor_set(v___x_1338_, 1, v___x_1337_);
lean_inc(v_size_1237_);
v___x_1339_ = l_Nat_reprFast(v_size_1237_);
v___x_1340_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1339_);
v___x_1341_ = l_Lean_MessageData_ofFormat(v___x_1340_);
v___x_1342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1338_);
lean_ctor_set(v___x_1342_, 1, v___x_1341_);
v___x_1343_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(v___x_1333_, v___x_1342_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_dec_ref_known(v___x_1343_, 1);
v___y_1242_ = v_a_1211_;
v___y_1243_ = v_a_1212_;
v___y_1244_ = v_a_1213_;
v___y_1245_ = v_a_1214_;
v___y_1246_ = v_a_1215_;
v___y_1247_ = v_a_1216_;
v___y_1248_ = v_a_1217_;
v___y_1249_ = v_a_1218_;
v___y_1250_ = v_a_1219_;
v___y_1251_ = v_a_1220_;
goto v___jp_1241_;
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1351_; 
lean_dec_ref(v___f_1240_);
lean_dec(v_size_1237_);
lean_dec(v_a_1220_);
lean_dec_ref(v_a_1219_);
lean_dec(v_a_1218_);
lean_dec_ref(v_a_1217_);
lean_dec(v_a_1216_);
lean_dec_ref(v_a_1215_);
lean_dec(v_a_1214_);
lean_dec_ref(v_a_1213_);
lean_dec(v_a_1212_);
lean_dec(v_a_1211_);
lean_dec_ref(v_expr_1210_);
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1346_ = v___x_1343_;
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1343_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1349_; 
if (v_isShared_1347_ == 0)
{
v___x_1349_ = v___x_1346_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1344_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
}
v___jp_1241_:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_1253_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1252_, v___f_1240_, v___y_1242_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v___x_1254_; 
lean_dec_ref_known(v___x_1253_, 1);
lean_inc_ref(v_expr_1210_);
v___x_1254_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_1252_, v_expr_1210_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v___x_1255_; 
lean_dec_ref_known(v___x_1254_, 1);
lean_inc(v_size_1237_);
lean_inc_ref(v_expr_1210_);
v___x_1255_ = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(v_expr_1210_, v_size_1237_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v___x_1256_; 
lean_dec_ref_known(v___x_1255_, 1);
lean_inc(v_size_1237_);
lean_inc_ref(v_expr_1210_);
v___x_1256_ = l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg(v_expr_1210_, v_size_1237_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v___x_1257_; 
lean_dec_ref_known(v___x_1256_, 1);
lean_inc(v_size_1237_);
lean_inc_ref(v_expr_1210_);
v___x_1257_ = l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds(v_expr_1210_, v_size_1237_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v___x_1258_; 
lean_dec_ref_known(v___x_1257_, 1);
lean_inc_ref(v_expr_1210_);
v___x_1258_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm(v_expr_1210_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1284_; 
v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1261_ = v___x_1258_;
v_isShared_1262_ = v_isSharedCheck_1284_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1258_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1284_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
uint8_t v___x_1263_; 
v___x_1263_ = lean_unbox(v_a_1259_);
lean_dec(v_a_1259_);
if (v___x_1263_ == 0)
{
lean_object* v___x_1265_; 
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec_ref(v_expr_1210_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 0, v_size_1237_);
v___x_1265_ = v___x_1261_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_size_1237_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
else
{
lean_object* v___x_1267_; 
lean_del_object(v___x_1261_);
lean_inc(v_size_1237_);
v___x_1267_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt(v_expr_1210_, v_size_1237_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec(v___y_1243_);
lean_dec(v___y_1242_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1274_ == 0)
{
lean_object* v_unused_1275_; 
v_unused_1275_ = lean_ctor_get(v___x_1267_, 0);
lean_dec(v_unused_1275_);
v___x_1269_ = v___x_1267_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_dec(v___x_1267_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 0, v_size_1237_);
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_size_1237_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
else
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
lean_dec(v_size_1237_);
v_a_1276_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v___x_1267_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1267_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
}
}
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec(v_size_1237_);
lean_dec_ref(v_expr_1210_);
v_a_1285_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1258_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1258_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
else
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1300_; 
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec(v_size_1237_);
lean_dec_ref(v_expr_1210_);
v_a_1293_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1295_ = v___x_1257_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1257_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
if (v_isShared_1296_ == 0)
{
v___x_1298_ = v___x_1295_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1293_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
else
{
lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1308_; 
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec(v_size_1237_);
lean_dec_ref(v_expr_1210_);
v_a_1301_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1303_ = v___x_1256_;
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_dec(v___x_1256_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1306_; 
if (v_isShared_1304_ == 0)
{
v___x_1306_ = v___x_1303_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_a_1301_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
}
else
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec(v_size_1237_);
lean_dec_ref(v_expr_1210_);
v_a_1309_ = lean_ctor_get(v___x_1255_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1311_ = v___x_1255_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1255_);
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
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec(v_size_1237_);
lean_dec_ref(v_expr_1210_);
v_a_1317_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1254_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1254_);
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
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec(v_size_1237_);
lean_dec_ref(v_expr_1210_);
v_a_1325_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1253_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1253_);
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
}
else
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1359_; 
lean_dec(v_a_1220_);
lean_dec_ref(v_a_1219_);
lean_dec(v_a_1218_);
lean_dec_ref(v_a_1217_);
lean_dec(v_a_1216_);
lean_dec_ref(v_a_1215_);
lean_dec(v_a_1214_);
lean_dec_ref(v_a_1213_);
lean_dec(v_a_1212_);
lean_dec(v_a_1211_);
lean_dec_ref(v_expr_1210_);
v_a_1352_ = lean_ctor_get(v___x_1233_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1354_ = v___x_1233_;
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1233_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1352_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
}
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
lean_dec(v_a_1220_);
lean_dec_ref(v_a_1219_);
lean_dec(v_a_1218_);
lean_dec_ref(v_a_1217_);
lean_dec(v_a_1216_);
lean_dec_ref(v_a_1215_);
lean_dec(v_a_1214_);
lean_dec_ref(v_a_1213_);
lean_dec(v_a_1212_);
lean_dec(v_a_1211_);
lean_dec_ref(v_expr_1210_);
v_a_1361_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1222_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1222_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___boxed(lean_object* v_expr_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = lean_grind_cutsat_mk_var(v_expr_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0(lean_object* v_00_u03b2_1382_, lean_object* v_x_1383_, lean_object* v_x_1384_){
_start:
{
lean_object* v___x_1385_; 
v___x_1385_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(v_x_1383_, v_x_1384_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___boxed(lean_object* v_00_u03b2_1386_, lean_object* v_x_1387_, lean_object* v_x_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0(v_00_u03b2_1386_, v_x_1387_, v_x_1388_);
lean_dec_ref(v_x_1388_);
lean_dec_ref(v_x_1387_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1(lean_object* v_00_u03b2_1390_, lean_object* v_x_1391_, lean_object* v_x_1392_, lean_object* v_x_1393_){
_start:
{
lean_object* v___x_1394_; 
v___x_1394_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg(v_x_1391_, v_x_1392_, v_x_1393_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2(lean_object* v_cls_1395_, lean_object* v_msg_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(v_cls_1395_, v_msg_1396_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___boxed(lean_object* v_cls_1409_, lean_object* v_msg_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2(v_cls_1409_, v_msg_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec(v___y_1411_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0(lean_object* v_00_u03b2_1423_, lean_object* v_x_1424_, size_t v_x_1425_, lean_object* v_x_1426_){
_start:
{
lean_object* v___x_1427_; 
v___x_1427_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(v_x_1424_, v_x_1425_, v_x_1426_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1428_, lean_object* v_x_1429_, lean_object* v_x_1430_, lean_object* v_x_1431_){
_start:
{
size_t v_x_33647__boxed_1432_; lean_object* v_res_1433_; 
v_x_33647__boxed_1432_ = lean_unbox_usize(v_x_1430_);
lean_dec(v_x_1430_);
v_res_1433_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0(v_00_u03b2_1428_, v_x_1429_, v_x_33647__boxed_1432_, v_x_1431_);
lean_dec_ref(v_x_1431_);
lean_dec_ref(v_x_1429_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2(lean_object* v_00_u03b2_1434_, lean_object* v_x_1435_, size_t v_x_1436_, size_t v_x_1437_, lean_object* v_x_1438_, lean_object* v_x_1439_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_x_1435_, v_x_1436_, v_x_1437_, v_x_1438_, v_x_1439_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1441_, lean_object* v_x_1442_, lean_object* v_x_1443_, lean_object* v_x_1444_, lean_object* v_x_1445_, lean_object* v_x_1446_){
_start:
{
size_t v_x_33658__boxed_1447_; size_t v_x_33659__boxed_1448_; lean_object* v_res_1449_; 
v_x_33658__boxed_1447_ = lean_unbox_usize(v_x_1443_);
lean_dec(v_x_1443_);
v_x_33659__boxed_1448_ = lean_unbox_usize(v_x_1444_);
lean_dec(v_x_1444_);
v_res_1449_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2(v_00_u03b2_1441_, v_x_1442_, v_x_33658__boxed_1447_, v_x_33659__boxed_1448_, v_x_1445_, v_x_1446_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1450_, lean_object* v_keys_1451_, lean_object* v_vals_1452_, lean_object* v_heq_1453_, lean_object* v_i_1454_, lean_object* v_k_1455_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(v_keys_1451_, v_vals_1452_, v_i_1454_, v_k_1455_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1457_, lean_object* v_keys_1458_, lean_object* v_vals_1459_, lean_object* v_heq_1460_, lean_object* v_i_1461_, lean_object* v_k_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1(v_00_u03b2_1457_, v_keys_1458_, v_vals_1459_, v_heq_1460_, v_i_1461_, v_k_1462_);
lean_dec_ref(v_k_1462_);
lean_dec_ref(v_vals_1459_);
lean_dec_ref(v_keys_1458_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1464_, lean_object* v_n_1465_, lean_object* v_k_1466_, lean_object* v_v_1467_){
_start:
{
lean_object* v___x_1468_; 
v___x_1468_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4___redArg(v_n_1465_, v_k_1466_, v_v_1467_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1469_, size_t v_depth_1470_, lean_object* v_keys_1471_, lean_object* v_vals_1472_, lean_object* v_heq_1473_, lean_object* v_i_1474_, lean_object* v_entries_1475_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(v_depth_1470_, v_keys_1471_, v_vals_1472_, v_i_1474_, v_entries_1475_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1477_, lean_object* v_depth_1478_, lean_object* v_keys_1479_, lean_object* v_vals_1480_, lean_object* v_heq_1481_, lean_object* v_i_1482_, lean_object* v_entries_1483_){
_start:
{
size_t v_depth_boxed_1484_; lean_object* v_res_1485_; 
v_depth_boxed_1484_ = lean_unbox_usize(v_depth_1478_);
lean_dec(v_depth_1478_);
v_res_1485_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5(v_00_u03b2_1477_, v_depth_boxed_1484_, v_keys_1479_, v_vals_1480_, v_heq_1481_, v_i_1482_, v_entries_1483_);
lean_dec_ref(v_vals_1480_);
lean_dec_ref(v_keys_1479_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_1486_, lean_object* v_x_1487_, lean_object* v_x_1488_, lean_object* v_x_1489_, lean_object* v_x_1490_){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7___redArg(v_x_1487_, v_x_1488_, v_x_1489_, v_x_1490_);
return v___x_1491_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2(void){
_start:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1495_ = lean_box(0);
v___x_1496_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__1));
v___x_1497_ = l_Lean_mkConst(v___x_1496_, v___x_1495_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(lean_object* v_e_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_){
_start:
{
lean_object* v___x_1504_; 
lean_inc(v_a_1502_);
lean_inc_ref(v_a_1501_);
lean_inc(v_a_1500_);
lean_inc_ref(v_a_1499_);
v___x_1504_ = lean_infer_type(v_e_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v_a_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
v_a_1505_ = lean_ctor_get(v___x_1504_, 0);
lean_inc(v_a_1505_);
lean_dec_ref_known(v___x_1504_, 1);
v___x_1506_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2);
v___x_1507_ = l_Lean_Meta_isExprDefEq(v_a_1505_, v___x_1506_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_);
return v___x_1507_;
}
else
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1515_; 
v_a_1508_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1510_ = v___x_1504_;
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1504_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
if (v_isShared_1511_ == 0)
{
v___x_1513_ = v___x_1510_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_a_1508_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___boxed(lean_object* v_e_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(v_e_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
lean_dec(v_a_1520_);
lean_dec_ref(v_a_1519_);
lean_dec(v_a_1518_);
lean_dec_ref(v_a_1517_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt(lean_object* v_e_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(v_e_1523_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___boxed(lean_object* v_e_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l_Lean_Meta_Grind_Arith_Cutsat_isInt(v_e_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_);
lean_dec(v_a_1546_);
lean_dec_ref(v_a_1545_);
lean_dec(v_a_1544_);
lean_dec_ref(v_a_1543_);
lean_dec(v_a_1542_);
lean_dec_ref(v_a_1541_);
lean_dec(v_a_1540_);
lean_dec_ref(v_a_1539_);
lean_dec(v_a_1538_);
lean_dec(v_a_1537_);
return v_res_1548_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4(void){
_start:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1555_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__3));
v___x_1556_ = l_Lean_stringToMessageData(v___x_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(lean_object* v_e_1557_, uint8_t v_report_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_){
_start:
{
lean_object* v___x_1569_; 
lean_inc_ref(v_e_1557_);
v___x_1569_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1557_, v_a_1562_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1640_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1572_ = v___x_1569_;
v_isShared_1573_ = v_isSharedCheck_1640_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1569_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1640_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1579_; uint8_t v___x_1580_; 
v___x_1579_ = l_Lean_Expr_cleanupAnnotations(v_a_1570_);
v___x_1580_ = l_Lean_Expr_isApp(v___x_1579_);
if (v___x_1580_ == 0)
{
lean_dec_ref(v___x_1579_);
lean_dec_ref(v_e_1557_);
goto v___jp_1574_;
}
else
{
lean_object* v_arg_1581_; lean_object* v___x_1582_; uint8_t v___x_1583_; 
v_arg_1581_ = lean_ctor_get(v___x_1579_, 1);
lean_inc_ref(v_arg_1581_);
v___x_1582_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1579_);
v___x_1583_ = l_Lean_Expr_isApp(v___x_1582_);
if (v___x_1583_ == 0)
{
lean_dec_ref(v___x_1582_);
lean_dec_ref(v_arg_1581_);
lean_dec_ref(v_e_1557_);
goto v___jp_1574_;
}
else
{
lean_object* v_arg_1584_; lean_object* v___x_1585_; uint8_t v___x_1586_; 
v_arg_1584_ = lean_ctor_get(v___x_1582_, 1);
lean_inc_ref(v_arg_1584_);
v___x_1585_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1582_);
v___x_1586_ = l_Lean_Expr_isApp(v___x_1585_);
if (v___x_1586_ == 0)
{
lean_dec_ref(v___x_1585_);
lean_dec_ref(v_arg_1584_);
lean_dec_ref(v_arg_1581_);
lean_dec_ref(v_e_1557_);
goto v___jp_1574_;
}
else
{
lean_object* v_arg_1587_; lean_object* v___x_1588_; uint8_t v___x_1589_; 
v_arg_1587_ = lean_ctor_get(v___x_1585_, 1);
lean_inc_ref(v_arg_1587_);
v___x_1588_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1585_);
v___x_1589_ = l_Lean_Expr_isApp(v___x_1588_);
if (v___x_1589_ == 0)
{
lean_dec_ref(v___x_1588_);
lean_dec_ref(v_arg_1587_);
lean_dec_ref(v_arg_1584_);
lean_dec_ref(v_arg_1581_);
lean_dec_ref(v_e_1557_);
goto v___jp_1574_;
}
else
{
lean_object* v___x_1590_; uint8_t v___x_1591_; 
v___x_1590_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1588_);
v___x_1591_ = l_Lean_Expr_isApp(v___x_1590_);
if (v___x_1591_ == 0)
{
lean_dec_ref(v___x_1590_);
lean_dec_ref(v_arg_1587_);
lean_dec_ref(v_arg_1584_);
lean_dec_ref(v_arg_1581_);
lean_dec_ref(v_e_1557_);
goto v___jp_1574_;
}
else
{
lean_object* v___x_1592_; uint8_t v___x_1593_; 
v___x_1592_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1590_);
v___x_1593_ = l_Lean_Expr_isApp(v___x_1592_);
if (v___x_1593_ == 0)
{
lean_dec_ref(v___x_1592_);
lean_dec_ref(v_arg_1587_);
lean_dec_ref(v_arg_1584_);
lean_dec_ref(v_arg_1581_);
lean_dec_ref(v_e_1557_);
goto v___jp_1574_;
}
else
{
lean_object* v___x_1594_; lean_object* v___x_1595_; uint8_t v___x_1596_; 
v___x_1594_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1592_);
v___x_1595_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__2));
v___x_1596_ = l_Lean_Expr_isConstOf(v___x_1594_, v___x_1595_);
lean_dec_ref(v___x_1594_);
if (v___x_1596_ == 0)
{
lean_dec_ref(v_arg_1587_);
lean_dec_ref(v_arg_1584_);
lean_dec_ref(v_arg_1581_);
lean_dec_ref(v_e_1557_);
goto v___jp_1574_;
}
else
{
lean_object* v___x_1597_; 
lean_del_object(v___x_1572_);
v___x_1597_ = l_Lean_Meta_Structural_isInstHAddInt___redArg(v_arg_1587_, v_a_1562_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1631_; 
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1600_ = v___x_1597_;
v_isShared_1601_ = v_isSharedCheck_1631_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1597_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1631_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
uint8_t v___x_1602_; 
v___x_1602_ = lean_unbox(v_a_1598_);
lean_dec(v_a_1598_);
if (v___x_1602_ == 0)
{
lean_del_object(v___x_1600_);
lean_dec_ref(v_arg_1584_);
lean_dec_ref(v_arg_1581_);
if (v_report_1558_ == 0)
{
lean_dec_ref(v_e_1557_);
goto v___jp_1566_;
}
else
{
lean_object* v___x_1603_; 
v___x_1603_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1559_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; uint8_t v___x_1605_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_a_1604_);
lean_dec_ref_known(v___x_1603_, 1);
v___x_1605_ = lean_unbox(v_a_1604_);
lean_dec(v_a_1604_);
if (v___x_1605_ == 0)
{
lean_dec_ref(v_e_1557_);
goto v___jp_1566_;
}
else
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1606_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4);
v___x_1607_ = l_Lean_indentExpr(v_e_1557_);
v___x_1608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1606_);
lean_ctor_set(v___x_1608_, 1, v___x_1607_);
v___x_1609_ = l_Lean_Meta_Sym_reportIssue(v___x_1608_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_dec_ref_known(v___x_1609_, 1);
goto v___jp_1566_;
}
else
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1612_ = v___x_1609_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1609_);
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
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1625_; 
lean_dec_ref(v_e_1557_);
v_a_1618_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1620_ = v___x_1603_;
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1603_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1623_; 
if (v_isShared_1621_ == 0)
{
v___x_1623_ = v___x_1620_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_a_1618_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
}
else
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1629_; 
lean_dec_ref(v_e_1557_);
v___x_1626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1626_, 0, v_arg_1584_);
lean_ctor_set(v___x_1626_, 1, v_arg_1581_);
v___x_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1626_);
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v___x_1627_);
v___x_1629_ = v___x_1600_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1627_);
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
else
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
lean_dec_ref(v_arg_1584_);
lean_dec_ref(v_arg_1581_);
lean_dec_ref(v_e_1557_);
v_a_1632_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1597_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1597_);
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
}
}
}
}
}
}
}
v___jp_1574_:
{
lean_object* v___x_1575_; lean_object* v___x_1577_; 
v___x_1575_ = lean_box(0);
if (v_isShared_1573_ == 0)
{
lean_ctor_set(v___x_1572_, 0, v___x_1575_);
v___x_1577_ = v___x_1572_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1575_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
else
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1648_; 
lean_dec_ref(v_e_1557_);
v_a_1641_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1643_ = v___x_1569_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1569_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1646_; 
if (v_isShared_1644_ == 0)
{
v___x_1646_ = v___x_1643_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_a_1641_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___boxed(lean_object* v_e_1649_, lean_object* v_report_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_){
_start:
{
uint8_t v_report_boxed_1658_; lean_object* v_res_1659_; 
v_report_boxed_1658_ = lean_unbox(v_report_1650_);
v_res_1659_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_1649_, v_report_boxed_1658_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_);
lean_dec(v_a_1656_);
lean_dec_ref(v_a_1655_);
lean_dec(v_a_1654_);
lean_dec_ref(v_a_1653_);
lean_dec(v_a_1652_);
lean_dec_ref(v_a_1651_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f(lean_object* v_e_1660_, uint8_t v_report_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_){
_start:
{
lean_object* v___x_1673_; 
v___x_1673_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_1660_, v_report_1661_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___boxed(lean_object* v_e_1674_, lean_object* v_report_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_){
_start:
{
uint8_t v_report_boxed_1687_; lean_object* v_res_1688_; 
v_report_boxed_1687_ = lean_unbox(v_report_1675_);
v_res_1688_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f(v_e_1674_, v_report_boxed_1687_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_);
lean_dec(v_a_1685_);
lean_dec_ref(v_a_1684_);
lean_dec(v_a_1683_);
lean_dec_ref(v_a_1682_);
lean_dec(v_a_1681_);
lean_dec_ref(v_a_1680_);
lean_dec(v_a_1679_);
lean_dec_ref(v_a_1678_);
lean_dec(v_a_1677_);
lean_dec(v_a_1676_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(lean_object* v_e_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_){
_start:
{
uint8_t v___x_1697_; lean_object* v___x_1698_; 
v___x_1697_ = 0;
v___x_1698_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_1689_, v___x_1697_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1712_; 
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1701_ = v___x_1698_;
v_isShared_1702_ = v_isSharedCheck_1712_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1698_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1712_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
if (lean_obj_tag(v_a_1699_) == 0)
{
lean_object* v___x_1703_; lean_object* v___x_1705_; 
v___x_1703_ = lean_box(v___x_1697_);
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 0, v___x_1703_);
v___x_1705_ = v___x_1701_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1703_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
else
{
uint8_t v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1710_; 
lean_dec_ref_known(v_a_1699_, 1);
v___x_1707_ = 1;
v___x_1708_ = lean_box(v___x_1707_);
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 0, v___x_1708_);
v___x_1710_ = v___x_1701_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v___x_1708_);
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
else
{
lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1720_; 
v_a_1713_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1715_ = v___x_1698_;
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1698_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1713_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg___boxed(lean_object* v_e_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(v_e_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_);
lean_dec(v_a_1727_);
lean_dec_ref(v_a_1726_);
lean_dec(v_a_1725_);
lean_dec_ref(v_a_1724_);
lean_dec(v_a_1723_);
lean_dec_ref(v_a_1722_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd(lean_object* v_e_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(v_e_1730_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___boxed(lean_object* v_e_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd(v_e_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_);
lean_dec(v_a_1753_);
lean_dec_ref(v_a_1752_);
lean_dec(v_a_1751_);
lean_dec_ref(v_a_1750_);
lean_dec(v_a_1749_);
lean_dec_ref(v_a_1748_);
lean_dec(v_a_1747_);
lean_dec_ref(v_a_1746_);
lean_dec(v_a_1745_);
lean_dec(v_a_1744_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(lean_object* v_e_1756_, uint8_t v_report_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_){
_start:
{
lean_object* v___x_1768_; 
lean_inc_ref(v_e_1756_);
v___x_1768_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1756_, v_a_1761_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1860_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1771_ = v___x_1768_;
v_isShared_1772_ = v_isSharedCheck_1860_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1768_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1860_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1778_; uint8_t v___x_1779_; 
v___x_1778_ = l_Lean_Expr_cleanupAnnotations(v_a_1769_);
v___x_1779_ = l_Lean_Expr_isApp(v___x_1778_);
if (v___x_1779_ == 0)
{
lean_dec_ref(v___x_1778_);
lean_dec_ref(v_e_1756_);
goto v___jp_1773_;
}
else
{
lean_object* v_arg_1780_; lean_object* v___x_1781_; uint8_t v___x_1782_; 
v_arg_1780_ = lean_ctor_get(v___x_1778_, 1);
lean_inc_ref(v_arg_1780_);
v___x_1781_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1778_);
v___x_1782_ = l_Lean_Expr_isApp(v___x_1781_);
if (v___x_1782_ == 0)
{
lean_dec_ref(v___x_1781_);
lean_dec_ref(v_arg_1780_);
lean_dec_ref(v_e_1756_);
goto v___jp_1773_;
}
else
{
lean_object* v_arg_1783_; lean_object* v___x_1784_; uint8_t v___x_1785_; 
v_arg_1783_ = lean_ctor_get(v___x_1781_, 1);
lean_inc_ref(v_arg_1783_);
v___x_1784_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1781_);
v___x_1785_ = l_Lean_Expr_isApp(v___x_1784_);
if (v___x_1785_ == 0)
{
lean_dec_ref(v___x_1784_);
lean_dec_ref(v_arg_1783_);
lean_dec_ref(v_arg_1780_);
lean_dec_ref(v_e_1756_);
goto v___jp_1773_;
}
else
{
lean_object* v_arg_1786_; lean_object* v___x_1787_; uint8_t v___x_1788_; 
v_arg_1786_ = lean_ctor_get(v___x_1784_, 1);
lean_inc_ref(v_arg_1786_);
v___x_1787_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1784_);
v___x_1788_ = l_Lean_Expr_isApp(v___x_1787_);
if (v___x_1788_ == 0)
{
lean_dec_ref(v___x_1787_);
lean_dec_ref(v_arg_1786_);
lean_dec_ref(v_arg_1783_);
lean_dec_ref(v_arg_1780_);
lean_dec_ref(v_e_1756_);
goto v___jp_1773_;
}
else
{
lean_object* v___x_1789_; uint8_t v___x_1790_; 
v___x_1789_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1787_);
v___x_1790_ = l_Lean_Expr_isApp(v___x_1789_);
if (v___x_1790_ == 0)
{
lean_dec_ref(v___x_1789_);
lean_dec_ref(v_arg_1786_);
lean_dec_ref(v_arg_1783_);
lean_dec_ref(v_arg_1780_);
lean_dec_ref(v_e_1756_);
goto v___jp_1773_;
}
else
{
lean_object* v___x_1791_; uint8_t v___x_1792_; 
v___x_1791_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1789_);
v___x_1792_ = l_Lean_Expr_isApp(v___x_1791_);
if (v___x_1792_ == 0)
{
lean_dec_ref(v___x_1791_);
lean_dec_ref(v_arg_1786_);
lean_dec_ref(v_arg_1783_);
lean_dec_ref(v_arg_1780_);
lean_dec_ref(v_e_1756_);
goto v___jp_1773_;
}
else
{
lean_object* v___x_1793_; lean_object* v___x_1794_; uint8_t v___x_1795_; 
v___x_1793_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1791_);
v___x_1794_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11));
v___x_1795_ = l_Lean_Expr_isConstOf(v___x_1793_, v___x_1794_);
lean_dec_ref(v___x_1793_);
if (v___x_1795_ == 0)
{
lean_dec_ref(v_arg_1786_);
lean_dec_ref(v_arg_1783_);
lean_dec_ref(v_arg_1780_);
lean_dec_ref(v_e_1756_);
goto v___jp_1773_;
}
else
{
lean_object* v___x_1796_; 
lean_del_object(v___x_1771_);
v___x_1796_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_1786_, v_a_1761_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_a_1797_; uint8_t v___x_1798_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_a_1797_);
lean_dec_ref_known(v___x_1796_, 1);
v___x_1798_ = lean_unbox(v_a_1797_);
lean_dec(v_a_1797_);
if (v___x_1798_ == 0)
{
lean_dec_ref(v_arg_1783_);
lean_dec_ref(v_arg_1780_);
if (v_report_1757_ == 0)
{
lean_dec_ref(v_e_1756_);
goto v___jp_1765_;
}
else
{
lean_object* v___x_1799_; 
v___x_1799_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1758_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v_a_1800_; uint8_t v___x_1801_; 
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
lean_inc(v_a_1800_);
lean_dec_ref_known(v___x_1799_, 1);
v___x_1801_ = lean_unbox(v_a_1800_);
lean_dec(v_a_1800_);
if (v___x_1801_ == 0)
{
lean_dec_ref(v_e_1756_);
goto v___jp_1765_;
}
else
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1802_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4);
v___x_1803_ = l_Lean_indentExpr(v_e_1756_);
v___x_1804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1802_);
lean_ctor_set(v___x_1804_, 1, v___x_1803_);
v___x_1805_ = l_Lean_Meta_Sym_reportIssue(v___x_1804_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_dec_ref_known(v___x_1805_, 1);
goto v___jp_1765_;
}
else
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1813_; 
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1808_ = v___x_1805_;
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1805_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1811_; 
if (v_isShared_1809_ == 0)
{
v___x_1811_ = v___x_1808_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_a_1806_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
}
}
else
{
lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1821_; 
lean_dec_ref(v_e_1756_);
v_a_1814_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1816_ = v___x_1799_;
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1799_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1819_; 
if (v_isShared_1817_ == 0)
{
v___x_1819_ = v___x_1816_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_a_1814_);
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
}
else
{
lean_object* v___x_1822_; 
lean_dec_ref(v_e_1756_);
v___x_1822_ = l_Lean_Meta_getIntValue_x3f(v_arg_1783_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1843_; 
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1825_ = v___x_1822_;
v_isShared_1826_ = v_isSharedCheck_1843_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1822_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1843_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
if (lean_obj_tag(v_a_1823_) == 1)
{
lean_object* v_val_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1838_; 
v_val_1827_ = lean_ctor_get(v_a_1823_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v_a_1823_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1829_ = v_a_1823_;
v_isShared_1830_ = v_isSharedCheck_1838_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_val_1827_);
lean_dec(v_a_1823_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1838_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1831_; lean_object* v___x_1833_; 
v___x_1831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1831_, 0, v_val_1827_);
lean_ctor_set(v___x_1831_, 1, v_arg_1780_);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 0, v___x_1831_);
v___x_1833_ = v___x_1829_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1831_);
v___x_1833_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
lean_object* v___x_1835_; 
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 0, v___x_1833_);
v___x_1835_ = v___x_1825_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1833_);
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
else
{
lean_object* v___x_1839_; lean_object* v___x_1841_; 
lean_dec(v_a_1823_);
lean_dec_ref(v_arg_1780_);
v___x_1839_ = lean_box(0);
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 0, v___x_1839_);
v___x_1841_ = v___x_1825_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1839_);
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
else
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1851_; 
lean_dec_ref(v_arg_1780_);
v_a_1844_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1846_ = v___x_1822_;
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1822_);
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
}
}
else
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1859_; 
lean_dec_ref(v_arg_1783_);
lean_dec_ref(v_arg_1780_);
lean_dec_ref(v_e_1756_);
v_a_1852_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1854_ = v___x_1796_;
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1796_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1855_ == 0)
{
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_a_1852_);
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
}
}
}
}
}
}
v___jp_1773_:
{
lean_object* v___x_1774_; lean_object* v___x_1776_; 
v___x_1774_ = lean_box(0);
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 0, v___x_1774_);
v___x_1776_ = v___x_1771_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v___x_1774_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_dec_ref(v_e_1756_);
v_a_1861_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1768_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1768_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
v___jp_1765_:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1766_ = lean_box(0);
v___x_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1766_);
return v___x_1767_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg___boxed(lean_object* v_e_1869_, lean_object* v_report_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_){
_start:
{
uint8_t v_report_boxed_1878_; lean_object* v_res_1879_; 
v_report_boxed_1878_ = lean_unbox(v_report_1870_);
v_res_1879_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1869_, v_report_boxed_1878_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_);
lean_dec(v_a_1876_);
lean_dec_ref(v_a_1875_);
lean_dec(v_a_1874_);
lean_dec_ref(v_a_1873_);
lean_dec(v_a_1872_);
lean_dec_ref(v_a_1871_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f(lean_object* v_e_1880_, uint8_t v_report_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1880_, v_report_1881_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___boxed(lean_object* v_e_1894_, lean_object* v_report_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_){
_start:
{
uint8_t v_report_boxed_1907_; lean_object* v_res_1908_; 
v_report_boxed_1907_ = lean_unbox(v_report_1895_);
v_res_1908_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f(v_e_1894_, v_report_boxed_1907_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_);
lean_dec(v_a_1905_);
lean_dec_ref(v_a_1904_);
lean_dec(v_a_1903_);
lean_dec_ref(v_a_1902_);
lean_dec(v_a_1901_);
lean_dec_ref(v_a_1900_);
lean_dec(v_a_1899_);
lean_dec_ref(v_a_1898_);
lean_dec(v_a_1897_);
lean_dec(v_a_1896_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(lean_object* v_e_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_){
_start:
{
uint8_t v___x_1917_; lean_object* v___x_1918_; 
v___x_1917_ = 0;
v___x_1918_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1909_, v___x_1917_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1932_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1921_ = v___x_1918_;
v_isShared_1922_ = v_isSharedCheck_1932_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1918_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1932_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
if (lean_obj_tag(v_a_1919_) == 0)
{
lean_object* v___x_1923_; lean_object* v___x_1925_; 
v___x_1923_ = lean_box(v___x_1917_);
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 0, v___x_1923_);
v___x_1925_ = v___x_1921_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___x_1923_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
else
{
uint8_t v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1930_; 
lean_dec_ref_known(v_a_1919_, 1);
v___x_1927_ = 1;
v___x_1928_ = lean_box(v___x_1927_);
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 0, v___x_1928_);
v___x_1930_ = v___x_1921_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1928_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
}
else
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
v_a_1933_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1935_ = v___x_1918_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1918_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg___boxed(lean_object* v_e_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(v_e_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_);
lean_dec(v_a_1947_);
lean_dec_ref(v_a_1946_);
lean_dec(v_a_1945_);
lean_dec_ref(v_a_1944_);
lean_dec(v_a_1943_);
lean_dec_ref(v_a_1942_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul(lean_object* v_e_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_){
_start:
{
lean_object* v___x_1962_; 
v___x_1962_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(v_e_1950_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___boxed(lean_object* v_e_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul(v_e_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_);
lean_dec(v_a_1973_);
lean_dec_ref(v_a_1972_);
lean_dec(v_a_1971_);
lean_dec_ref(v_a_1970_);
lean_dec(v_a_1969_);
lean_dec_ref(v_a_1968_);
lean_dec(v_a_1967_);
lean_dec_ref(v_a_1966_);
lean_dec(v_a_1965_);
lean_dec(v_a_1964_);
return v_res_1975_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0(void){
_start:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1976_ = lean_unsigned_to_nat(1u);
v___x_1977_ = lean_nat_to_int(v___x_1976_);
return v___x_1977_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2(void){
_start:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1979_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__1));
v___x_1980_ = l_Lean_stringToMessageData(v___x_1979_);
return v___x_1980_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4(void){
_start:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1982_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__3));
v___x_1983_ = l_Lean_stringToMessageData(v___x_1982_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(lean_object* v_e_1984_, lean_object* v_p_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_){
_start:
{
lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v___y_2003_; lean_object* v___y_2004_; lean_object* v___y_2005_; lean_object* v___y_2006_; lean_object* v___y_2007_; uint8_t v___x_2027_; lean_object* v___x_2028_; 
v___x_2027_ = 1;
lean_inc_ref(v_e_1984_);
v___x_2028_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1984_, v___x_2027_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_);
if (lean_obj_tag(v___x_2028_) == 0)
{
lean_object* v_a_2029_; 
v_a_2029_ = lean_ctor_get(v___x_2028_, 0);
lean_inc(v_a_2029_);
lean_dec_ref_known(v___x_2028_, 1);
if (lean_obj_tag(v_a_2029_) == 1)
{
lean_object* v_val_2030_; lean_object* v_fst_2031_; lean_object* v_snd_2032_; lean_object* v___x_2033_; 
lean_dec_ref(v_e_1984_);
v_val_2030_ = lean_ctor_get(v_a_2029_, 0);
lean_inc(v_val_2030_);
lean_dec_ref_known(v_a_2029_, 1);
v_fst_2031_ = lean_ctor_get(v_val_2030_, 0);
lean_inc(v_fst_2031_);
v_snd_2032_ = lean_ctor_get(v_val_2030_, 1);
lean_inc(v_snd_2032_);
lean_dec(v_val_2030_);
lean_inc(v_a_1995_);
lean_inc_ref(v_a_1994_);
lean_inc(v_a_1993_);
lean_inc_ref(v_a_1992_);
lean_inc(v_a_1991_);
lean_inc_ref(v_a_1990_);
lean_inc(v_a_1989_);
lean_inc_ref(v_a_1988_);
lean_inc(v_a_1987_);
lean_inc(v_a_1986_);
v___x_2033_ = lean_grind_cutsat_mk_var(v_snd_2032_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2042_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2036_ = v___x_2033_;
v_isShared_2037_ = v_isSharedCheck_2042_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_2033_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2042_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2038_; lean_object* v___x_2040_; 
v___x_2038_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2038_, 0, v_fst_2031_);
lean_ctor_set(v___x_2038_, 1, v_a_2034_);
lean_ctor_set(v___x_2038_, 2, v_p_1985_);
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 0, v___x_2038_);
v___x_2040_ = v___x_2036_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2038_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
else
{
lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2050_; 
lean_dec(v_fst_2031_);
lean_dec_ref(v_p_1985_);
v_a_2043_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2045_ = v___x_2033_;
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_2033_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2048_; 
if (v_isShared_2046_ == 0)
{
v___x_2048_ = v___x_2045_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2043_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
else
{
lean_object* v___x_2051_; 
lean_dec(v_a_2029_);
lean_inc_ref(v_e_1984_);
v___x_2051_ = l_Lean_Meta_getIntValue_x3f(v_e_1984_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2093_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2054_ = v___x_2051_;
v_isShared_2055_ = v_isSharedCheck_2093_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2051_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2093_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
if (lean_obj_tag(v_a_2052_) == 1)
{
lean_object* v_val_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2092_; 
v_val_2056_ = lean_ctor_get(v_a_2052_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v_a_2052_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2058_ = v_a_2052_;
v_isShared_2059_ = v_isSharedCheck_2092_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_val_2056_);
lean_dec(v_a_2052_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2092_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
uint8_t v___x_2060_; 
v___x_2060_ = l_Int_Linear_Poly_isZero(v_p_1985_);
if (v___x_2060_ == 0)
{
lean_object* v___x_2061_; 
lean_del_object(v___x_2058_);
lean_dec(v_val_2056_);
lean_del_object(v___x_2054_);
v___x_2061_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1990_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; uint8_t v___x_2063_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
lean_inc(v_a_2062_);
lean_dec_ref_known(v___x_2061_, 1);
v___x_2063_ = lean_unbox(v_a_2062_);
lean_dec(v_a_2062_);
if (v___x_2063_ == 0)
{
v___y_1998_ = v_a_1986_;
v___y_1999_ = v_a_1987_;
v___y_2000_ = v_a_1988_;
v___y_2001_ = v_a_1989_;
v___y_2002_ = v_a_1990_;
v___y_2003_ = v_a_1991_;
v___y_2004_ = v_a_1992_;
v___y_2005_ = v_a_1993_;
v___y_2006_ = v_a_1994_;
v___y_2007_ = v_a_1995_;
goto v___jp_1997_;
}
else
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2064_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2);
lean_inc_ref(v_e_1984_);
v___x_2065_ = l_Lean_indentExpr(v_e_1984_);
v___x_2066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2064_);
lean_ctor_set(v___x_2066_, 1, v___x_2065_);
v___x_2067_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4);
v___x_2068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2066_);
lean_ctor_set(v___x_2068_, 1, v___x_2067_);
v___x_2069_ = l_Lean_Meta_Sym_reportIssue(v___x_2068_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_dec_ref_known(v___x_2069_, 1);
v___y_1998_ = v_a_1986_;
v___y_1999_ = v_a_1987_;
v___y_2000_ = v_a_1988_;
v___y_2001_ = v_a_1989_;
v___y_2002_ = v_a_1990_;
v___y_2003_ = v_a_1991_;
v___y_2004_ = v_a_1992_;
v___y_2005_ = v_a_1993_;
v___y_2006_ = v_a_1994_;
v___y_2007_ = v_a_1995_;
goto v___jp_1997_;
}
else
{
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2077_; 
lean_dec_ref(v_p_1985_);
lean_dec_ref(v_e_1984_);
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2072_ = v___x_2069_;
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_2069_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2075_; 
if (v_isShared_2073_ == 0)
{
v___x_2075_ = v___x_2072_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_a_2070_);
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
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
lean_dec_ref(v_p_1985_);
lean_dec_ref(v_e_1984_);
v_a_2078_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2080_ = v___x_2061_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_2061_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2081_ == 0)
{
v___x_2083_ = v___x_2080_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_a_2078_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
else
{
lean_object* v___x_2087_; 
lean_dec_ref(v_p_1985_);
lean_dec_ref(v_e_1984_);
if (v_isShared_2059_ == 0)
{
lean_ctor_set_tag(v___x_2058_, 0);
v___x_2087_ = v___x_2058_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_val_2056_);
v___x_2087_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
lean_object* v___x_2089_; 
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 0, v___x_2087_);
v___x_2089_ = v___x_2054_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v___x_2087_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
}
}
else
{
lean_del_object(v___x_2054_);
lean_dec(v_a_2052_);
v___y_1998_ = v_a_1986_;
v___y_1999_ = v_a_1987_;
v___y_2000_ = v_a_1988_;
v___y_2001_ = v_a_1989_;
v___y_2002_ = v_a_1990_;
v___y_2003_ = v_a_1991_;
v___y_2004_ = v_a_1992_;
v___y_2005_ = v_a_1993_;
v___y_2006_ = v_a_1994_;
v___y_2007_ = v_a_1995_;
goto v___jp_1997_;
}
}
}
else
{
lean_object* v_a_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2101_; 
lean_dec_ref(v_p_1985_);
lean_dec_ref(v_e_1984_);
v_a_2094_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2096_ = v___x_2051_;
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_a_2094_);
lean_dec(v___x_2051_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2099_; 
if (v_isShared_2097_ == 0)
{
v___x_2099_ = v___x_2096_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_a_2094_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
}
}
else
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2109_; 
lean_dec_ref(v_p_1985_);
lean_dec_ref(v_e_1984_);
v_a_2102_ = lean_ctor_get(v___x_2028_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2104_ = v___x_2028_;
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2028_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2105_ == 0)
{
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_a_2102_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
v___jp_1997_:
{
lean_object* v___x_2008_; 
lean_inc(v___y_2007_);
lean_inc_ref(v___y_2006_);
lean_inc(v___y_2005_);
lean_inc_ref(v___y_2004_);
lean_inc(v___y_2003_);
lean_inc_ref(v___y_2002_);
lean_inc(v___y_2001_);
lean_inc_ref(v___y_2000_);
lean_inc(v___y_1999_);
lean_inc(v___y_1998_);
v___x_2008_ = lean_grind_cutsat_mk_var(v_e_1984_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2018_; 
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2011_ = v___x_2008_;
v_isShared_2012_ = v_isSharedCheck_2018_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___x_2008_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2018_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2016_; 
v___x_2013_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0);
v___x_2014_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2013_);
lean_ctor_set(v___x_2014_, 1, v_a_2009_);
lean_ctor_set(v___x_2014_, 2, v_p_1985_);
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 0, v___x_2014_);
v___x_2016_ = v___x_2011_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2014_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
else
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2026_; 
lean_dec_ref(v_p_1985_);
v_a_2019_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2021_ = v___x_2008_;
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_2008_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2024_; 
if (v_isShared_2022_ == 0)
{
v___x_2024_ = v___x_2021_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_a_2019_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___boxed(lean_object* v_e_2110_, lean_object* v_p_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_e_2110_, v_p_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_);
lean_dec(v_a_2121_);
lean_dec_ref(v_a_2120_);
lean_dec(v_a_2119_);
lean_dec_ref(v_a_2118_);
lean_dec(v_a_2117_);
lean_dec_ref(v_a_2116_);
lean_dec(v_a_2115_);
lean_dec_ref(v_a_2114_);
lean_dec(v_a_2113_);
lean_dec(v_a_2112_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go(lean_object* v_e_2124_, lean_object* v_p_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_){
_start:
{
uint8_t v___x_2137_; lean_object* v___x_2138_; 
v___x_2137_ = 1;
lean_inc_ref(v_e_2124_);
v___x_2138_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_2124_, v___x_2137_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2139_);
lean_dec_ref_known(v___x_2138_, 1);
if (lean_obj_tag(v_a_2139_) == 1)
{
lean_object* v_val_2140_; lean_object* v_fst_2141_; lean_object* v_snd_2142_; lean_object* v___x_2143_; 
lean_dec_ref(v_e_2124_);
v_val_2140_ = lean_ctor_get(v_a_2139_, 0);
lean_inc(v_val_2140_);
lean_dec_ref_known(v_a_2139_, 1);
v_fst_2141_ = lean_ctor_get(v_val_2140_, 0);
lean_inc(v_fst_2141_);
v_snd_2142_ = lean_ctor_get(v_val_2140_, 1);
lean_inc(v_snd_2142_);
lean_dec(v_val_2140_);
v___x_2143_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_snd_2142_, v_p_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_a_2144_);
lean_dec_ref_known(v___x_2143_, 1);
v_e_2124_ = v_fst_2141_;
v_p_2125_ = v_a_2144_;
goto _start;
}
else
{
lean_dec(v_fst_2141_);
return v___x_2143_;
}
}
else
{
lean_object* v___x_2146_; 
lean_dec(v_a_2139_);
v___x_2146_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_e_2124_, v_p_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_);
return v___x_2146_;
}
}
else
{
lean_object* v_a_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2154_; 
lean_dec_ref(v_p_2125_);
lean_dec_ref(v_e_2124_);
v_a_2147_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2149_ = v___x_2138_;
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_a_2147_);
lean_dec(v___x_2138_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2152_; 
if (v_isShared_2150_ == 0)
{
v___x_2152_ = v___x_2149_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_a_2147_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go___boxed(lean_object* v_e_2155_, lean_object* v_p_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_){
_start:
{
lean_object* v_res_2168_; 
v_res_2168_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go(v_e_2155_, v_p_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_);
lean_dec(v_a_2166_);
lean_dec_ref(v_a_2165_);
lean_dec(v_a_2164_);
lean_dec_ref(v_a_2163_);
lean_dec(v_a_2162_);
lean_dec_ref(v_a_2161_);
lean_dec(v_a_2160_);
lean_dec_ref(v_a_2159_);
lean_dec(v_a_2158_);
lean_dec(v_a_2157_);
return v_res_2168_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0(void){
_start:
{
lean_object* v___x_2169_; lean_object* v___x_2170_; 
v___x_2169_ = lean_unsigned_to_nat(0u);
v___x_2170_ = lean_nat_to_int(v___x_2169_);
return v___x_2170_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1(void){
_start:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2171_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0);
v___x_2172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2171_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly(lean_object* v_e_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_){
_start:
{
uint8_t v___x_2185_; lean_object* v___x_2186_; 
v___x_2185_ = 1;
lean_inc_ref(v_e_2173_);
v___x_2186_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_2173_, v___x_2185_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_object* v_a_2187_; 
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
lean_inc(v_a_2187_);
lean_dec_ref_known(v___x_2186_, 1);
if (lean_obj_tag(v_a_2187_) == 1)
{
lean_object* v_val_2188_; lean_object* v_fst_2189_; lean_object* v_snd_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
lean_dec_ref(v_e_2173_);
v_val_2188_ = lean_ctor_get(v_a_2187_, 0);
lean_inc(v_val_2188_);
lean_dec_ref_known(v_a_2187_, 1);
v_fst_2189_ = lean_ctor_get(v_val_2188_, 0);
lean_inc(v_fst_2189_);
v_snd_2190_ = lean_ctor_get(v_val_2188_, 1);
lean_inc(v_snd_2190_);
lean_dec(v_val_2188_);
v___x_2191_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1);
v___x_2192_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_snd_2190_, v___x_2191_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v_a_2193_; lean_object* v___x_2194_; 
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_a_2193_);
lean_dec_ref_known(v___x_2192_, 1);
v___x_2194_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go(v_fst_2189_, v_a_2193_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_);
return v___x_2194_;
}
else
{
lean_dec(v_fst_2189_);
return v___x_2192_;
}
}
else
{
lean_object* v___x_2195_; lean_object* v___x_2196_; 
lean_dec(v_a_2187_);
v___x_2195_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1);
v___x_2196_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_e_2173_, v___x_2195_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_);
return v___x_2196_;
}
}
else
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2204_; 
lean_dec_ref(v_e_2173_);
v_a_2197_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2199_ = v___x_2186_;
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___x_2186_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2202_; 
if (v_isShared_2200_ == 0)
{
v___x_2202_ = v___x_2199_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_a_2197_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly___boxed(lean_object* v_e_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_e_2205_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_);
lean_dec(v_a_2215_);
lean_dec_ref(v_a_2214_);
lean_dec(v_a_2213_);
lean_dec_ref(v_a_2212_);
lean_dec(v_a_2211_);
lean_dec_ref(v_a_2210_);
lean_dec(v_a_2209_);
lean_dec_ref(v_a_2208_);
lean_dec(v_a_2207_);
lean_dec(v_a_2206_);
return v_res_2217_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_IntInstTesters(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(builtin);
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
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(uint8_t builtin);
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
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(builtin);
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
