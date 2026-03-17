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
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHAddInt___redArg(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__2;
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3_spec__6___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__3___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__3___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__3___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__3___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 4, .m_data = " ↦ #"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__6;
LEAN_EXPORT lean_object* lean_grind_cutsat_mk_var(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3_spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNonlinearTerm___boxed(lean_object* v_y_14_, lean_object* v_x_15_, lean_object* v_a_00___x40___internal___hyg_16_, lean_object* v_a_00___x40___internal___hyg_17_, lean_object* v_a_00___x40___internal___hyg_18_, lean_object* v_a_00___x40___internal___hyg_19_, lean_object* v_a_00___x40___internal___hyg_20_, lean_object* v_a_00___x40___internal___hyg_21_, lean_object* v_a_00___x40___internal___hyg_22_, lean_object* v_a_00___x40___internal___hyg_23_, lean_object* v_a_00___x40___internal___hyg_24_, lean_object* v_a_00___x40___internal___hyg_25_, lean_object* v_a_00___x40___internal___hyg_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = lean_cutsat_propagate_nonlinear(v_y_14_, v_x_15_, v_a_00___x40___internal___hyg_16_, v_a_00___x40___internal___hyg_17_, v_a_00___x40___internal___hyg_18_, v_a_00___x40___internal___hyg_19_, v_a_00___x40___internal___hyg_20_, v_a_00___x40___internal___hyg_21_, v_a_00___x40___internal___hyg_22_, v_a_00___x40___internal___hyg_23_, v_a_00___x40___internal___hyg_24_, v_a_00___x40___internal___hyg_25_);
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
lean_dec(v_a_52_);
lean_dec_ref(v_a_51_);
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
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
lean_dec(v_a_52_);
lean_dec_ref(v_a_51_);
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
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
lean_dec(v_a_52_);
lean_dec_ref(v_a_51_);
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
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
lean_dec(v_a_52_);
lean_dec_ref(v_a_51_);
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
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
lean_dec(v_a_52_);
lean_dec_ref(v_a_51_);
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
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
lean_dec(v_a_52_);
lean_dec_ref(v_a_51_);
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
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
lean_dec(v_a_52_);
lean_dec_ref(v_a_51_);
lean_dec_ref(v_a_49_);
v___x_87_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11));
v___x_88_ = l_Lean_Expr_isConstOf(v___x_80_, v___x_87_);
lean_dec_ref(v___x_80_);
if (v___x_88_ == 0)
{
lean_dec_ref(v_arg_73_);
lean_dec(v_a_50_);
goto v___jp_59_;
}
else
{
lean_object* v___x_89_; 
lean_del_object(v___x_57_);
v___x_89_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_73_, v_a_50_);
lean_dec(v_a_50_);
return v___x_89_;
}
}
else
{
lean_object* v___x_90_; 
lean_dec_ref(v___x_80_);
lean_del_object(v___x_57_);
lean_inc(v_a_50_);
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
lean_dec(v_a_50_);
return v___x_95_;
}
else
{
lean_object* v___x_96_; lean_object* v___x_98_; 
lean_dec_ref(v_a_91_);
lean_dec_ref(v_arg_73_);
lean_dec(v_a_50_);
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
lean_dec(v_a_50_);
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
lean_inc(v_a_50_);
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
lean_dec(v_a_50_);
return v___x_114_;
}
else
{
lean_object* v___x_115_; lean_object* v___x_117_; 
lean_dec_ref(v_a_110_);
lean_dec_ref(v_arg_73_);
lean_dec(v_a_50_);
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
lean_dec(v_a_50_);
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
lean_dec(v_a_52_);
lean_dec_ref(v_a_51_);
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
return v___x_128_;
}
else
{
lean_object* v___x_131_; 
lean_dec_ref(v___x_128_);
lean_inc(v_a_52_);
lean_inc_ref(v_a_51_);
lean_inc(v_a_50_);
lean_inc_ref(v_a_49_);
v___x_131_ = l_Lean_Meta_getIntValue_x3f(v_arg_70_, v_a_49_, v_a_50_, v_a_51_, v_a_52_);
if (lean_obj_tag(v___x_131_) == 0)
{
lean_object* v_a_132_; lean_object* v___x_133_; 
v_a_132_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_a_132_);
lean_dec_ref(v___x_131_);
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
lean_dec_ref(v_a_132_);
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
lean_dec_ref(v_a_143_);
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
lean_dec(v_a_52_);
lean_dec_ref(v_a_51_);
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
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
lean_dec(v_a_52_);
lean_dec_ref(v_a_51_);
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
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
lean_dec(v_a_52_);
lean_dec_ref(v_a_51_);
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
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
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_223_; size_t v___x_224_; size_t v___x_225_; 
v___x_223_ = ((size_t)5ULL);
v___x_224_ = ((size_t)1ULL);
v___x_225_ = lean_usize_shift_left(v___x_224_, v___x_223_);
return v___x_225_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_226_; size_t v___x_227_; size_t v___x_228_; 
v___x_226_ = ((size_t)1ULL);
v___x_227_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__0);
v___x_228_ = lean_usize_sub(v___x_227_, v___x_226_);
return v___x_228_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(lean_object* v_x_230_, size_t v_x_231_, size_t v_x_232_, lean_object* v_x_233_, lean_object* v_x_234_){
_start:
{
if (lean_obj_tag(v_x_230_) == 0)
{
lean_object* v_es_235_; size_t v___x_236_; size_t v___x_237_; size_t v___x_238_; size_t v___x_239_; lean_object* v_j_240_; lean_object* v___x_241_; uint8_t v___x_242_; 
v_es_235_ = lean_ctor_get(v_x_230_, 0);
v___x_236_ = ((size_t)5ULL);
v___x_237_ = ((size_t)1ULL);
v___x_238_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1);
v___x_239_ = lean_usize_land(v_x_231_, v___x_238_);
v_j_240_ = lean_usize_to_nat(v___x_239_);
v___x_241_ = lean_array_get_size(v_es_235_);
v___x_242_ = lean_nat_dec_lt(v_j_240_, v___x_241_);
if (v___x_242_ == 0)
{
lean_dec(v_j_240_);
lean_dec(v_x_234_);
lean_dec(v_x_233_);
return v_x_230_;
}
else
{
lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_279_; 
lean_inc_ref(v_es_235_);
v_isSharedCheck_279_ = !lean_is_exclusive(v_x_230_);
if (v_isSharedCheck_279_ == 0)
{
lean_object* v_unused_280_; 
v_unused_280_ = lean_ctor_get(v_x_230_, 0);
lean_dec(v_unused_280_);
v___x_244_ = v_x_230_;
v_isShared_245_ = v_isSharedCheck_279_;
goto v_resetjp_243_;
}
else
{
lean_dec(v_x_230_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_279_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v_v_246_; lean_object* v___x_247_; lean_object* v_xs_x27_248_; lean_object* v___y_250_; 
v_v_246_ = lean_array_fget(v_es_235_, v_j_240_);
v___x_247_ = lean_box(0);
v_xs_x27_248_ = lean_array_fset(v_es_235_, v_j_240_, v___x_247_);
switch(lean_obj_tag(v_v_246_))
{
case 0:
{
lean_object* v_key_255_; lean_object* v_val_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_266_; 
v_key_255_ = lean_ctor_get(v_v_246_, 0);
v_val_256_ = lean_ctor_get(v_v_246_, 1);
v_isSharedCheck_266_ = !lean_is_exclusive(v_v_246_);
if (v_isSharedCheck_266_ == 0)
{
v___x_258_ = v_v_246_;
v_isShared_259_ = v_isSharedCheck_266_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_val_256_);
lean_inc(v_key_255_);
lean_dec(v_v_246_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_266_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
uint8_t v___x_260_; 
v___x_260_ = lean_nat_dec_eq(v_x_233_, v_key_255_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; lean_object* v___x_262_; 
lean_del_object(v___x_258_);
v___x_261_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_255_, v_val_256_, v_x_233_, v_x_234_);
v___x_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
v___y_250_ = v___x_262_;
goto v___jp_249_;
}
else
{
lean_object* v___x_264_; 
lean_dec(v_val_256_);
lean_dec(v_key_255_);
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 1, v_x_234_);
lean_ctor_set(v___x_258_, 0, v_x_233_);
v___x_264_ = v___x_258_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_x_233_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v_x_234_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
v___y_250_ = v___x_264_;
goto v___jp_249_;
}
}
}
}
case 1:
{
lean_object* v_node_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_277_; 
v_node_267_ = lean_ctor_get(v_v_246_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v_v_246_);
if (v_isSharedCheck_277_ == 0)
{
v___x_269_ = v_v_246_;
v_isShared_270_ = v_isSharedCheck_277_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_node_267_);
lean_dec(v_v_246_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_277_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
size_t v___x_271_; size_t v___x_272_; lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_271_ = lean_usize_shift_right(v_x_231_, v___x_236_);
v___x_272_ = lean_usize_add(v_x_232_, v___x_237_);
v___x_273_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_node_267_, v___x_271_, v___x_272_, v_x_233_, v_x_234_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 0, v___x_273_);
v___x_275_ = v___x_269_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_273_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
v___y_250_ = v___x_275_;
goto v___jp_249_;
}
}
}
default: 
{
lean_object* v___x_278_; 
v___x_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_278_, 0, v_x_233_);
lean_ctor_set(v___x_278_, 1, v_x_234_);
v___y_250_ = v___x_278_;
goto v___jp_249_;
}
}
v___jp_249_:
{
lean_object* v___x_251_; lean_object* v___x_253_; 
v___x_251_ = lean_array_fset(v_xs_x27_248_, v_j_240_, v___y_250_);
lean_dec(v_j_240_);
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 0, v___x_251_);
v___x_253_ = v___x_244_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_251_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
}
}
else
{
lean_object* v_ks_281_; lean_object* v_vs_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_302_; 
v_ks_281_ = lean_ctor_get(v_x_230_, 0);
v_vs_282_ = lean_ctor_get(v_x_230_, 1);
v_isSharedCheck_302_ = !lean_is_exclusive(v_x_230_);
if (v_isSharedCheck_302_ == 0)
{
v___x_284_ = v_x_230_;
v_isShared_285_ = v_isSharedCheck_302_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_vs_282_);
lean_inc(v_ks_281_);
lean_dec(v_x_230_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_302_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_287_; 
if (v_isShared_285_ == 0)
{
v___x_287_ = v___x_284_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_ks_281_);
lean_ctor_set(v_reuseFailAlloc_301_, 1, v_vs_282_);
v___x_287_ = v_reuseFailAlloc_301_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
lean_object* v_newNode_288_; uint8_t v___y_290_; size_t v___x_296_; uint8_t v___x_297_; 
v_newNode_288_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1___redArg(v___x_287_, v_x_233_, v_x_234_);
v___x_296_ = ((size_t)7ULL);
v___x_297_ = lean_usize_dec_le(v___x_296_, v_x_232_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_298_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_288_);
v___x_299_ = lean_unsigned_to_nat(4u);
v___x_300_ = lean_nat_dec_lt(v___x_298_, v___x_299_);
lean_dec(v___x_298_);
v___y_290_ = v___x_300_;
goto v___jp_289_;
}
else
{
v___y_290_ = v___x_297_;
goto v___jp_289_;
}
v___jp_289_:
{
if (v___y_290_ == 0)
{
lean_object* v_ks_291_; lean_object* v_vs_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v_ks_291_ = lean_ctor_get(v_newNode_288_, 0);
lean_inc_ref(v_ks_291_);
v_vs_292_ = lean_ctor_get(v_newNode_288_, 1);
lean_inc_ref(v_vs_292_);
lean_dec_ref(v_newNode_288_);
v___x_293_ = lean_unsigned_to_nat(0u);
v___x_294_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__2);
v___x_295_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg(v_x_232_, v_ks_291_, v_vs_292_, v___x_293_, v___x_294_);
lean_dec_ref(v_vs_292_);
lean_dec_ref(v_ks_291_);
return v___x_295_;
}
else
{
return v_newNode_288_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg(size_t v_depth_303_, lean_object* v_keys_304_, lean_object* v_vals_305_, lean_object* v_i_306_, lean_object* v_entries_307_){
_start:
{
lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_308_ = lean_array_get_size(v_keys_304_);
v___x_309_ = lean_nat_dec_lt(v_i_306_, v___x_308_);
if (v___x_309_ == 0)
{
lean_dec(v_i_306_);
return v_entries_307_;
}
else
{
lean_object* v_k_310_; lean_object* v_v_311_; uint64_t v___x_312_; size_t v_h_313_; size_t v___x_314_; lean_object* v___x_315_; size_t v___x_316_; size_t v___x_317_; size_t v___x_318_; size_t v_h_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v_k_310_ = lean_array_fget_borrowed(v_keys_304_, v_i_306_);
v_v_311_ = lean_array_fget_borrowed(v_vals_305_, v_i_306_);
v___x_312_ = lean_uint64_of_nat(v_k_310_);
v_h_313_ = lean_uint64_to_usize(v___x_312_);
v___x_314_ = ((size_t)5ULL);
v___x_315_ = lean_unsigned_to_nat(1u);
v___x_316_ = ((size_t)1ULL);
v___x_317_ = lean_usize_sub(v_depth_303_, v___x_316_);
v___x_318_ = lean_usize_mul(v___x_314_, v___x_317_);
v_h_319_ = lean_usize_shift_right(v_h_313_, v___x_318_);
v___x_320_ = lean_nat_add(v_i_306_, v___x_315_);
lean_dec(v_i_306_);
lean_inc(v_v_311_);
lean_inc(v_k_310_);
v___x_321_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_entries_307_, v_h_319_, v_depth_303_, v_k_310_, v_v_311_);
v_i_306_ = v___x_320_;
v_entries_307_ = v___x_321_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_323_, lean_object* v_keys_324_, lean_object* v_vals_325_, lean_object* v_i_326_, lean_object* v_entries_327_){
_start:
{
size_t v_depth_boxed_328_; lean_object* v_res_329_; 
v_depth_boxed_328_ = lean_unbox_usize(v_depth_323_);
lean_dec(v_depth_323_);
v_res_329_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg(v_depth_boxed_328_, v_keys_324_, v_vals_325_, v_i_326_, v_entries_327_);
lean_dec_ref(v_vals_325_);
lean_dec_ref(v_keys_324_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___boxed(lean_object* v_x_330_, lean_object* v_x_331_, lean_object* v_x_332_, lean_object* v_x_333_, lean_object* v_x_334_){
_start:
{
size_t v_x_9175__boxed_335_; size_t v_x_9176__boxed_336_; lean_object* v_res_337_; 
v_x_9175__boxed_335_ = lean_unbox_usize(v_x_331_);
lean_dec(v_x_331_);
v_x_9176__boxed_336_ = lean_unbox_usize(v_x_332_);
lean_dec(v_x_332_);
v_res_337_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_x_330_, v_x_9175__boxed_335_, v_x_9176__boxed_336_, v_x_333_, v_x_334_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0___redArg(lean_object* v_x_338_, lean_object* v_x_339_, lean_object* v_x_340_){
_start:
{
uint64_t v___x_341_; size_t v___x_342_; size_t v___x_343_; lean_object* v___x_344_; 
v___x_341_ = lean_uint64_of_nat(v_x_339_);
v___x_342_ = lean_uint64_to_usize(v___x_341_);
v___x_343_ = ((size_t)1ULL);
v___x_344_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_x_338_, v___x_342_, v___x_343_, v_x_339_, v_x_340_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___lam__0(lean_object* v_x_345_, lean_object* v___y_346_, lean_object* v_a_347_, lean_object* v_s_348_){
_start:
{
lean_object* v_vars_349_; lean_object* v_varMap_350_; lean_object* v_vars_x27_351_; lean_object* v_varMap_x27_352_; lean_object* v_natToIntMap_353_; lean_object* v_natDef_354_; lean_object* v_dvds_355_; lean_object* v_lowers_356_; lean_object* v_uppers_357_; lean_object* v_diseqs_358_; lean_object* v_elimEqs_359_; lean_object* v_elimStack_360_; lean_object* v_occurs_361_; lean_object* v_assignment_362_; lean_object* v_nextCnstrId_363_; uint8_t v_caseSplits_364_; lean_object* v_conflict_x3f_365_; lean_object* v_diseqSplits_366_; lean_object* v_divMod_367_; lean_object* v_toIntIds_368_; lean_object* v_toIntInfos_369_; lean_object* v_toIntTermMap_370_; lean_object* v_toIntVarMap_371_; uint8_t v_usedCommRing_372_; lean_object* v_nonlinearOccs_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_382_; 
v_vars_349_ = lean_ctor_get(v_s_348_, 0);
v_varMap_350_ = lean_ctor_get(v_s_348_, 1);
v_vars_x27_351_ = lean_ctor_get(v_s_348_, 2);
v_varMap_x27_352_ = lean_ctor_get(v_s_348_, 3);
v_natToIntMap_353_ = lean_ctor_get(v_s_348_, 4);
v_natDef_354_ = lean_ctor_get(v_s_348_, 5);
v_dvds_355_ = lean_ctor_get(v_s_348_, 6);
v_lowers_356_ = lean_ctor_get(v_s_348_, 7);
v_uppers_357_ = lean_ctor_get(v_s_348_, 8);
v_diseqs_358_ = lean_ctor_get(v_s_348_, 9);
v_elimEqs_359_ = lean_ctor_get(v_s_348_, 10);
v_elimStack_360_ = lean_ctor_get(v_s_348_, 11);
v_occurs_361_ = lean_ctor_get(v_s_348_, 12);
v_assignment_362_ = lean_ctor_get(v_s_348_, 13);
v_nextCnstrId_363_ = lean_ctor_get(v_s_348_, 14);
v_caseSplits_364_ = lean_ctor_get_uint8(v_s_348_, sizeof(void*)*23);
v_conflict_x3f_365_ = lean_ctor_get(v_s_348_, 15);
v_diseqSplits_366_ = lean_ctor_get(v_s_348_, 16);
v_divMod_367_ = lean_ctor_get(v_s_348_, 17);
v_toIntIds_368_ = lean_ctor_get(v_s_348_, 18);
v_toIntInfos_369_ = lean_ctor_get(v_s_348_, 19);
v_toIntTermMap_370_ = lean_ctor_get(v_s_348_, 20);
v_toIntVarMap_371_ = lean_ctor_get(v_s_348_, 21);
v_usedCommRing_372_ = lean_ctor_get_uint8(v_s_348_, sizeof(void*)*23 + 1);
v_nonlinearOccs_373_ = lean_ctor_get(v_s_348_, 22);
v_isSharedCheck_382_ = !lean_is_exclusive(v_s_348_);
if (v_isSharedCheck_382_ == 0)
{
v___x_375_ = v_s_348_;
v_isShared_376_ = v_isSharedCheck_382_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_nonlinearOccs_373_);
lean_inc(v_toIntVarMap_371_);
lean_inc(v_toIntTermMap_370_);
lean_inc(v_toIntInfos_369_);
lean_inc(v_toIntIds_368_);
lean_inc(v_divMod_367_);
lean_inc(v_diseqSplits_366_);
lean_inc(v_conflict_x3f_365_);
lean_inc(v_nextCnstrId_363_);
lean_inc(v_assignment_362_);
lean_inc(v_occurs_361_);
lean_inc(v_elimStack_360_);
lean_inc(v_elimEqs_359_);
lean_inc(v_diseqs_358_);
lean_inc(v_uppers_357_);
lean_inc(v_lowers_356_);
lean_inc(v_dvds_355_);
lean_inc(v_natDef_354_);
lean_inc(v_natToIntMap_353_);
lean_inc(v_varMap_x27_352_);
lean_inc(v_vars_x27_351_);
lean_inc(v_varMap_350_);
lean_inc(v_vars_349_);
lean_dec(v_s_348_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_382_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_380_; 
v___x_377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_377_, 0, v_x_345_);
lean_ctor_set(v___x_377_, 1, v___y_346_);
v___x_378_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0___redArg(v_nonlinearOccs_373_, v_a_347_, v___x_377_);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 22, v___x_378_);
v___x_380_ = v___x_375_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_vars_349_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v_varMap_350_);
lean_ctor_set(v_reuseFailAlloc_381_, 2, v_vars_x27_351_);
lean_ctor_set(v_reuseFailAlloc_381_, 3, v_varMap_x27_352_);
lean_ctor_set(v_reuseFailAlloc_381_, 4, v_natToIntMap_353_);
lean_ctor_set(v_reuseFailAlloc_381_, 5, v_natDef_354_);
lean_ctor_set(v_reuseFailAlloc_381_, 6, v_dvds_355_);
lean_ctor_set(v_reuseFailAlloc_381_, 7, v_lowers_356_);
lean_ctor_set(v_reuseFailAlloc_381_, 8, v_uppers_357_);
lean_ctor_set(v_reuseFailAlloc_381_, 9, v_diseqs_358_);
lean_ctor_set(v_reuseFailAlloc_381_, 10, v_elimEqs_359_);
lean_ctor_set(v_reuseFailAlloc_381_, 11, v_elimStack_360_);
lean_ctor_set(v_reuseFailAlloc_381_, 12, v_occurs_361_);
lean_ctor_set(v_reuseFailAlloc_381_, 13, v_assignment_362_);
lean_ctor_set(v_reuseFailAlloc_381_, 14, v_nextCnstrId_363_);
lean_ctor_set(v_reuseFailAlloc_381_, 15, v_conflict_x3f_365_);
lean_ctor_set(v_reuseFailAlloc_381_, 16, v_diseqSplits_366_);
lean_ctor_set(v_reuseFailAlloc_381_, 17, v_divMod_367_);
lean_ctor_set(v_reuseFailAlloc_381_, 18, v_toIntIds_368_);
lean_ctor_set(v_reuseFailAlloc_381_, 19, v_toIntInfos_369_);
lean_ctor_set(v_reuseFailAlloc_381_, 20, v_toIntTermMap_370_);
lean_ctor_set(v_reuseFailAlloc_381_, 21, v_toIntVarMap_371_);
lean_ctor_set(v_reuseFailAlloc_381_, 22, v___x_378_);
lean_ctor_set_uint8(v_reuseFailAlloc_381_, sizeof(void*)*23, v_caseSplits_364_);
lean_ctor_set_uint8(v_reuseFailAlloc_381_, sizeof(void*)*23 + 1, v_usedCommRing_372_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5___redArg(lean_object* v_keys_383_, lean_object* v_vals_384_, lean_object* v_i_385_, lean_object* v_k_386_){
_start:
{
lean_object* v___x_387_; uint8_t v___x_388_; 
v___x_387_ = lean_array_get_size(v_keys_383_);
v___x_388_ = lean_nat_dec_lt(v_i_385_, v___x_387_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; 
lean_dec(v_i_385_);
v___x_389_ = lean_box(0);
return v___x_389_;
}
else
{
lean_object* v_k_x27_390_; uint8_t v___x_391_; 
v_k_x27_390_ = lean_array_fget_borrowed(v_keys_383_, v_i_385_);
v___x_391_ = lean_nat_dec_eq(v_k_386_, v_k_x27_390_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = lean_unsigned_to_nat(1u);
v___x_393_ = lean_nat_add(v_i_385_, v___x_392_);
lean_dec(v_i_385_);
v_i_385_ = v___x_393_;
goto _start;
}
else
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = lean_array_fget_borrowed(v_vals_384_, v_i_385_);
lean_dec(v_i_385_);
lean_inc(v___x_395_);
v___x_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
return v___x_396_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_keys_397_, lean_object* v_vals_398_, lean_object* v_i_399_, lean_object* v_k_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5___redArg(v_keys_397_, v_vals_398_, v_i_399_, v_k_400_);
lean_dec(v_k_400_);
lean_dec_ref(v_vals_398_);
lean_dec_ref(v_keys_397_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2___redArg(lean_object* v_x_402_, size_t v_x_403_, lean_object* v_x_404_){
_start:
{
if (lean_obj_tag(v_x_402_) == 0)
{
lean_object* v_es_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_426_; 
v_es_405_ = lean_ctor_get(v_x_402_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v_x_402_);
if (v_isSharedCheck_426_ == 0)
{
v___x_407_ = v_x_402_;
v_isShared_408_ = v_isSharedCheck_426_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_es_405_);
lean_dec(v_x_402_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_426_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_409_; size_t v___x_410_; size_t v___x_411_; size_t v___x_412_; lean_object* v_j_413_; lean_object* v___x_414_; 
v___x_409_ = lean_box(2);
v___x_410_ = ((size_t)5ULL);
v___x_411_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1);
v___x_412_ = lean_usize_land(v_x_403_, v___x_411_);
v_j_413_ = lean_usize_to_nat(v___x_412_);
v___x_414_ = lean_array_get(v___x_409_, v_es_405_, v_j_413_);
lean_dec(v_j_413_);
lean_dec_ref(v_es_405_);
switch(lean_obj_tag(v___x_414_))
{
case 0:
{
lean_object* v_key_415_; lean_object* v_val_416_; uint8_t v___x_417_; 
v_key_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc(v_key_415_);
v_val_416_ = lean_ctor_get(v___x_414_, 1);
lean_inc(v_val_416_);
lean_dec_ref(v___x_414_);
v___x_417_ = lean_nat_dec_eq(v_x_404_, v_key_415_);
lean_dec(v_key_415_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; 
lean_dec(v_val_416_);
lean_del_object(v___x_407_);
v___x_418_ = lean_box(0);
return v___x_418_;
}
else
{
lean_object* v___x_420_; 
if (v_isShared_408_ == 0)
{
lean_ctor_set_tag(v___x_407_, 1);
lean_ctor_set(v___x_407_, 0, v_val_416_);
v___x_420_ = v___x_407_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_val_416_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
case 1:
{
lean_object* v_node_422_; size_t v___x_423_; 
lean_del_object(v___x_407_);
v_node_422_ = lean_ctor_get(v___x_414_, 0);
lean_inc(v_node_422_);
lean_dec_ref(v___x_414_);
v___x_423_ = lean_usize_shift_right(v_x_403_, v___x_410_);
v_x_402_ = v_node_422_;
v_x_403_ = v___x_423_;
goto _start;
}
default: 
{
lean_object* v___x_425_; 
lean_del_object(v___x_407_);
v___x_425_ = lean_box(0);
return v___x_425_;
}
}
}
}
else
{
lean_object* v_ks_427_; lean_object* v_vs_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v_ks_427_ = lean_ctor_get(v_x_402_, 0);
lean_inc_ref(v_ks_427_);
v_vs_428_ = lean_ctor_get(v_x_402_, 1);
lean_inc_ref(v_vs_428_);
lean_dec_ref(v_x_402_);
v___x_429_ = lean_unsigned_to_nat(0u);
v___x_430_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5___redArg(v_ks_427_, v_vs_428_, v___x_429_, v_x_404_);
lean_dec_ref(v_vs_428_);
lean_dec_ref(v_ks_427_);
return v___x_430_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2___redArg___boxed(lean_object* v_x_431_, lean_object* v_x_432_, lean_object* v_x_433_){
_start:
{
size_t v_x_9397__boxed_434_; lean_object* v_res_435_; 
v_x_9397__boxed_434_ = lean_unbox_usize(v_x_432_);
lean_dec(v_x_432_);
v_res_435_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2___redArg(v_x_431_, v_x_9397__boxed_434_, v_x_433_);
lean_dec(v_x_433_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___redArg(lean_object* v_x_436_, lean_object* v_x_437_){
_start:
{
uint64_t v___x_438_; size_t v___x_439_; lean_object* v___x_440_; 
v___x_438_ = lean_uint64_of_nat(v_x_437_);
v___x_439_ = lean_uint64_to_usize(v___x_438_);
v___x_440_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2___redArg(v_x_436_, v___x_439_, v_x_437_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___redArg___boxed(lean_object* v_x_441_, lean_object* v_x_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___redArg(v_x_441_, v_x_442_);
lean_dec(v_x_442_);
return v_res_443_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___closed__0(void){
_start:
{
lean_object* v___x_444_; lean_object* v___f_445_; 
v___x_444_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_445_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_445_, 0, v___x_444_);
return v___f_445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(lean_object* v_arg_446_, lean_object* v_x_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_){
_start:
{
lean_object* v___x_459_; 
lean_inc(v_a_457_);
lean_inc_ref(v_a_456_);
lean_inc(v_a_455_);
lean_inc_ref(v_a_454_);
lean_inc(v_a_453_);
lean_inc_ref(v_a_452_);
lean_inc(v_a_451_);
lean_inc_ref(v_a_450_);
lean_inc(v_a_449_);
lean_inc(v_a_448_);
v___x_459_ = lean_grind_cutsat_mk_var(v_arg_446_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_);
if (lean_obj_tag(v___x_459_) == 0)
{
lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_531_; 
v_a_460_ = lean_ctor_get(v___x_459_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_531_ == 0)
{
v___x_462_ = v___x_459_;
v_isShared_463_ = v_isSharedCheck_531_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v___x_459_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_531_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___y_465_; lean_object* v___y_466_; lean_object* v___y_467_; lean_object* v___y_477_; lean_object* v___y_478_; lean_object* v___x_494_; 
v___x_494_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_448_, v_a_456_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v_a_495_; lean_object* v___y_497_; lean_object* v_elimEqs_517_; lean_object* v_size_518_; lean_object* v___x_519_; uint8_t v___x_520_; 
v_a_495_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_a_495_);
lean_dec_ref(v___x_494_);
v_elimEqs_517_ = lean_ctor_get(v_a_495_, 10);
lean_inc_ref(v_elimEqs_517_);
lean_dec(v_a_495_);
v_size_518_ = lean_ctor_get(v_elimEqs_517_, 2);
v___x_519_ = lean_box(0);
v___x_520_ = lean_nat_dec_lt(v_a_460_, v_size_518_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; 
lean_dec_ref(v_elimEqs_517_);
v___x_521_ = l_outOfBounds___redArg(v___x_519_);
v___y_497_ = v___x_521_;
goto v___jp_496_;
}
else
{
lean_object* v___x_522_; 
v___x_522_ = l_Lean_PersistentArray_get_x21___redArg(v___x_519_, v_elimEqs_517_, v_a_460_);
v___y_497_ = v___x_522_;
goto v___jp_496_;
}
v___jp_496_:
{
if (lean_obj_tag(v___y_497_) == 0)
{
lean_dec(v_a_457_);
lean_dec(v_a_455_);
lean_dec_ref(v_a_454_);
lean_dec(v_a_453_);
lean_dec_ref(v_a_452_);
lean_dec(v_a_451_);
lean_dec_ref(v_a_450_);
lean_dec(v_a_449_);
v___y_477_ = v_a_448_;
v___y_478_ = v_a_456_;
goto v___jp_476_;
}
else
{
lean_object* v___x_498_; 
lean_dec_ref(v___y_497_);
lean_inc_ref(v_a_456_);
lean_inc(v_a_448_);
lean_inc(v_x_447_);
lean_inc(v_a_460_);
v___x_498_ = lean_cutsat_propagate_nonlinear(v_a_460_, v_x_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_508_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_508_ == 0)
{
v___x_501_ = v___x_498_;
v_isShared_502_ = v_isSharedCheck_508_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_498_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_508_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
uint8_t v___x_503_; 
v___x_503_ = lean_unbox(v_a_499_);
lean_dec(v_a_499_);
if (v___x_503_ == 0)
{
lean_del_object(v___x_501_);
v___y_477_ = v_a_448_;
v___y_478_ = v_a_456_;
goto v___jp_476_;
}
else
{
lean_object* v___x_504_; lean_object* v___x_506_; 
lean_del_object(v___x_462_);
lean_dec(v_a_460_);
lean_dec_ref(v_a_456_);
lean_dec(v_a_448_);
lean_dec(v_x_447_);
v___x_504_ = lean_box(0);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v___x_504_);
v___x_506_ = v___x_501_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_504_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
else
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_516_; 
lean_del_object(v___x_462_);
lean_dec(v_a_460_);
lean_dec_ref(v_a_456_);
lean_dec(v_a_448_);
lean_dec(v_x_447_);
v_a_509_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_516_ == 0)
{
v___x_511_ = v___x_498_;
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_498_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_512_ == 0)
{
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_509_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
}
}
else
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
lean_del_object(v___x_462_);
lean_dec(v_a_460_);
lean_dec(v_a_457_);
lean_dec_ref(v_a_456_);
lean_dec(v_a_455_);
lean_dec_ref(v_a_454_);
lean_dec(v_a_453_);
lean_dec_ref(v_a_452_);
lean_dec(v_a_451_);
lean_dec_ref(v_a_450_);
lean_dec(v_a_449_);
lean_dec(v_a_448_);
lean_dec(v_x_447_);
v_a_523_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___x_494_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_494_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_a_523_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
v___jp_464_:
{
uint8_t v___x_468_; 
lean_inc(v___y_467_);
lean_inc(v_x_447_);
v___x_468_ = l_List_elem___redArg(v___y_466_, v_x_447_, v___y_467_);
if (v___x_468_ == 0)
{
lean_object* v___f_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
lean_del_object(v___x_462_);
v___f_469_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___lam__0), 4, 3);
lean_closure_set(v___f_469_, 0, v_x_447_);
lean_closure_set(v___f_469_, 1, v___y_467_);
lean_closure_set(v___f_469_, 2, v_a_460_);
v___x_470_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_471_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_470_, v___f_469_, v___y_465_);
lean_dec(v___y_465_);
return v___x_471_;
}
else
{
lean_object* v___x_472_; lean_object* v___x_474_; 
lean_dec(v___y_467_);
lean_dec(v___y_465_);
lean_dec(v_a_460_);
lean_dec(v_x_447_);
v___x_472_ = lean_box(0);
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 0, v___x_472_);
v___x_474_ = v___x_462_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v___x_472_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
v___jp_476_:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v___y_477_, v___y_478_);
lean_dec_ref(v___y_478_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_480_; lean_object* v_nonlinearOccs_481_; lean_object* v___f_482_; lean_object* v___x_483_; 
v_a_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_a_480_);
lean_dec_ref(v___x_479_);
v_nonlinearOccs_481_ = lean_ctor_get(v_a_480_, 22);
lean_inc_ref(v_nonlinearOccs_481_);
lean_dec(v_a_480_);
v___f_482_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___closed__0);
v___x_483_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___redArg(v_nonlinearOccs_481_, v_a_460_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v___x_484_; 
v___x_484_ = lean_box(0);
v___y_465_ = v___y_477_;
v___y_466_ = v___f_482_;
v___y_467_ = v___x_484_;
goto v___jp_464_;
}
else
{
lean_object* v_val_485_; 
v_val_485_ = lean_ctor_get(v___x_483_, 0);
lean_inc(v_val_485_);
lean_dec_ref(v___x_483_);
v___y_465_ = v___y_477_;
v___y_466_ = v___f_482_;
v___y_467_ = v_val_485_;
goto v___jp_464_;
}
}
else
{
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
lean_dec(v___y_477_);
lean_del_object(v___x_462_);
lean_dec(v_a_460_);
lean_dec(v_x_447_);
v_a_486_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_493_ == 0)
{
v___x_488_ = v___x_479_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_479_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_a_486_);
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
}
}
else
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
lean_dec(v_a_457_);
lean_dec_ref(v_a_456_);
lean_dec(v_a_455_);
lean_dec_ref(v_a_454_);
lean_dec(v_a_453_);
lean_dec_ref(v_a_452_);
lean_dec(v_a_451_);
lean_dec_ref(v_a_450_);
lean_dec(v_a_449_);
lean_dec(v_a_448_);
lean_dec(v_x_447_);
v_a_532_ = lean_ctor_get(v___x_459_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_539_ == 0)
{
v___x_534_ = v___x_459_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_459_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_532_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___boxed(lean_object* v_arg_540_, lean_object* v_x_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_arg_540_, v_x_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0(lean_object* v_00_u03b2_554_, lean_object* v_x_555_, lean_object* v_x_556_, lean_object* v_x_557_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0___redArg(v_x_555_, v_x_556_, v_x_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1(lean_object* v_00_u03b2_559_, lean_object* v_x_560_, lean_object* v_x_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___redArg(v_x_560_, v_x_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___boxed(lean_object* v_00_u03b2_563_, lean_object* v_x_564_, lean_object* v_x_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1(v_00_u03b2_563_, v_x_564_, v_x_565_);
lean_dec(v_x_565_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0(lean_object* v_00_u03b2_567_, lean_object* v_x_568_, size_t v_x_569_, size_t v_x_570_, lean_object* v_x_571_, lean_object* v_x_572_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_x_568_, v_x_569_, v_x_570_, v_x_571_, v_x_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___boxed(lean_object* v_00_u03b2_574_, lean_object* v_x_575_, lean_object* v_x_576_, lean_object* v_x_577_, lean_object* v_x_578_, lean_object* v_x_579_){
_start:
{
size_t v_x_9682__boxed_580_; size_t v_x_9683__boxed_581_; lean_object* v_res_582_; 
v_x_9682__boxed_580_ = lean_unbox_usize(v_x_576_);
lean_dec(v_x_576_);
v_x_9683__boxed_581_ = lean_unbox_usize(v_x_577_);
lean_dec(v_x_577_);
v_res_582_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0(v_00_u03b2_574_, v_x_575_, v_x_9682__boxed_580_, v_x_9683__boxed_581_, v_x_578_, v_x_579_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2(lean_object* v_00_u03b2_583_, lean_object* v_x_584_, size_t v_x_585_, lean_object* v_x_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2___redArg(v_x_584_, v_x_585_, v_x_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2___boxed(lean_object* v_00_u03b2_588_, lean_object* v_x_589_, lean_object* v_x_590_, lean_object* v_x_591_){
_start:
{
size_t v_x_9699__boxed_592_; lean_object* v_res_593_; 
v_x_9699__boxed_592_ = lean_unbox_usize(v_x_590_);
lean_dec(v_x_590_);
v_res_593_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2(v_00_u03b2_588_, v_x_589_, v_x_9699__boxed_592_, v_x_591_);
lean_dec(v_x_591_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_594_, lean_object* v_n_595_, lean_object* v_k_596_, lean_object* v_v_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1___redArg(v_n_595_, v_k_596_, v_v_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_599_, size_t v_depth_600_, lean_object* v_keys_601_, lean_object* v_vals_602_, lean_object* v_heq_603_, lean_object* v_i_604_, lean_object* v_entries_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___redArg(v_depth_600_, v_keys_601_, v_vals_602_, v_i_604_, v_entries_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_607_, lean_object* v_depth_608_, lean_object* v_keys_609_, lean_object* v_vals_610_, lean_object* v_heq_611_, lean_object* v_i_612_, lean_object* v_entries_613_){
_start:
{
size_t v_depth_boxed_614_; lean_object* v_res_615_; 
v_depth_boxed_614_ = lean_unbox_usize(v_depth_608_);
lean_dec(v_depth_608_);
v_res_615_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__2(v_00_u03b2_607_, v_depth_boxed_614_, v_keys_609_, v_vals_610_, v_heq_611_, v_i_612_, v_entries_613_);
lean_dec_ref(v_vals_610_);
lean_dec_ref(v_keys_609_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_616_, lean_object* v_keys_617_, lean_object* v_vals_618_, lean_object* v_heq_619_, lean_object* v_i_620_, lean_object* v_k_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5___redArg(v_keys_617_, v_vals_618_, v_i_620_, v_k_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_623_, lean_object* v_keys_624_, lean_object* v_vals_625_, lean_object* v_heq_626_, lean_object* v_i_627_, lean_object* v_k_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5(v_00_u03b2_623_, v_keys_624_, v_vals_625_, v_heq_626_, v_i_627_, v_k_628_);
lean_dec(v_k_628_);
lean_dec_ref(v_vals_625_);
lean_dec_ref(v_keys_624_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_630_, lean_object* v_x_631_, lean_object* v_x_632_, lean_object* v_x_633_, lean_object* v_x_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__3___redArg(v_x_631_, v_x_632_, v_x_633_, v_x_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(lean_object* v_x_636_, lean_object* v_e_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_){
_start:
{
lean_object* v___x_649_; 
lean_inc_ref(v_e_637_);
v___x_649_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_637_, v_a_645_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_a_650_; lean_object* v___x_651_; uint8_t v___x_652_; 
v_a_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_a_650_);
lean_dec_ref(v___x_649_);
v___x_651_ = l_Lean_Expr_cleanupAnnotations(v_a_650_);
v___x_652_ = l_Lean_Expr_isApp(v___x_651_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; 
lean_dec_ref(v___x_651_);
v___x_653_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_637_, v_x_636_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_);
return v___x_653_;
}
else
{
lean_object* v_arg_654_; lean_object* v___x_655_; uint8_t v___x_656_; 
v_arg_654_ = lean_ctor_get(v___x_651_, 1);
lean_inc_ref(v_arg_654_);
v___x_655_ = l_Lean_Expr_appFnCleanup___redArg(v___x_651_);
v___x_656_ = l_Lean_Expr_isApp(v___x_655_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; 
lean_dec_ref(v___x_655_);
lean_dec_ref(v_arg_654_);
v___x_657_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_637_, v_x_636_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_);
return v___x_657_;
}
else
{
lean_object* v_arg_658_; lean_object* v___x_659_; uint8_t v___x_660_; 
v_arg_658_ = lean_ctor_get(v___x_655_, 1);
lean_inc_ref(v_arg_658_);
v___x_659_ = l_Lean_Expr_appFnCleanup___redArg(v___x_655_);
v___x_660_ = l_Lean_Expr_isApp(v___x_659_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; 
lean_dec_ref(v___x_659_);
lean_dec_ref(v_arg_658_);
lean_dec_ref(v_arg_654_);
v___x_661_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_637_, v_x_636_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_);
return v___x_661_;
}
else
{
lean_object* v_arg_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v_arg_662_ = lean_ctor_get(v___x_659_, 1);
lean_inc_ref(v_arg_662_);
v___x_663_ = l_Lean_Expr_appFnCleanup___redArg(v___x_659_);
v___x_664_ = l_Lean_Expr_isApp(v___x_663_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; 
lean_dec_ref(v___x_663_);
lean_dec_ref(v_arg_662_);
lean_dec_ref(v_arg_658_);
lean_dec_ref(v_arg_654_);
v___x_665_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_637_, v_x_636_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_);
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
lean_dec_ref(v_arg_662_);
lean_dec_ref(v_arg_658_);
lean_dec_ref(v_arg_654_);
v___x_668_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_637_, v_x_636_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_);
return v___x_668_;
}
else
{
lean_object* v___x_669_; uint8_t v___x_670_; 
v___x_669_ = l_Lean_Expr_appFnCleanup___redArg(v___x_666_);
v___x_670_ = l_Lean_Expr_isApp(v___x_669_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; 
lean_dec_ref(v___x_669_);
lean_dec_ref(v_arg_662_);
lean_dec_ref(v_arg_658_);
lean_dec_ref(v_arg_654_);
v___x_671_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_637_, v_x_636_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_);
return v___x_671_;
}
else
{
lean_object* v___x_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v___x_672_ = l_Lean_Expr_appFnCleanup___redArg(v___x_669_);
v___x_673_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11));
v___x_674_ = l_Lean_Expr_isConstOf(v___x_672_, v___x_673_);
lean_dec_ref(v___x_672_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; 
lean_dec_ref(v_arg_662_);
lean_dec_ref(v_arg_658_);
lean_dec_ref(v_arg_654_);
v___x_675_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_637_, v_x_636_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_);
return v___x_675_;
}
else
{
lean_object* v___x_676_; 
v___x_676_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_662_, v_a_645_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v_a_677_; uint8_t v___x_678_; 
v_a_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_a_677_);
lean_dec_ref(v___x_676_);
v___x_678_ = lean_unbox(v_a_677_);
lean_dec(v_a_677_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; 
lean_dec_ref(v_arg_658_);
lean_dec_ref(v_arg_654_);
v___x_679_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_e_637_, v_x_636_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_);
return v___x_679_;
}
else
{
lean_object* v___x_680_; 
lean_dec_ref(v_e_637_);
lean_inc(v_a_647_);
lean_inc_ref(v_a_646_);
lean_inc(v_a_645_);
lean_inc_ref(v_a_644_);
lean_inc(v_a_643_);
lean_inc_ref(v_a_642_);
lean_inc(v_a_641_);
lean_inc_ref(v_a_640_);
lean_inc(v_a_639_);
lean_inc(v_a_638_);
lean_inc(v_x_636_);
v___x_680_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(v_x_636_, v_arg_658_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_dec_ref(v___x_680_);
v_e_637_ = v_arg_654_;
goto _start;
}
else
{
lean_dec_ref(v_arg_654_);
lean_dec(v_a_647_);
lean_dec_ref(v_a_646_);
lean_dec(v_a_645_);
lean_dec_ref(v_a_644_);
lean_dec(v_a_643_);
lean_dec_ref(v_a_642_);
lean_dec(v_a_641_);
lean_dec_ref(v_a_640_);
lean_dec(v_a_639_);
lean_dec(v_a_638_);
lean_dec(v_x_636_);
return v___x_680_;
}
}
}
else
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
lean_dec_ref(v_arg_658_);
lean_dec_ref(v_arg_654_);
lean_dec(v_a_647_);
lean_dec_ref(v_a_646_);
lean_dec(v_a_645_);
lean_dec_ref(v_a_644_);
lean_dec(v_a_643_);
lean_dec_ref(v_a_642_);
lean_dec(v_a_641_);
lean_dec_ref(v_a_640_);
lean_dec(v_a_639_);
lean_dec(v_a_638_);
lean_dec_ref(v_e_637_);
lean_dec(v_x_636_);
v_a_682_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_676_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_676_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_682_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
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
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
lean_dec(v_a_647_);
lean_dec_ref(v_a_646_);
lean_dec(v_a_645_);
lean_dec_ref(v_a_644_);
lean_dec(v_a_643_);
lean_dec_ref(v_a_642_);
lean_dec(v_a_641_);
lean_dec_ref(v_a_640_);
lean_dec(v_a_639_);
lean_dec(v_a_638_);
lean_dec_ref(v_e_637_);
lean_dec(v_x_636_);
v_a_690_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_649_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_649_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go___boxed(lean_object* v_x_698_, lean_object* v_e_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(v_x_698_, v_e_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt(lean_object* v_e_712_, lean_object* v_x_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_712_, v_a_721_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_831_; 
v_a_729_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_831_ == 0)
{
v___x_731_ = v___x_728_;
v_isShared_732_ = v_isSharedCheck_831_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_728_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_831_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_738_ = l_Lean_Expr_cleanupAnnotations(v_a_729_);
v___x_739_ = l_Lean_Expr_isApp(v___x_738_);
if (v___x_739_ == 0)
{
lean_dec_ref(v___x_738_);
lean_dec(v_a_723_);
lean_dec_ref(v_a_722_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec(v_a_717_);
lean_dec_ref(v_a_716_);
lean_dec(v_a_715_);
lean_dec(v_a_714_);
lean_dec(v_x_713_);
goto v___jp_733_;
}
else
{
lean_object* v_arg_740_; lean_object* v___x_741_; uint8_t v___x_742_; 
v_arg_740_ = lean_ctor_get(v___x_738_, 1);
lean_inc_ref(v_arg_740_);
v___x_741_ = l_Lean_Expr_appFnCleanup___redArg(v___x_738_);
v___x_742_ = l_Lean_Expr_isApp(v___x_741_);
if (v___x_742_ == 0)
{
lean_dec_ref(v___x_741_);
lean_dec_ref(v_arg_740_);
lean_dec(v_a_723_);
lean_dec_ref(v_a_722_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec(v_a_717_);
lean_dec_ref(v_a_716_);
lean_dec(v_a_715_);
lean_dec(v_a_714_);
lean_dec(v_x_713_);
goto v___jp_733_;
}
else
{
lean_object* v_arg_743_; lean_object* v___x_744_; uint8_t v___x_745_; 
v_arg_743_ = lean_ctor_get(v___x_741_, 1);
lean_inc_ref(v_arg_743_);
v___x_744_ = l_Lean_Expr_appFnCleanup___redArg(v___x_741_);
v___x_745_ = l_Lean_Expr_isApp(v___x_744_);
if (v___x_745_ == 0)
{
lean_dec_ref(v___x_744_);
lean_dec_ref(v_arg_743_);
lean_dec_ref(v_arg_740_);
lean_dec(v_a_723_);
lean_dec_ref(v_a_722_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec(v_a_717_);
lean_dec_ref(v_a_716_);
lean_dec(v_a_715_);
lean_dec(v_a_714_);
lean_dec(v_x_713_);
goto v___jp_733_;
}
else
{
lean_object* v___x_746_; uint8_t v___x_747_; 
v___x_746_ = l_Lean_Expr_appFnCleanup___redArg(v___x_744_);
v___x_747_ = l_Lean_Expr_isApp(v___x_746_);
if (v___x_747_ == 0)
{
lean_dec_ref(v___x_746_);
lean_dec_ref(v_arg_743_);
lean_dec_ref(v_arg_740_);
lean_dec(v_a_723_);
lean_dec_ref(v_a_722_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec(v_a_717_);
lean_dec_ref(v_a_716_);
lean_dec(v_a_715_);
lean_dec(v_a_714_);
lean_dec(v_x_713_);
goto v___jp_733_;
}
else
{
lean_object* v___x_748_; uint8_t v___x_749_; 
v___x_748_ = l_Lean_Expr_appFnCleanup___redArg(v___x_746_);
v___x_749_ = l_Lean_Expr_isApp(v___x_748_);
if (v___x_749_ == 0)
{
lean_dec_ref(v___x_748_);
lean_dec_ref(v_arg_743_);
lean_dec_ref(v_arg_740_);
lean_dec(v_a_723_);
lean_dec_ref(v_a_722_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec(v_a_717_);
lean_dec_ref(v_a_716_);
lean_dec(v_a_715_);
lean_dec(v_a_714_);
lean_dec(v_x_713_);
goto v___jp_733_;
}
else
{
lean_object* v___x_750_; uint8_t v___x_751_; 
v___x_750_ = l_Lean_Expr_appFnCleanup___redArg(v___x_748_);
v___x_751_ = l_Lean_Expr_isApp(v___x_750_);
if (v___x_751_ == 0)
{
lean_dec_ref(v___x_750_);
lean_dec_ref(v_arg_743_);
lean_dec_ref(v_arg_740_);
lean_dec(v_a_723_);
lean_dec_ref(v_a_722_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec(v_a_717_);
lean_dec_ref(v_a_716_);
lean_dec(v_a_715_);
lean_dec(v_a_714_);
lean_dec(v_x_713_);
goto v___jp_733_;
}
else
{
lean_object* v___x_752_; lean_object* v___x_753_; uint8_t v___x_754_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; 
v___x_752_ = l_Lean_Expr_appFnCleanup___redArg(v___x_750_);
v___x_753_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__2));
v___x_754_ = l_Lean_Expr_isConstOf(v___x_752_, v___x_753_);
if (v___x_754_ == 0)
{
lean_object* v___x_810_; uint8_t v___x_811_; 
v___x_810_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__5));
v___x_811_ = l_Lean_Expr_isConstOf(v___x_752_, v___x_810_);
if (v___x_811_ == 0)
{
lean_object* v___x_812_; uint8_t v___x_813_; 
v___x_812_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__8));
v___x_813_ = l_Lean_Expr_isConstOf(v___x_752_, v___x_812_);
if (v___x_813_ == 0)
{
lean_object* v___x_814_; uint8_t v___x_815_; 
v___x_814_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11));
v___x_815_ = l_Lean_Expr_isConstOf(v___x_752_, v___x_814_);
lean_dec_ref(v___x_752_);
if (v___x_815_ == 0)
{
lean_dec_ref(v_arg_743_);
lean_dec_ref(v_arg_740_);
lean_dec(v_a_723_);
lean_dec_ref(v_a_722_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec(v_a_717_);
lean_dec_ref(v_a_716_);
lean_dec(v_a_715_);
lean_dec(v_a_714_);
lean_dec(v_x_713_);
goto v___jp_733_;
}
else
{
lean_object* v___x_816_; 
lean_del_object(v___x_731_);
lean_inc(v_a_723_);
lean_inc_ref(v_a_722_);
lean_inc(v_a_721_);
lean_inc_ref(v_a_720_);
lean_inc(v_a_719_);
lean_inc_ref(v_a_718_);
lean_inc(v_a_717_);
lean_inc_ref(v_a_716_);
lean_inc(v_a_715_);
lean_inc(v_a_714_);
lean_inc(v_x_713_);
v___x_816_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(v_x_713_, v_arg_743_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v___x_817_; 
lean_dec_ref(v___x_816_);
v___x_817_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt_go(v_x_713_, v_arg_740_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
return v___x_817_;
}
else
{
lean_dec_ref(v_arg_740_);
lean_dec(v_a_723_);
lean_dec_ref(v_a_722_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec(v_a_717_);
lean_dec_ref(v_a_716_);
lean_dec(v_a_715_);
lean_dec(v_a_714_);
lean_dec(v_x_713_);
return v___x_816_;
}
}
}
else
{
lean_object* v___x_818_; 
lean_dec_ref(v___x_752_);
lean_dec_ref(v_arg_743_);
lean_del_object(v___x_731_);
v___x_818_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_arg_740_, v_x_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
return v___x_818_;
}
}
else
{
lean_object* v___x_819_; 
lean_dec_ref(v___x_752_);
lean_dec_ref(v_arg_743_);
lean_del_object(v___x_731_);
v___x_819_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_arg_740_, v_x_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
return v___x_819_;
}
}
else
{
lean_object* v___x_820_; 
lean_dec_ref(v___x_752_);
lean_del_object(v___x_731_);
lean_inc(v_a_723_);
lean_inc_ref(v_a_722_);
lean_inc(v_a_721_);
lean_inc_ref(v_a_720_);
lean_inc_ref(v_arg_743_);
v___x_820_ = l_Lean_Meta_getIntValue_x3f(v_arg_743_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_a_821_);
lean_dec_ref(v___x_820_);
if (lean_obj_tag(v_a_821_) == 0)
{
if (v___x_754_ == 0)
{
lean_dec_ref(v_arg_743_);
v___y_756_ = v_a_714_;
v___y_757_ = v_a_715_;
v___y_758_ = v_a_716_;
v___y_759_ = v_a_717_;
v___y_760_ = v_a_718_;
v___y_761_ = v_a_719_;
v___y_762_ = v_a_720_;
v___y_763_ = v_a_721_;
v___y_764_ = v_a_722_;
v___y_765_ = v_a_723_;
goto v___jp_755_;
}
else
{
lean_object* v___x_822_; 
lean_inc(v_a_723_);
lean_inc_ref(v_a_722_);
lean_inc(v_a_721_);
lean_inc_ref(v_a_720_);
lean_inc(v_a_719_);
lean_inc_ref(v_a_718_);
lean_inc(v_a_717_);
lean_inc_ref(v_a_716_);
lean_inc(v_a_715_);
lean_inc(v_a_714_);
lean_inc(v_x_713_);
v___x_822_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_arg_743_, v_x_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_dec_ref(v___x_822_);
v___y_756_ = v_a_714_;
v___y_757_ = v_a_715_;
v___y_758_ = v_a_716_;
v___y_759_ = v_a_717_;
v___y_760_ = v_a_718_;
v___y_761_ = v_a_719_;
v___y_762_ = v_a_720_;
v___y_763_ = v_a_721_;
v___y_764_ = v_a_722_;
v___y_765_ = v_a_723_;
goto v___jp_755_;
}
else
{
lean_dec_ref(v_arg_740_);
lean_dec(v_a_723_);
lean_dec_ref(v_a_722_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec(v_a_717_);
lean_dec_ref(v_a_716_);
lean_dec(v_a_715_);
lean_dec(v_a_714_);
lean_dec(v_x_713_);
return v___x_822_;
}
}
}
else
{
lean_dec_ref(v_a_821_);
lean_dec_ref(v_arg_743_);
v___y_756_ = v_a_714_;
v___y_757_ = v_a_715_;
v___y_758_ = v_a_716_;
v___y_759_ = v_a_717_;
v___y_760_ = v_a_718_;
v___y_761_ = v_a_719_;
v___y_762_ = v_a_720_;
v___y_763_ = v_a_721_;
v___y_764_ = v_a_722_;
v___y_765_ = v_a_723_;
goto v___jp_755_;
}
}
else
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_830_; 
lean_dec_ref(v_arg_743_);
lean_dec_ref(v_arg_740_);
lean_dec(v_a_723_);
lean_dec_ref(v_a_722_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec(v_a_717_);
lean_dec_ref(v_a_716_);
lean_dec(v_a_715_);
lean_dec(v_a_714_);
lean_dec(v_x_713_);
v_a_823_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_830_ == 0)
{
v___x_825_ = v___x_820_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_820_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_823_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
v___jp_755_:
{
lean_object* v___x_766_; 
lean_inc(v___y_765_);
lean_inc_ref(v___y_764_);
lean_inc(v___y_763_);
lean_inc_ref(v___y_762_);
lean_inc_ref(v_arg_740_);
v___x_766_ = l_Lean_Meta_getIntValue_x3f(v_arg_740_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v___x_768_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_a_767_);
lean_dec_ref(v___x_766_);
lean_inc(v___y_765_);
lean_inc_ref(v___y_764_);
lean_inc(v___y_763_);
lean_inc_ref(v___y_762_);
v___x_768_ = l_Lean_Meta_getNatValue_x3f(v_arg_740_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
if (lean_obj_tag(v___x_768_) == 0)
{
if (lean_obj_tag(v_a_767_) == 0)
{
if (v___x_754_ == 0)
{
lean_dec_ref(v___x_768_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec(v___y_756_);
lean_dec_ref(v_arg_740_);
lean_dec(v_x_713_);
goto v___jp_725_;
}
else
{
lean_object* v_a_769_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_a_769_);
lean_dec_ref(v___x_768_);
if (lean_obj_tag(v_a_769_) == 0)
{
lean_object* v___x_770_; 
lean_inc(v___y_765_);
lean_inc_ref(v___y_764_);
lean_inc(v___y_763_);
lean_inc_ref(v___y_762_);
lean_inc(v___y_761_);
lean_inc_ref(v___y_760_);
lean_inc(v___y_759_);
lean_inc_ref(v___y_758_);
lean_inc(v___y_757_);
lean_inc(v___y_756_);
lean_inc_ref(v_arg_740_);
v___x_770_ = l_Lean_Meta_Grind_Arith_Cutsat_mkNatVar(v_arg_740_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; lean_object* v_fst_772_; lean_object* v___x_773_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_a_771_);
lean_dec_ref(v___x_770_);
v_fst_772_ = lean_ctor_get(v_a_771_, 0);
lean_inc(v_fst_772_);
lean_dec(v_a_771_);
v___x_773_ = l_Lean_Meta_Grind_getGeneration___redArg(v_arg_740_, v___y_756_);
lean_dec_ref(v_arg_740_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v_a_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v_a_774_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_a_774_);
lean_dec_ref(v___x_773_);
v___x_775_ = lean_box(0);
lean_inc(v___y_765_);
lean_inc_ref(v___y_764_);
lean_inc(v___y_763_);
lean_inc_ref(v___y_762_);
lean_inc(v___y_761_);
lean_inc_ref(v___y_760_);
lean_inc(v___y_759_);
lean_inc_ref(v___y_758_);
lean_inc(v___y_757_);
lean_inc(v___y_756_);
lean_inc(v_fst_772_);
v___x_776_ = lean_grind_internalize(v_fst_772_, v_a_774_, v___x_775_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v___x_777_; 
lean_dec_ref(v___x_776_);
v___x_777_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(v_fst_772_, v_x_713_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
return v___x_777_;
}
else
{
lean_dec(v_fst_772_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec(v___y_756_);
lean_dec(v_x_713_);
return v___x_776_;
}
}
else
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
lean_dec(v_fst_772_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec(v___y_756_);
lean_dec(v_x_713_);
v_a_778_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_773_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_773_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec(v___y_756_);
lean_dec_ref(v_arg_740_);
lean_dec(v_x_713_);
v_a_786_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_770_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_770_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
else
{
lean_dec_ref(v_a_769_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec(v___y_756_);
lean_dec_ref(v_arg_740_);
lean_dec(v_x_713_);
goto v___jp_725_;
}
}
}
else
{
lean_dec_ref(v_a_767_);
lean_dec_ref(v___x_768_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec(v___y_756_);
lean_dec_ref(v_arg_740_);
lean_dec(v_x_713_);
goto v___jp_725_;
}
}
else
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
lean_dec(v_a_767_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec(v___y_756_);
lean_dec_ref(v_arg_740_);
lean_dec(v_x_713_);
v_a_794_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_768_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_768_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
else
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_809_; 
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec(v___y_756_);
lean_dec_ref(v_arg_740_);
lean_dec(v_x_713_);
v_a_802_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_809_ == 0)
{
v___x_804_ = v___x_766_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_766_);
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
}
}
}
}
}
}
v___jp_733_:
{
lean_object* v___x_734_; lean_object* v___x_736_; 
v___x_734_ = lean_box(0);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 0, v___x_734_);
v___x_736_ = v___x_731_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_734_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
else
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
lean_dec(v_a_723_);
lean_dec_ref(v_a_722_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec(v_a_717_);
lean_dec_ref(v_a_716_);
lean_dec(v_a_715_);
lean_dec(v_a_714_);
lean_dec(v_x_713_);
v_a_832_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___x_728_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_728_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
v___jp_725_:
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = lean_box(0);
v___x_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
return v___x_727_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt___boxed(lean_object* v_e_840_, lean_object* v_x_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt(v_e_840_, v_x_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg(lean_object* v_cls_857_, lean_object* v___y_858_){
_start:
{
lean_object* v_options_860_; uint8_t v_hasTrace_861_; 
v_options_860_ = lean_ctor_get(v___y_858_, 2);
v_hasTrace_861_ = lean_ctor_get_uint8(v_options_860_, sizeof(void*)*1);
if (v_hasTrace_861_ == 0)
{
lean_object* v___x_862_; lean_object* v___x_863_; 
lean_dec(v_cls_857_);
v___x_862_ = lean_box(v_hasTrace_861_);
v___x_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_863_, 0, v___x_862_);
return v___x_863_;
}
else
{
lean_object* v_inheritedTraceOptions_864_; lean_object* v___x_865_; lean_object* v___x_866_; uint8_t v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v_inheritedTraceOptions_864_ = lean_ctor_get(v___y_858_, 13);
v___x_865_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg___closed__1));
v___x_866_ = l_Lean_Name_append(v___x_865_, v_cls_857_);
v___x_867_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_864_, v_options_860_, v___x_866_);
lean_dec(v___x_866_);
v___x_868_ = lean_box(v___x_867_);
v___x_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
return v___x_869_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg___boxed(lean_object* v_cls_870_, lean_object* v___y_871_, lean_object* v___y_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg(v_cls_870_, v___y_871_);
lean_dec_ref(v___y_871_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1(lean_object* v_cls_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg(v_cls_874_, v___y_883_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___boxed(lean_object* v_cls_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1(v_cls_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec(v___y_889_);
lean_dec(v___y_888_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3_spec__5_spec__8___redArg(lean_object* v_x_900_, lean_object* v_x_901_, lean_object* v_x_902_, lean_object* v_x_903_){
_start:
{
lean_object* v_ks_904_; lean_object* v_vs_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_929_; 
v_ks_904_ = lean_ctor_get(v_x_900_, 0);
v_vs_905_ = lean_ctor_get(v_x_900_, 1);
v_isSharedCheck_929_ = !lean_is_exclusive(v_x_900_);
if (v_isSharedCheck_929_ == 0)
{
v___x_907_ = v_x_900_;
v_isShared_908_ = v_isSharedCheck_929_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_vs_905_);
lean_inc(v_ks_904_);
lean_dec(v_x_900_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_929_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_909_; uint8_t v___x_910_; 
v___x_909_ = lean_array_get_size(v_ks_904_);
v___x_910_ = lean_nat_dec_lt(v_x_901_, v___x_909_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_914_; 
lean_dec(v_x_901_);
v___x_911_ = lean_array_push(v_ks_904_, v_x_902_);
v___x_912_ = lean_array_push(v_vs_905_, v_x_903_);
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 1, v___x_912_);
lean_ctor_set(v___x_907_, 0, v___x_911_);
v___x_914_ = v___x_907_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_911_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v___x_912_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
else
{
lean_object* v_k_x27_916_; uint8_t v___x_917_; 
v_k_x27_916_ = lean_array_fget_borrowed(v_ks_904_, v_x_901_);
v___x_917_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_902_, v_k_x27_916_);
if (v___x_917_ == 0)
{
lean_object* v___x_919_; 
if (v_isShared_908_ == 0)
{
v___x_919_ = v___x_907_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_ks_904_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v_vs_905_);
v___x_919_ = v_reuseFailAlloc_923_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = lean_unsigned_to_nat(1u);
v___x_921_ = lean_nat_add(v_x_901_, v___x_920_);
lean_dec(v_x_901_);
v_x_900_ = v___x_919_;
v_x_901_ = v___x_921_;
goto _start;
}
}
else
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_927_; 
v___x_924_ = lean_array_fset(v_ks_904_, v_x_901_, v_x_902_);
v___x_925_ = lean_array_fset(v_vs_905_, v_x_901_, v_x_903_);
lean_dec(v_x_901_);
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 1, v___x_925_);
lean_ctor_set(v___x_907_, 0, v___x_924_);
v___x_927_ = v___x_907_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v___x_924_);
lean_ctor_set(v_reuseFailAlloc_928_, 1, v___x_925_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3_spec__5___redArg(lean_object* v_n_930_, lean_object* v_k_931_, lean_object* v_v_932_){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_933_ = lean_unsigned_to_nat(0u);
v___x_934_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3_spec__5_spec__8___redArg(v_n_930_, v___x_933_, v_k_931_, v_v_932_);
return v___x_934_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3___redArg(lean_object* v_x_936_, size_t v_x_937_, size_t v_x_938_, lean_object* v_x_939_, lean_object* v_x_940_){
_start:
{
if (lean_obj_tag(v_x_936_) == 0)
{
lean_object* v_es_941_; size_t v___x_942_; size_t v___x_943_; size_t v___x_944_; size_t v___x_945_; lean_object* v_j_946_; lean_object* v___x_947_; uint8_t v___x_948_; 
v_es_941_ = lean_ctor_get(v_x_936_, 0);
v___x_942_ = ((size_t)5ULL);
v___x_943_ = ((size_t)1ULL);
v___x_944_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1);
v___x_945_ = lean_usize_land(v_x_937_, v___x_944_);
v_j_946_ = lean_usize_to_nat(v___x_945_);
v___x_947_ = lean_array_get_size(v_es_941_);
v___x_948_ = lean_nat_dec_lt(v_j_946_, v___x_947_);
if (v___x_948_ == 0)
{
lean_dec(v_j_946_);
lean_dec(v_x_940_);
lean_dec_ref(v_x_939_);
return v_x_936_;
}
else
{
lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_985_; 
lean_inc_ref(v_es_941_);
v_isSharedCheck_985_ = !lean_is_exclusive(v_x_936_);
if (v_isSharedCheck_985_ == 0)
{
lean_object* v_unused_986_; 
v_unused_986_ = lean_ctor_get(v_x_936_, 0);
lean_dec(v_unused_986_);
v___x_950_ = v_x_936_;
v_isShared_951_ = v_isSharedCheck_985_;
goto v_resetjp_949_;
}
else
{
lean_dec(v_x_936_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_985_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v_v_952_; lean_object* v___x_953_; lean_object* v_xs_x27_954_; lean_object* v___y_956_; 
v_v_952_ = lean_array_fget(v_es_941_, v_j_946_);
v___x_953_ = lean_box(0);
v_xs_x27_954_ = lean_array_fset(v_es_941_, v_j_946_, v___x_953_);
switch(lean_obj_tag(v_v_952_))
{
case 0:
{
lean_object* v_key_961_; lean_object* v_val_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_972_; 
v_key_961_ = lean_ctor_get(v_v_952_, 0);
v_val_962_ = lean_ctor_get(v_v_952_, 1);
v_isSharedCheck_972_ = !lean_is_exclusive(v_v_952_);
if (v_isSharedCheck_972_ == 0)
{
v___x_964_ = v_v_952_;
v_isShared_965_ = v_isSharedCheck_972_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_val_962_);
lean_inc(v_key_961_);
lean_dec(v_v_952_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_972_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
uint8_t v___x_966_; 
v___x_966_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_939_, v_key_961_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; lean_object* v___x_968_; 
lean_del_object(v___x_964_);
v___x_967_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_961_, v_val_962_, v_x_939_, v_x_940_);
v___x_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
v___y_956_ = v___x_968_;
goto v___jp_955_;
}
else
{
lean_object* v___x_970_; 
lean_dec(v_val_962_);
lean_dec(v_key_961_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 1, v_x_940_);
lean_ctor_set(v___x_964_, 0, v_x_939_);
v___x_970_ = v___x_964_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_x_939_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v_x_940_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
v___y_956_ = v___x_970_;
goto v___jp_955_;
}
}
}
}
case 1:
{
lean_object* v_node_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_983_; 
v_node_973_ = lean_ctor_get(v_v_952_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v_v_952_);
if (v_isSharedCheck_983_ == 0)
{
v___x_975_ = v_v_952_;
v_isShared_976_ = v_isSharedCheck_983_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_node_973_);
lean_dec(v_v_952_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_983_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
size_t v___x_977_; size_t v___x_978_; lean_object* v___x_979_; lean_object* v___x_981_; 
v___x_977_ = lean_usize_shift_right(v_x_937_, v___x_942_);
v___x_978_ = lean_usize_add(v_x_938_, v___x_943_);
v___x_979_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3___redArg(v_node_973_, v___x_977_, v___x_978_, v_x_939_, v_x_940_);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v___x_979_);
v___x_981_ = v___x_975_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_979_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
v___y_956_ = v___x_981_;
goto v___jp_955_;
}
}
}
default: 
{
lean_object* v___x_984_; 
v___x_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_984_, 0, v_x_939_);
lean_ctor_set(v___x_984_, 1, v_x_940_);
v___y_956_ = v___x_984_;
goto v___jp_955_;
}
}
v___jp_955_:
{
lean_object* v___x_957_; lean_object* v___x_959_; 
v___x_957_ = lean_array_fset(v_xs_x27_954_, v_j_946_, v___y_956_);
lean_dec(v_j_946_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 0, v___x_957_);
v___x_959_ = v___x_950_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v___x_957_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
}
else
{
lean_object* v_ks_987_; lean_object* v_vs_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_1008_; 
v_ks_987_ = lean_ctor_get(v_x_936_, 0);
v_vs_988_ = lean_ctor_get(v_x_936_, 1);
v_isSharedCheck_1008_ = !lean_is_exclusive(v_x_936_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_990_ = v_x_936_;
v_isShared_991_ = v_isSharedCheck_1008_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_vs_988_);
lean_inc(v_ks_987_);
lean_dec(v_x_936_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_1008_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_ks_987_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v_vs_988_);
v___x_993_ = v_reuseFailAlloc_1007_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_object* v_newNode_994_; uint8_t v___y_996_; size_t v___x_1002_; uint8_t v___x_1003_; 
v_newNode_994_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3_spec__5___redArg(v___x_993_, v_x_939_, v_x_940_);
v___x_1002_ = ((size_t)7ULL);
v___x_1003_ = lean_usize_dec_le(v___x_1002_, v_x_938_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1004_; lean_object* v___x_1005_; uint8_t v___x_1006_; 
v___x_1004_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_994_);
v___x_1005_ = lean_unsigned_to_nat(4u);
v___x_1006_ = lean_nat_dec_lt(v___x_1004_, v___x_1005_);
lean_dec(v___x_1004_);
v___y_996_ = v___x_1006_;
goto v___jp_995_;
}
else
{
v___y_996_ = v___x_1003_;
goto v___jp_995_;
}
v___jp_995_:
{
if (v___y_996_ == 0)
{
lean_object* v_ks_997_; lean_object* v_vs_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v_ks_997_ = lean_ctor_get(v_newNode_994_, 0);
lean_inc_ref(v_ks_997_);
v_vs_998_ = lean_ctor_get(v_newNode_994_, 1);
lean_inc_ref(v_vs_998_);
lean_dec_ref(v_newNode_994_);
v___x_999_ = lean_unsigned_to_nat(0u);
v___x_1000_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3___redArg___closed__0);
v___x_1001_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3_spec__6___redArg(v_x_938_, v_ks_997_, v_vs_998_, v___x_999_, v___x_1000_);
lean_dec_ref(v_vs_998_);
lean_dec_ref(v_ks_997_);
return v___x_1001_;
}
else
{
return v_newNode_994_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3_spec__6___redArg(size_t v_depth_1009_, lean_object* v_keys_1010_, lean_object* v_vals_1011_, lean_object* v_i_1012_, lean_object* v_entries_1013_){
_start:
{
lean_object* v___x_1014_; uint8_t v___x_1015_; 
v___x_1014_ = lean_array_get_size(v_keys_1010_);
v___x_1015_ = lean_nat_dec_lt(v_i_1012_, v___x_1014_);
if (v___x_1015_ == 0)
{
lean_dec(v_i_1012_);
return v_entries_1013_;
}
else
{
lean_object* v_k_1016_; lean_object* v_v_1017_; uint64_t v___x_1018_; size_t v_h_1019_; size_t v___x_1020_; lean_object* v___x_1021_; size_t v___x_1022_; size_t v___x_1023_; size_t v___x_1024_; size_t v_h_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v_k_1016_ = lean_array_fget_borrowed(v_keys_1010_, v_i_1012_);
v_v_1017_ = lean_array_fget_borrowed(v_vals_1011_, v_i_1012_);
v___x_1018_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_1016_);
v_h_1019_ = lean_uint64_to_usize(v___x_1018_);
v___x_1020_ = ((size_t)5ULL);
v___x_1021_ = lean_unsigned_to_nat(1u);
v___x_1022_ = ((size_t)1ULL);
v___x_1023_ = lean_usize_sub(v_depth_1009_, v___x_1022_);
v___x_1024_ = lean_usize_mul(v___x_1020_, v___x_1023_);
v_h_1025_ = lean_usize_shift_right(v_h_1019_, v___x_1024_);
v___x_1026_ = lean_nat_add(v_i_1012_, v___x_1021_);
lean_dec(v_i_1012_);
lean_inc(v_v_1017_);
lean_inc(v_k_1016_);
v___x_1027_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3___redArg(v_entries_1013_, v_h_1025_, v_depth_1009_, v_k_1016_, v_v_1017_);
v_i_1012_ = v___x_1026_;
v_entries_1013_ = v___x_1027_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_depth_1029_, lean_object* v_keys_1030_, lean_object* v_vals_1031_, lean_object* v_i_1032_, lean_object* v_entries_1033_){
_start:
{
size_t v_depth_boxed_1034_; lean_object* v_res_1035_; 
v_depth_boxed_1034_ = lean_unbox_usize(v_depth_1029_);
lean_dec(v_depth_1029_);
v_res_1035_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3_spec__6___redArg(v_depth_boxed_1034_, v_keys_1030_, v_vals_1031_, v_i_1032_, v_entries_1033_);
lean_dec_ref(v_vals_1031_);
lean_dec_ref(v_keys_1030_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3___redArg___boxed(lean_object* v_x_1036_, lean_object* v_x_1037_, lean_object* v_x_1038_, lean_object* v_x_1039_, lean_object* v_x_1040_){
_start:
{
size_t v_x_31834__boxed_1041_; size_t v_x_31835__boxed_1042_; lean_object* v_res_1043_; 
v_x_31834__boxed_1041_ = lean_unbox_usize(v_x_1037_);
lean_dec(v_x_1037_);
v_x_31835__boxed_1042_ = lean_unbox_usize(v_x_1038_);
lean_dec(v_x_1038_);
v_res_1043_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3___redArg(v_x_1036_, v_x_31834__boxed_1041_, v_x_31835__boxed_1042_, v_x_1039_, v_x_1040_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(lean_object* v_x_1044_, lean_object* v_x_1045_, lean_object* v_x_1046_){
_start:
{
uint64_t v___x_1047_; size_t v___x_1048_; size_t v___x_1049_; lean_object* v___x_1050_; 
v___x_1047_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1045_);
v___x_1048_ = lean_uint64_to_usize(v___x_1047_);
v___x_1049_ = ((size_t)1ULL);
v___x_1050_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3___redArg(v_x_1044_, v___x_1048_, v___x_1049_, v_x_1045_, v_x_1046_);
return v___x_1050_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1051_ = lean_unsigned_to_nat(32u);
v___x_1052_ = lean_mk_empty_array_with_capacity(v___x_1051_);
v___x_1053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
return v___x_1053_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1(void){
_start:
{
size_t v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1054_ = ((size_t)5ULL);
v___x_1055_ = lean_unsigned_to_nat(0u);
v___x_1056_ = lean_unsigned_to_nat(32u);
v___x_1057_ = lean_mk_empty_array_with_capacity(v___x_1056_);
v___x_1058_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0);
v___x_1059_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
lean_ctor_set(v___x_1059_, 1, v___x_1057_);
lean_ctor_set(v___x_1059_, 2, v___x_1055_);
lean_ctor_set(v___x_1059_, 3, v___x_1055_);
lean_ctor_set_usize(v___x_1059_, 4, v___x_1054_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0(lean_object* v_expr_1060_, lean_object* v_size_1061_, lean_object* v_s_1062_){
_start:
{
lean_object* v_vars_1063_; lean_object* v_varMap_1064_; lean_object* v_vars_x27_1065_; lean_object* v_varMap_x27_1066_; lean_object* v_natToIntMap_1067_; lean_object* v_natDef_1068_; lean_object* v_dvds_1069_; lean_object* v_lowers_1070_; lean_object* v_uppers_1071_; lean_object* v_diseqs_1072_; lean_object* v_elimEqs_1073_; lean_object* v_elimStack_1074_; lean_object* v_occurs_1075_; lean_object* v_assignment_1076_; lean_object* v_nextCnstrId_1077_; uint8_t v_caseSplits_1078_; lean_object* v_conflict_x3f_1079_; lean_object* v_diseqSplits_1080_; lean_object* v_divMod_1081_; lean_object* v_toIntIds_1082_; lean_object* v_toIntInfos_1083_; lean_object* v_toIntTermMap_1084_; lean_object* v_toIntVarMap_1085_; uint8_t v_usedCommRing_1086_; lean_object* v_nonlinearOccs_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1105_; 
v_vars_1063_ = lean_ctor_get(v_s_1062_, 0);
v_varMap_1064_ = lean_ctor_get(v_s_1062_, 1);
v_vars_x27_1065_ = lean_ctor_get(v_s_1062_, 2);
v_varMap_x27_1066_ = lean_ctor_get(v_s_1062_, 3);
v_natToIntMap_1067_ = lean_ctor_get(v_s_1062_, 4);
v_natDef_1068_ = lean_ctor_get(v_s_1062_, 5);
v_dvds_1069_ = lean_ctor_get(v_s_1062_, 6);
v_lowers_1070_ = lean_ctor_get(v_s_1062_, 7);
v_uppers_1071_ = lean_ctor_get(v_s_1062_, 8);
v_diseqs_1072_ = lean_ctor_get(v_s_1062_, 9);
v_elimEqs_1073_ = lean_ctor_get(v_s_1062_, 10);
v_elimStack_1074_ = lean_ctor_get(v_s_1062_, 11);
v_occurs_1075_ = lean_ctor_get(v_s_1062_, 12);
v_assignment_1076_ = lean_ctor_get(v_s_1062_, 13);
v_nextCnstrId_1077_ = lean_ctor_get(v_s_1062_, 14);
v_caseSplits_1078_ = lean_ctor_get_uint8(v_s_1062_, sizeof(void*)*23);
v_conflict_x3f_1079_ = lean_ctor_get(v_s_1062_, 15);
v_diseqSplits_1080_ = lean_ctor_get(v_s_1062_, 16);
v_divMod_1081_ = lean_ctor_get(v_s_1062_, 17);
v_toIntIds_1082_ = lean_ctor_get(v_s_1062_, 18);
v_toIntInfos_1083_ = lean_ctor_get(v_s_1062_, 19);
v_toIntTermMap_1084_ = lean_ctor_get(v_s_1062_, 20);
v_toIntVarMap_1085_ = lean_ctor_get(v_s_1062_, 21);
v_usedCommRing_1086_ = lean_ctor_get_uint8(v_s_1062_, sizeof(void*)*23 + 1);
v_nonlinearOccs_1087_ = lean_ctor_get(v_s_1062_, 22);
v_isSharedCheck_1105_ = !lean_is_exclusive(v_s_1062_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1089_ = v_s_1062_;
v_isShared_1090_ = v_isSharedCheck_1105_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_nonlinearOccs_1087_);
lean_inc(v_toIntVarMap_1085_);
lean_inc(v_toIntTermMap_1084_);
lean_inc(v_toIntInfos_1083_);
lean_inc(v_toIntIds_1082_);
lean_inc(v_divMod_1081_);
lean_inc(v_diseqSplits_1080_);
lean_inc(v_conflict_x3f_1079_);
lean_inc(v_nextCnstrId_1077_);
lean_inc(v_assignment_1076_);
lean_inc(v_occurs_1075_);
lean_inc(v_elimStack_1074_);
lean_inc(v_elimEqs_1073_);
lean_inc(v_diseqs_1072_);
lean_inc(v_uppers_1071_);
lean_inc(v_lowers_1070_);
lean_inc(v_dvds_1069_);
lean_inc(v_natDef_1068_);
lean_inc(v_natToIntMap_1067_);
lean_inc(v_varMap_x27_1066_);
lean_inc(v_vars_x27_1065_);
lean_inc(v_varMap_1064_);
lean_inc(v_vars_1063_);
lean_dec(v_s_1062_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1105_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1103_; 
lean_inc_ref(v_expr_1060_);
v___x_1091_ = l_Lean_PersistentArray_push___redArg(v_vars_1063_, v_expr_1060_);
v___x_1092_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(v_varMap_1064_, v_expr_1060_, v_size_1061_);
v___x_1093_ = lean_box(0);
v___x_1094_ = l_Lean_PersistentArray_push___redArg(v_dvds_1069_, v___x_1093_);
v___x_1095_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1);
v___x_1096_ = l_Lean_PersistentArray_push___redArg(v_lowers_1070_, v___x_1095_);
v___x_1097_ = l_Lean_PersistentArray_push___redArg(v_uppers_1071_, v___x_1095_);
v___x_1098_ = l_Lean_PersistentArray_push___redArg(v_diseqs_1072_, v___x_1095_);
v___x_1099_ = l_Lean_PersistentArray_push___redArg(v_elimEqs_1073_, v___x_1093_);
v___x_1100_ = lean_box(1);
v___x_1101_ = l_Lean_PersistentArray_push___redArg(v_occurs_1075_, v___x_1100_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 12, v___x_1101_);
lean_ctor_set(v___x_1089_, 10, v___x_1099_);
lean_ctor_set(v___x_1089_, 9, v___x_1098_);
lean_ctor_set(v___x_1089_, 8, v___x_1097_);
lean_ctor_set(v___x_1089_, 7, v___x_1096_);
lean_ctor_set(v___x_1089_, 6, v___x_1094_);
lean_ctor_set(v___x_1089_, 1, v___x_1092_);
lean_ctor_set(v___x_1089_, 0, v___x_1091_);
v___x_1103_ = v___x_1089_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1091_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v___x_1092_);
lean_ctor_set(v_reuseFailAlloc_1104_, 2, v_vars_x27_1065_);
lean_ctor_set(v_reuseFailAlloc_1104_, 3, v_varMap_x27_1066_);
lean_ctor_set(v_reuseFailAlloc_1104_, 4, v_natToIntMap_1067_);
lean_ctor_set(v_reuseFailAlloc_1104_, 5, v_natDef_1068_);
lean_ctor_set(v_reuseFailAlloc_1104_, 6, v___x_1094_);
lean_ctor_set(v_reuseFailAlloc_1104_, 7, v___x_1096_);
lean_ctor_set(v_reuseFailAlloc_1104_, 8, v___x_1097_);
lean_ctor_set(v_reuseFailAlloc_1104_, 9, v___x_1098_);
lean_ctor_set(v_reuseFailAlloc_1104_, 10, v___x_1099_);
lean_ctor_set(v_reuseFailAlloc_1104_, 11, v_elimStack_1074_);
lean_ctor_set(v_reuseFailAlloc_1104_, 12, v___x_1101_);
lean_ctor_set(v_reuseFailAlloc_1104_, 13, v_assignment_1076_);
lean_ctor_set(v_reuseFailAlloc_1104_, 14, v_nextCnstrId_1077_);
lean_ctor_set(v_reuseFailAlloc_1104_, 15, v_conflict_x3f_1079_);
lean_ctor_set(v_reuseFailAlloc_1104_, 16, v_diseqSplits_1080_);
lean_ctor_set(v_reuseFailAlloc_1104_, 17, v_divMod_1081_);
lean_ctor_set(v_reuseFailAlloc_1104_, 18, v_toIntIds_1082_);
lean_ctor_set(v_reuseFailAlloc_1104_, 19, v_toIntInfos_1083_);
lean_ctor_set(v_reuseFailAlloc_1104_, 20, v_toIntTermMap_1084_);
lean_ctor_set(v_reuseFailAlloc_1104_, 21, v_toIntVarMap_1085_);
lean_ctor_set(v_reuseFailAlloc_1104_, 22, v_nonlinearOccs_1087_);
lean_ctor_set_uint8(v_reuseFailAlloc_1104_, sizeof(void*)*23, v_caseSplits_1078_);
lean_ctor_set_uint8(v_reuseFailAlloc_1104_, sizeof(void*)*23 + 1, v_usedCommRing_1086_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__2___redArg(lean_object* v_keys_1106_, lean_object* v_vals_1107_, lean_object* v_i_1108_, lean_object* v_k_1109_){
_start:
{
lean_object* v___x_1110_; uint8_t v___x_1111_; 
v___x_1110_ = lean_array_get_size(v_keys_1106_);
v___x_1111_ = lean_nat_dec_lt(v_i_1108_, v___x_1110_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; 
lean_dec(v_i_1108_);
v___x_1112_ = lean_box(0);
return v___x_1112_;
}
else
{
lean_object* v_k_x27_1113_; uint8_t v___x_1114_; 
v_k_x27_1113_ = lean_array_fget_borrowed(v_keys_1106_, v_i_1108_);
v___x_1114_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_1109_, v_k_x27_1113_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = lean_unsigned_to_nat(1u);
v___x_1116_ = lean_nat_add(v_i_1108_, v___x_1115_);
lean_dec(v_i_1108_);
v_i_1108_ = v___x_1116_;
goto _start;
}
else
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1118_ = lean_array_fget_borrowed(v_vals_1107_, v_i_1108_);
lean_dec(v_i_1108_);
lean_inc(v___x_1118_);
v___x_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
return v___x_1119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_keys_1120_, lean_object* v_vals_1121_, lean_object* v_i_1122_, lean_object* v_k_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__2___redArg(v_keys_1120_, v_vals_1121_, v_i_1122_, v_k_1123_);
lean_dec_ref(v_k_1123_);
lean_dec_ref(v_vals_1121_);
lean_dec_ref(v_keys_1120_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(lean_object* v_x_1125_, size_t v_x_1126_, lean_object* v_x_1127_){
_start:
{
if (lean_obj_tag(v_x_1125_) == 0)
{
lean_object* v_es_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1149_; 
v_es_1128_ = lean_ctor_get(v_x_1125_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v_x_1125_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1130_ = v_x_1125_;
v_isShared_1131_ = v_isSharedCheck_1149_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_es_1128_);
lean_dec(v_x_1125_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1149_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1132_; size_t v___x_1133_; size_t v___x_1134_; size_t v___x_1135_; lean_object* v_j_1136_; lean_object* v___x_1137_; 
v___x_1132_ = lean_box(2);
v___x_1133_ = ((size_t)5ULL);
v___x_1134_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1);
v___x_1135_ = lean_usize_land(v_x_1126_, v___x_1134_);
v_j_1136_ = lean_usize_to_nat(v___x_1135_);
v___x_1137_ = lean_array_get(v___x_1132_, v_es_1128_, v_j_1136_);
lean_dec(v_j_1136_);
lean_dec_ref(v_es_1128_);
switch(lean_obj_tag(v___x_1137_))
{
case 0:
{
lean_object* v_key_1138_; lean_object* v_val_1139_; uint8_t v___x_1140_; 
v_key_1138_ = lean_ctor_get(v___x_1137_, 0);
lean_inc(v_key_1138_);
v_val_1139_ = lean_ctor_get(v___x_1137_, 1);
lean_inc(v_val_1139_);
lean_dec_ref(v___x_1137_);
v___x_1140_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1127_, v_key_1138_);
lean_dec(v_key_1138_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; 
lean_dec(v_val_1139_);
lean_del_object(v___x_1130_);
v___x_1141_ = lean_box(0);
return v___x_1141_;
}
else
{
lean_object* v___x_1143_; 
if (v_isShared_1131_ == 0)
{
lean_ctor_set_tag(v___x_1130_, 1);
lean_ctor_set(v___x_1130_, 0, v_val_1139_);
v___x_1143_ = v___x_1130_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_val_1139_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
case 1:
{
lean_object* v_node_1145_; size_t v___x_1146_; 
lean_del_object(v___x_1130_);
v_node_1145_ = lean_ctor_get(v___x_1137_, 0);
lean_inc(v_node_1145_);
lean_dec_ref(v___x_1137_);
v___x_1146_ = lean_usize_shift_right(v_x_1126_, v___x_1133_);
v_x_1125_ = v_node_1145_;
v_x_1126_ = v___x_1146_;
goto _start;
}
default: 
{
lean_object* v___x_1148_; 
lean_del_object(v___x_1130_);
v___x_1148_ = lean_box(0);
return v___x_1148_;
}
}
}
}
else
{
lean_object* v_ks_1150_; lean_object* v_vs_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v_ks_1150_ = lean_ctor_get(v_x_1125_, 0);
lean_inc_ref(v_ks_1150_);
v_vs_1151_ = lean_ctor_get(v_x_1125_, 1);
lean_inc_ref(v_vs_1151_);
lean_dec_ref(v_x_1125_);
v___x_1152_ = lean_unsigned_to_nat(0u);
v___x_1153_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__2___redArg(v_ks_1150_, v_vs_1151_, v___x_1152_, v_x_1127_);
lean_dec_ref(v_vs_1151_);
lean_dec_ref(v_ks_1150_);
return v___x_1153_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg___boxed(lean_object* v_x_1154_, lean_object* v_x_1155_, lean_object* v_x_1156_){
_start:
{
size_t v_x_32093__boxed_1157_; lean_object* v_res_1158_; 
v_x_32093__boxed_1157_ = lean_unbox_usize(v_x_1155_);
lean_dec(v_x_1155_);
v_res_1158_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(v_x_1154_, v_x_32093__boxed_1157_, v_x_1156_);
lean_dec_ref(v_x_1156_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(lean_object* v_x_1159_, lean_object* v_x_1160_){
_start:
{
uint64_t v___x_1161_; size_t v___x_1162_; lean_object* v___x_1163_; 
v___x_1161_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1160_);
v___x_1162_ = lean_uint64_to_usize(v___x_1161_);
v___x_1163_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(v_x_1159_, v___x_1162_, v_x_1160_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg___boxed(lean_object* v_x_1164_, lean_object* v_x_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(v_x_1164_, v_x_1165_);
lean_dec_ref(v_x_1165_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__3_spec__5(lean_object* v_msgData_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v___x_1173_; lean_object* v_env_1174_; lean_object* v___x_1175_; lean_object* v_mctx_1176_; lean_object* v_lctx_1177_; lean_object* v_options_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1173_ = lean_st_ref_get(v___y_1171_);
v_env_1174_ = lean_ctor_get(v___x_1173_, 0);
lean_inc_ref(v_env_1174_);
lean_dec(v___x_1173_);
v___x_1175_ = lean_st_ref_get(v___y_1169_);
v_mctx_1176_ = lean_ctor_get(v___x_1175_, 0);
lean_inc_ref(v_mctx_1176_);
lean_dec(v___x_1175_);
v_lctx_1177_ = lean_ctor_get(v___y_1168_, 2);
v_options_1178_ = lean_ctor_get(v___y_1170_, 2);
lean_inc_ref(v_options_1178_);
lean_inc_ref(v_lctx_1177_);
v___x_1179_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1179_, 0, v_env_1174_);
lean_ctor_set(v___x_1179_, 1, v_mctx_1176_);
lean_ctor_set(v___x_1179_, 2, v_lctx_1177_);
lean_ctor_set(v___x_1179_, 3, v_options_1178_);
v___x_1180_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
lean_ctor_set(v___x_1180_, 1, v_msgData_1167_);
v___x_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__3_spec__5___boxed(lean_object* v_msgData_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__3_spec__5(v_msgData_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
return v_res_1188_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1189_; double v___x_1190_; 
v___x_1189_ = lean_unsigned_to_nat(0u);
v___x_1190_ = lean_float_of_nat(v___x_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__3___redArg(lean_object* v_cls_1194_, lean_object* v_msg_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v_ref_1201_; lean_object* v___x_1202_; lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1247_; 
v_ref_1201_ = lean_ctor_get(v___y_1198_, 5);
v___x_1202_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__3_spec__5(v_msg_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1205_ = v___x_1202_;
v_isShared_1206_ = v_isSharedCheck_1247_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1202_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1247_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1207_; lean_object* v_traceState_1208_; lean_object* v_env_1209_; lean_object* v_nextMacroScope_1210_; lean_object* v_ngen_1211_; lean_object* v_auxDeclNGen_1212_; lean_object* v_cache_1213_; lean_object* v_messages_1214_; lean_object* v_infoState_1215_; lean_object* v_snapshotTasks_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1246_; 
v___x_1207_ = lean_st_ref_take(v___y_1199_);
v_traceState_1208_ = lean_ctor_get(v___x_1207_, 4);
v_env_1209_ = lean_ctor_get(v___x_1207_, 0);
v_nextMacroScope_1210_ = lean_ctor_get(v___x_1207_, 1);
v_ngen_1211_ = lean_ctor_get(v___x_1207_, 2);
v_auxDeclNGen_1212_ = lean_ctor_get(v___x_1207_, 3);
v_cache_1213_ = lean_ctor_get(v___x_1207_, 5);
v_messages_1214_ = lean_ctor_get(v___x_1207_, 6);
v_infoState_1215_ = lean_ctor_get(v___x_1207_, 7);
v_snapshotTasks_1216_ = lean_ctor_get(v___x_1207_, 8);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1207_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1218_ = v___x_1207_;
v_isShared_1219_ = v_isSharedCheck_1246_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_snapshotTasks_1216_);
lean_inc(v_infoState_1215_);
lean_inc(v_messages_1214_);
lean_inc(v_cache_1213_);
lean_inc(v_traceState_1208_);
lean_inc(v_auxDeclNGen_1212_);
lean_inc(v_ngen_1211_);
lean_inc(v_nextMacroScope_1210_);
lean_inc(v_env_1209_);
lean_dec(v___x_1207_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1246_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
uint64_t v_tid_1220_; lean_object* v_traces_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1245_; 
v_tid_1220_ = lean_ctor_get_uint64(v_traceState_1208_, sizeof(void*)*1);
v_traces_1221_ = lean_ctor_get(v_traceState_1208_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v_traceState_1208_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1223_ = v_traceState_1208_;
v_isShared_1224_ = v_isSharedCheck_1245_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_traces_1221_);
lean_dec(v_traceState_1208_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1245_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1225_; double v___x_1226_; uint8_t v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1235_; 
v___x_1225_ = lean_box(0);
v___x_1226_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__3___redArg___closed__0);
v___x_1227_ = 0;
v___x_1228_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__3___redArg___closed__1));
v___x_1229_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1229_, 0, v_cls_1194_);
lean_ctor_set(v___x_1229_, 1, v___x_1225_);
lean_ctor_set(v___x_1229_, 2, v___x_1228_);
lean_ctor_set_float(v___x_1229_, sizeof(void*)*3, v___x_1226_);
lean_ctor_set_float(v___x_1229_, sizeof(void*)*3 + 8, v___x_1226_);
lean_ctor_set_uint8(v___x_1229_, sizeof(void*)*3 + 16, v___x_1227_);
v___x_1230_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__3___redArg___closed__2));
v___x_1231_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1229_);
lean_ctor_set(v___x_1231_, 1, v_a_1203_);
lean_ctor_set(v___x_1231_, 2, v___x_1230_);
lean_inc(v_ref_1201_);
v___x_1232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1232_, 0, v_ref_1201_);
lean_ctor_set(v___x_1232_, 1, v___x_1231_);
v___x_1233_ = l_Lean_PersistentArray_push___redArg(v_traces_1221_, v___x_1232_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 0, v___x_1233_);
v___x_1235_ = v___x_1223_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1233_);
lean_ctor_set_uint64(v_reuseFailAlloc_1244_, sizeof(void*)*1, v_tid_1220_);
v___x_1235_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
lean_object* v___x_1237_; 
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 4, v___x_1235_);
v___x_1237_ = v___x_1218_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_env_1209_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v_nextMacroScope_1210_);
lean_ctor_set(v_reuseFailAlloc_1243_, 2, v_ngen_1211_);
lean_ctor_set(v_reuseFailAlloc_1243_, 3, v_auxDeclNGen_1212_);
lean_ctor_set(v_reuseFailAlloc_1243_, 4, v___x_1235_);
lean_ctor_set(v_reuseFailAlloc_1243_, 5, v_cache_1213_);
lean_ctor_set(v_reuseFailAlloc_1243_, 6, v_messages_1214_);
lean_ctor_set(v_reuseFailAlloc_1243_, 7, v_infoState_1215_);
lean_ctor_set(v_reuseFailAlloc_1243_, 8, v_snapshotTasks_1216_);
v___x_1237_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1241_; 
v___x_1238_ = lean_st_ref_set(v___y_1199_, v___x_1237_);
v___x_1239_ = lean_box(0);
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 0, v___x_1239_);
v___x_1241_ = v___x_1205_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___x_1239_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__3___redArg___boxed(lean_object* v_cls_1248_, lean_object* v_msg_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__3___redArg(v_cls_1248_, v_msg_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
return v_res_1255_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__6(void){
_start:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__5));
v___x_1267_ = l_Lean_stringToMessageData(v___x_1266_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* lean_grind_cutsat_mk_var(lean_object* v_expr_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_){
_start:
{
lean_object* v___x_1280_; 
v___x_1280_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1269_, v_a_1277_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1422_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1283_ = v___x_1280_;
v_isShared_1284_ = v_isSharedCheck_1422_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1280_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1422_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v_varMap_1285_; lean_object* v___x_1286_; 
v_varMap_1285_ = lean_ctor_get(v_a_1281_, 1);
lean_inc_ref(v_varMap_1285_);
lean_dec(v_a_1281_);
v___x_1286_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(v_varMap_1285_, v_expr_1268_);
if (lean_obj_tag(v___x_1286_) == 1)
{
lean_object* v_val_1287_; lean_object* v___x_1289_; 
lean_dec(v_a_1278_);
lean_dec_ref(v_a_1277_);
lean_dec(v_a_1276_);
lean_dec_ref(v_a_1275_);
lean_dec(v_a_1274_);
lean_dec_ref(v_a_1273_);
lean_dec(v_a_1272_);
lean_dec_ref(v_a_1271_);
lean_dec(v_a_1270_);
lean_dec(v_a_1269_);
lean_dec_ref(v_expr_1268_);
v_val_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_val_1287_);
lean_dec_ref(v___x_1286_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 0, v_val_1287_);
v___x_1289_ = v___x_1283_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_val_1287_);
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
lean_dec(v___x_1286_);
lean_del_object(v___x_1283_);
v___x_1291_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1269_, v_a_1277_);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_object* v_a_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v_vars_1295_; lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1413_; 
v_a_1292_ = lean_ctor_get(v___x_1291_, 0);
lean_inc(v_a_1292_);
lean_dec_ref(v___x_1291_);
v___x_1293_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4));
v___x_1294_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg(v___x_1293_, v_a_1277_);
v_vars_1295_ = lean_ctor_get(v_a_1292_, 0);
lean_inc_ref(v_vars_1295_);
lean_dec(v_a_1292_);
v_a_1296_ = lean_ctor_get(v___x_1294_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1298_ = v___x_1294_;
v_isShared_1299_ = v_isSharedCheck_1413_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1294_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1413_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v_size_1300_; lean_object* v___f_1301_; lean_object* v___y_1303_; lean_object* v___y_1304_; lean_object* v___y_1305_; lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v___y_1308_; lean_object* v___y_1309_; lean_object* v___y_1310_; lean_object* v___y_1311_; lean_object* v___y_1312_; uint8_t v___x_1394_; 
v_size_1300_ = lean_ctor_get(v_vars_1295_, 2);
lean_inc(v_size_1300_);
lean_dec_ref(v_vars_1295_);
lean_inc(v_size_1300_);
lean_inc_ref(v_expr_1268_);
v___f_1301_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0), 3, 2);
lean_closure_set(v___f_1301_, 0, v_expr_1268_);
lean_closure_set(v___f_1301_, 1, v_size_1300_);
v___x_1394_ = lean_unbox(v_a_1296_);
lean_dec(v_a_1296_);
if (v___x_1394_ == 0)
{
lean_del_object(v___x_1298_);
v___y_1303_ = v_a_1269_;
v___y_1304_ = v_a_1270_;
v___y_1305_ = v_a_1271_;
v___y_1306_ = v_a_1272_;
v___y_1307_ = v_a_1273_;
v___y_1308_ = v_a_1274_;
v___y_1309_ = v_a_1275_;
v___y_1310_ = v_a_1276_;
v___y_1311_ = v_a_1277_;
v___y_1312_ = v_a_1278_;
goto v___jp_1302_;
}
else
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1400_; 
lean_inc_ref(v_expr_1268_);
v___x_1395_ = l_Lean_MessageData_ofExpr(v_expr_1268_);
v___x_1396_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__6);
v___x_1397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1395_);
lean_ctor_set(v___x_1397_, 1, v___x_1396_);
lean_inc(v_size_1300_);
v___x_1398_ = l_Nat_reprFast(v_size_1300_);
if (v_isShared_1299_ == 0)
{
lean_ctor_set_tag(v___x_1298_, 3);
lean_ctor_set(v___x_1298_, 0, v___x_1398_);
v___x_1400_ = v___x_1298_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v___x_1398_);
v___x_1400_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1401_ = l_Lean_MessageData_ofFormat(v___x_1400_);
v___x_1402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1397_);
lean_ctor_set(v___x_1402_, 1, v___x_1401_);
v___x_1403_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__3___redArg(v___x_1293_, v___x_1402_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_dec_ref(v___x_1403_);
v___y_1303_ = v_a_1269_;
v___y_1304_ = v_a_1270_;
v___y_1305_ = v_a_1271_;
v___y_1306_ = v_a_1272_;
v___y_1307_ = v_a_1273_;
v___y_1308_ = v_a_1274_;
v___y_1309_ = v_a_1275_;
v___y_1310_ = v_a_1276_;
v___y_1311_ = v_a_1277_;
v___y_1312_ = v_a_1278_;
goto v___jp_1302_;
}
else
{
lean_object* v_a_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1411_; 
lean_dec_ref(v___f_1301_);
lean_dec(v_size_1300_);
lean_dec(v_a_1278_);
lean_dec_ref(v_a_1277_);
lean_dec(v_a_1276_);
lean_dec_ref(v_a_1275_);
lean_dec(v_a_1274_);
lean_dec_ref(v_a_1273_);
lean_dec(v_a_1272_);
lean_dec_ref(v_a_1271_);
lean_dec(v_a_1270_);
lean_dec(v_a_1269_);
lean_dec_ref(v_expr_1268_);
v_a_1404_ = lean_ctor_get(v___x_1403_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1406_ = v___x_1403_;
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_a_1404_);
lean_dec(v___x_1403_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1409_; 
if (v_isShared_1407_ == 0)
{
v___x_1409_ = v___x_1406_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_a_1404_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
}
v___jp_1302_:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1313_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_1314_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1313_, v___f_1301_, v___y_1303_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v___x_1315_; 
lean_dec_ref(v___x_1314_);
lean_inc(v___y_1312_);
lean_inc_ref(v___y_1311_);
lean_inc(v___y_1310_);
lean_inc_ref(v___y_1309_);
lean_inc(v___y_1308_);
lean_inc_ref(v___y_1307_);
lean_inc(v___y_1306_);
lean_inc_ref(v___y_1305_);
lean_inc(v___y_1304_);
lean_inc(v___y_1303_);
lean_inc_ref(v_expr_1268_);
v___x_1315_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_1313_, v_expr_1268_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v___x_1316_; 
lean_dec_ref(v___x_1315_);
lean_inc(v___y_1312_);
lean_inc_ref(v___y_1311_);
lean_inc(v___y_1310_);
lean_inc_ref(v___y_1309_);
lean_inc(v___y_1308_);
lean_inc_ref(v___y_1307_);
lean_inc(v___y_1306_);
lean_inc_ref(v___y_1305_);
lean_inc(v___y_1304_);
lean_inc(v___y_1303_);
lean_inc(v_size_1300_);
lean_inc_ref(v_expr_1268_);
v___x_1316_ = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(v_expr_1268_, v_size_1300_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v___x_1317_; 
lean_dec_ref(v___x_1316_);
lean_inc(v___y_1312_);
lean_inc_ref(v___y_1311_);
lean_inc(v___y_1310_);
lean_inc_ref(v___y_1309_);
lean_inc(v___y_1308_);
lean_inc_ref(v___y_1307_);
lean_inc(v___y_1306_);
lean_inc_ref(v___y_1305_);
lean_inc(v___y_1304_);
lean_inc(v___y_1303_);
lean_inc(v_size_1300_);
lean_inc_ref(v_expr_1268_);
v___x_1317_ = l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg(v_expr_1268_, v_size_1300_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v___x_1318_; 
lean_dec_ref(v___x_1317_);
lean_inc(v___y_1312_);
lean_inc_ref(v___y_1311_);
lean_inc(v___y_1310_);
lean_inc_ref(v___y_1309_);
lean_inc(v___y_1308_);
lean_inc_ref(v___y_1307_);
lean_inc(v___y_1306_);
lean_inc_ref(v___y_1305_);
lean_inc(v___y_1304_);
lean_inc(v___y_1303_);
lean_inc(v_size_1300_);
lean_inc_ref(v_expr_1268_);
v___x_1318_ = l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds(v_expr_1268_, v_size_1300_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v___x_1319_; 
lean_dec_ref(v___x_1318_);
lean_inc(v___y_1312_);
lean_inc_ref(v___y_1311_);
lean_inc(v___y_1310_);
lean_inc_ref(v___y_1309_);
lean_inc_ref(v_expr_1268_);
v___x_1319_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm(v_expr_1268_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1345_; 
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1322_ = v___x_1319_;
v_isShared_1323_ = v_isSharedCheck_1345_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1319_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1345_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
uint8_t v___x_1324_; 
v___x_1324_ = lean_unbox(v_a_1320_);
lean_dec(v_a_1320_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1326_; 
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec_ref(v_expr_1268_);
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 0, v_size_1300_);
v___x_1326_ = v___x_1322_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_size_1300_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
else
{
lean_object* v___x_1328_; 
lean_del_object(v___x_1322_);
lean_inc(v_size_1300_);
v___x_1328_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt(v_expr_1268_, v_size_1300_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1335_ == 0)
{
lean_object* v_unused_1336_; 
v_unused_1336_ = lean_ctor_get(v___x_1328_, 0);
lean_dec(v_unused_1336_);
v___x_1330_ = v___x_1328_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_dec(v___x_1328_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 0, v_size_1300_);
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_size_1300_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
else
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1344_; 
lean_dec(v_size_1300_);
v_a_1337_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1339_ = v___x_1328_;
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1328_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1342_; 
if (v_isShared_1340_ == 0)
{
v___x_1342_ = v___x_1339_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_a_1337_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
}
}
else
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1353_; 
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec(v_size_1300_);
lean_dec_ref(v_expr_1268_);
v_a_1346_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1348_ = v___x_1319_;
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1319_);
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
else
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec(v_size_1300_);
lean_dec_ref(v_expr_1268_);
v_a_1354_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1356_ = v___x_1318_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1318_);
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
else
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec(v_size_1300_);
lean_dec_ref(v_expr_1268_);
v_a_1362_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1317_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1317_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec(v_size_1300_);
lean_dec_ref(v_expr_1268_);
v_a_1370_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1316_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1316_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
else
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1385_; 
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec(v_size_1300_);
lean_dec_ref(v_expr_1268_);
v_a_1378_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1380_ = v___x_1315_;
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1315_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1383_; 
if (v_isShared_1381_ == 0)
{
v___x_1383_ = v___x_1380_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_a_1378_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
else
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1393_; 
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec(v_size_1300_);
lean_dec_ref(v_expr_1268_);
v_a_1386_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1388_ = v___x_1314_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1314_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1391_; 
if (v_isShared_1389_ == 0)
{
v___x_1391_ = v___x_1388_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_a_1386_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
}
}
}
else
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
lean_dec(v_a_1278_);
lean_dec_ref(v_a_1277_);
lean_dec(v_a_1276_);
lean_dec_ref(v_a_1275_);
lean_dec(v_a_1274_);
lean_dec_ref(v_a_1273_);
lean_dec(v_a_1272_);
lean_dec_ref(v_a_1271_);
lean_dec(v_a_1270_);
lean_dec(v_a_1269_);
lean_dec_ref(v_expr_1268_);
v_a_1414_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1291_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1291_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1414_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
}
}
else
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1430_; 
lean_dec(v_a_1278_);
lean_dec_ref(v_a_1277_);
lean_dec(v_a_1276_);
lean_dec_ref(v_a_1275_);
lean_dec(v_a_1274_);
lean_dec_ref(v_a_1273_);
lean_dec(v_a_1272_);
lean_dec_ref(v_a_1271_);
lean_dec(v_a_1270_);
lean_dec(v_a_1269_);
lean_dec_ref(v_expr_1268_);
v_a_1423_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1425_ = v___x_1280_;
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1280_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1428_; 
if (v_isShared_1426_ == 0)
{
v___x_1428_ = v___x_1425_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_a_1423_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___boxed(lean_object* v_expr_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = lean_grind_cutsat_mk_var(v_expr_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0(lean_object* v_00_u03b2_1444_, lean_object* v_x_1445_, lean_object* v_x_1446_){
_start:
{
lean_object* v___x_1447_; 
v___x_1447_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(v_x_1445_, v_x_1446_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___boxed(lean_object* v_00_u03b2_1448_, lean_object* v_x_1449_, lean_object* v_x_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0(v_00_u03b2_1448_, v_x_1449_, v_x_1450_);
lean_dec_ref(v_x_1450_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2(lean_object* v_00_u03b2_1452_, lean_object* v_x_1453_, lean_object* v_x_1454_, lean_object* v_x_1455_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(v_x_1453_, v_x_1454_, v_x_1455_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__3(lean_object* v_cls_1457_, lean_object* v_msg_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
lean_object* v___x_1470_; 
v___x_1470_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__3___redArg(v_cls_1457_, v_msg_1458_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__3___boxed(lean_object* v_cls_1471_, lean_object* v_msg_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__3(v_cls_1471_, v_msg_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1474_);
lean_dec(v___y_1473_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0(lean_object* v_00_u03b2_1485_, lean_object* v_x_1486_, size_t v_x_1487_, lean_object* v_x_1488_){
_start:
{
lean_object* v___x_1489_; 
v___x_1489_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(v_x_1486_, v_x_1487_, v_x_1488_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1490_, lean_object* v_x_1491_, lean_object* v_x_1492_, lean_object* v_x_1493_){
_start:
{
size_t v_x_32716__boxed_1494_; lean_object* v_res_1495_; 
v_x_32716__boxed_1494_ = lean_unbox_usize(v_x_1492_);
lean_dec(v_x_1492_);
v_res_1495_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0(v_00_u03b2_1490_, v_x_1491_, v_x_32716__boxed_1494_, v_x_1493_);
lean_dec_ref(v_x_1493_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3(lean_object* v_00_u03b2_1496_, lean_object* v_x_1497_, size_t v_x_1498_, size_t v_x_1499_, lean_object* v_x_1500_, lean_object* v_x_1501_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3___redArg(v_x_1497_, v_x_1498_, v_x_1499_, v_x_1500_, v_x_1501_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3___boxed(lean_object* v_00_u03b2_1503_, lean_object* v_x_1504_, lean_object* v_x_1505_, lean_object* v_x_1506_, lean_object* v_x_1507_, lean_object* v_x_1508_){
_start:
{
size_t v_x_32727__boxed_1509_; size_t v_x_32728__boxed_1510_; lean_object* v_res_1511_; 
v_x_32727__boxed_1509_ = lean_unbox_usize(v_x_1505_);
lean_dec(v_x_1505_);
v_x_32728__boxed_1510_ = lean_unbox_usize(v_x_1506_);
lean_dec(v_x_1506_);
v_res_1511_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3(v_00_u03b2_1503_, v_x_1504_, v_x_32727__boxed_1509_, v_x_32728__boxed_1510_, v_x_1507_, v_x_1508_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1512_, lean_object* v_keys_1513_, lean_object* v_vals_1514_, lean_object* v_heq_1515_, lean_object* v_i_1516_, lean_object* v_k_1517_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__2___redArg(v_keys_1513_, v_vals_1514_, v_i_1516_, v_k_1517_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1519_, lean_object* v_keys_1520_, lean_object* v_vals_1521_, lean_object* v_heq_1522_, lean_object* v_i_1523_, lean_object* v_k_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__2(v_00_u03b2_1519_, v_keys_1520_, v_vals_1521_, v_heq_1522_, v_i_1523_, v_k_1524_);
lean_dec_ref(v_k_1524_);
lean_dec_ref(v_vals_1521_);
lean_dec_ref(v_keys_1520_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3_spec__5(lean_object* v_00_u03b2_1526_, lean_object* v_n_1527_, lean_object* v_k_1528_, lean_object* v_v_1529_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3_spec__5___redArg(v_n_1527_, v_k_1528_, v_v_1529_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3_spec__6(lean_object* v_00_u03b2_1531_, size_t v_depth_1532_, lean_object* v_keys_1533_, lean_object* v_vals_1534_, lean_object* v_heq_1535_, lean_object* v_i_1536_, lean_object* v_entries_1537_){
_start:
{
lean_object* v___x_1538_; 
v___x_1538_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3_spec__6___redArg(v_depth_1532_, v_keys_1533_, v_vals_1534_, v_i_1536_, v_entries_1537_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03b2_1539_, lean_object* v_depth_1540_, lean_object* v_keys_1541_, lean_object* v_vals_1542_, lean_object* v_heq_1543_, lean_object* v_i_1544_, lean_object* v_entries_1545_){
_start:
{
size_t v_depth_boxed_1546_; lean_object* v_res_1547_; 
v_depth_boxed_1546_ = lean_unbox_usize(v_depth_1540_);
lean_dec(v_depth_1540_);
v_res_1547_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3_spec__6(v_00_u03b2_1539_, v_depth_boxed_1546_, v_keys_1541_, v_vals_1542_, v_heq_1543_, v_i_1544_, v_entries_1545_);
lean_dec_ref(v_vals_1542_);
lean_dec_ref(v_keys_1541_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3_spec__5_spec__8(lean_object* v_00_u03b2_1548_, lean_object* v_x_1549_, lean_object* v_x_1550_, lean_object* v_x_1551_, lean_object* v_x_1552_){
_start:
{
lean_object* v___x_1553_; 
v___x_1553_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__3_spec__5_spec__8___redArg(v_x_1549_, v_x_1550_, v_x_1551_, v_x_1552_);
return v___x_1553_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2(void){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1557_ = lean_box(0);
v___x_1558_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__1));
v___x_1559_ = l_Lean_mkConst(v___x_1558_, v___x_1557_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(lean_object* v_e_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_){
_start:
{
lean_object* v___x_1566_; 
lean_inc(v_a_1564_);
lean_inc_ref(v_a_1563_);
lean_inc(v_a_1562_);
lean_inc_ref(v_a_1561_);
v___x_1566_ = lean_infer_type(v_e_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v_a_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v_a_1567_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_a_1567_);
lean_dec_ref(v___x_1566_);
v___x_1568_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2);
v___x_1569_ = l_Lean_Meta_isExprDefEq(v_a_1567_, v___x_1568_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_);
return v___x_1569_;
}
else
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1577_; 
lean_dec(v_a_1564_);
lean_dec_ref(v_a_1563_);
lean_dec(v_a_1562_);
lean_dec_ref(v_a_1561_);
v_a_1570_ = lean_ctor_get(v___x_1566_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1572_ = v___x_1566_;
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1566_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1575_; 
if (v_isShared_1573_ == 0)
{
v___x_1575_ = v___x_1572_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_a_1570_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___boxed(lean_object* v_e_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(v_e_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt(lean_object* v_e_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_){
_start:
{
lean_object* v___x_1597_; 
v___x_1597_ = l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(v_e_1585_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___boxed(lean_object* v_e_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Lean_Meta_Grind_Arith_Cutsat_isInt(v_e_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_);
lean_dec(v_a_1604_);
lean_dec_ref(v_a_1603_);
lean_dec(v_a_1602_);
lean_dec_ref(v_a_1601_);
lean_dec(v_a_1600_);
lean_dec(v_a_1599_);
return v_res_1610_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4(void){
_start:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1617_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__3));
v___x_1618_ = l_Lean_stringToMessageData(v___x_1617_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(lean_object* v_e_1619_, uint8_t v_report_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_){
_start:
{
lean_object* v___x_1634_; 
lean_inc_ref(v_e_1619_);
v___x_1634_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1619_, v_a_1627_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1705_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1637_ = v___x_1634_;
v_isShared_1638_ = v_isSharedCheck_1705_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1634_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1705_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1644_; uint8_t v___x_1645_; 
v___x_1644_ = l_Lean_Expr_cleanupAnnotations(v_a_1635_);
v___x_1645_ = l_Lean_Expr_isApp(v___x_1644_);
if (v___x_1645_ == 0)
{
lean_dec_ref(v___x_1644_);
lean_dec_ref(v_e_1619_);
goto v___jp_1639_;
}
else
{
lean_object* v_arg_1646_; lean_object* v___x_1647_; uint8_t v___x_1648_; 
v_arg_1646_ = lean_ctor_get(v___x_1644_, 1);
lean_inc_ref(v_arg_1646_);
v___x_1647_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1644_);
v___x_1648_ = l_Lean_Expr_isApp(v___x_1647_);
if (v___x_1648_ == 0)
{
lean_dec_ref(v___x_1647_);
lean_dec_ref(v_arg_1646_);
lean_dec_ref(v_e_1619_);
goto v___jp_1639_;
}
else
{
lean_object* v_arg_1649_; lean_object* v___x_1650_; uint8_t v___x_1651_; 
v_arg_1649_ = lean_ctor_get(v___x_1647_, 1);
lean_inc_ref(v_arg_1649_);
v___x_1650_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1647_);
v___x_1651_ = l_Lean_Expr_isApp(v___x_1650_);
if (v___x_1651_ == 0)
{
lean_dec_ref(v___x_1650_);
lean_dec_ref(v_arg_1649_);
lean_dec_ref(v_arg_1646_);
lean_dec_ref(v_e_1619_);
goto v___jp_1639_;
}
else
{
lean_object* v_arg_1652_; lean_object* v___x_1653_; uint8_t v___x_1654_; 
v_arg_1652_ = lean_ctor_get(v___x_1650_, 1);
lean_inc_ref(v_arg_1652_);
v___x_1653_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1650_);
v___x_1654_ = l_Lean_Expr_isApp(v___x_1653_);
if (v___x_1654_ == 0)
{
lean_dec_ref(v___x_1653_);
lean_dec_ref(v_arg_1652_);
lean_dec_ref(v_arg_1649_);
lean_dec_ref(v_arg_1646_);
lean_dec_ref(v_e_1619_);
goto v___jp_1639_;
}
else
{
lean_object* v___x_1655_; uint8_t v___x_1656_; 
v___x_1655_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1653_);
v___x_1656_ = l_Lean_Expr_isApp(v___x_1655_);
if (v___x_1656_ == 0)
{
lean_dec_ref(v___x_1655_);
lean_dec_ref(v_arg_1652_);
lean_dec_ref(v_arg_1649_);
lean_dec_ref(v_arg_1646_);
lean_dec_ref(v_e_1619_);
goto v___jp_1639_;
}
else
{
lean_object* v___x_1657_; uint8_t v___x_1658_; 
v___x_1657_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1655_);
v___x_1658_ = l_Lean_Expr_isApp(v___x_1657_);
if (v___x_1658_ == 0)
{
lean_dec_ref(v___x_1657_);
lean_dec_ref(v_arg_1652_);
lean_dec_ref(v_arg_1649_);
lean_dec_ref(v_arg_1646_);
lean_dec_ref(v_e_1619_);
goto v___jp_1639_;
}
else
{
lean_object* v___x_1659_; lean_object* v___x_1660_; uint8_t v___x_1661_; 
v___x_1659_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1657_);
v___x_1660_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__2));
v___x_1661_ = l_Lean_Expr_isConstOf(v___x_1659_, v___x_1660_);
lean_dec_ref(v___x_1659_);
if (v___x_1661_ == 0)
{
lean_dec_ref(v_arg_1652_);
lean_dec_ref(v_arg_1649_);
lean_dec_ref(v_arg_1646_);
lean_dec_ref(v_e_1619_);
goto v___jp_1639_;
}
else
{
lean_object* v___x_1662_; 
lean_del_object(v___x_1637_);
v___x_1662_ = l_Lean_Meta_Structural_isInstHAddInt___redArg(v_arg_1652_, v_a_1627_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1696_; 
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1665_ = v___x_1662_;
v_isShared_1666_ = v_isSharedCheck_1696_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1662_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1696_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
uint8_t v___x_1667_; 
v___x_1667_ = lean_unbox(v_a_1663_);
lean_dec(v_a_1663_);
if (v___x_1667_ == 0)
{
lean_del_object(v___x_1665_);
lean_dec_ref(v_arg_1649_);
lean_dec_ref(v_arg_1646_);
if (v_report_1620_ == 0)
{
lean_dec_ref(v_e_1619_);
goto v___jp_1631_;
}
else
{
lean_object* v___x_1668_; 
v___x_1668_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1622_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; uint8_t v_verbose_1670_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
lean_inc(v_a_1669_);
lean_dec_ref(v___x_1668_);
v_verbose_1670_ = lean_ctor_get_uint8(v_a_1669_, sizeof(void*)*11 + 15);
lean_dec(v_a_1669_);
if (v_verbose_1670_ == 0)
{
lean_dec_ref(v_e_1619_);
goto v___jp_1631_;
}
else
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1671_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4);
v___x_1672_ = l_Lean_indentExpr(v_e_1619_);
v___x_1673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1671_);
lean_ctor_set(v___x_1673_, 1, v___x_1672_);
v___x_1674_ = l_Lean_Meta_Grind_reportIssue(v___x_1673_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_dec_ref(v___x_1674_);
goto v___jp_1631_;
}
else
{
lean_object* v_a_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1682_; 
v_a_1675_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1677_ = v___x_1674_;
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_a_1675_);
lean_dec(v___x_1674_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1680_; 
if (v_isShared_1678_ == 0)
{
v___x_1680_ = v___x_1677_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_a_1675_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
}
}
else
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
lean_dec_ref(v_e_1619_);
v_a_1683_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v___x_1668_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1668_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1683_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
}
else
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1694_; 
lean_dec_ref(v_e_1619_);
v___x_1691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1691_, 0, v_arg_1649_);
lean_ctor_set(v___x_1691_, 1, v_arg_1646_);
v___x_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1691_);
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 0, v___x_1692_);
v___x_1694_ = v___x_1665_;
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
}
}
else
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
lean_dec_ref(v_arg_1649_);
lean_dec_ref(v_arg_1646_);
lean_dec_ref(v_e_1619_);
v_a_1697_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1699_ = v___x_1662_;
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1662_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1700_ == 0)
{
v___x_1702_ = v___x_1699_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_a_1697_);
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
}
}
}
}
}
}
v___jp_1639_:
{
lean_object* v___x_1640_; lean_object* v___x_1642_; 
v___x_1640_ = lean_box(0);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v___x_1640_);
v___x_1642_ = v___x_1637_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1640_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
else
{
lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1713_; 
lean_dec_ref(v_e_1619_);
v_a_1706_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1708_ = v___x_1634_;
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_dec(v___x_1634_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1711_; 
if (v_isShared_1709_ == 0)
{
v___x_1711_ = v___x_1708_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_a_1706_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
v___jp_1631_:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1632_ = lean_box(0);
v___x_1633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1632_);
return v___x_1633_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___boxed(lean_object* v_e_1714_, lean_object* v_report_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_){
_start:
{
uint8_t v_report_boxed_1726_; lean_object* v_res_1727_; 
v_report_boxed_1726_ = lean_unbox(v_report_1715_);
v_res_1727_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_1714_, v_report_boxed_1726_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_);
lean_dec(v_a_1724_);
lean_dec_ref(v_a_1723_);
lean_dec(v_a_1722_);
lean_dec_ref(v_a_1721_);
lean_dec(v_a_1720_);
lean_dec_ref(v_a_1719_);
lean_dec(v_a_1718_);
lean_dec_ref(v_a_1717_);
lean_dec(v_a_1716_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f(lean_object* v_e_1728_, uint8_t v_report_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_){
_start:
{
lean_object* v___x_1741_; 
v___x_1741_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_1728_, v_report_1729_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_, v_a_1737_, v_a_1738_, v_a_1739_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___boxed(lean_object* v_e_1742_, lean_object* v_report_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_){
_start:
{
uint8_t v_report_boxed_1755_; lean_object* v_res_1756_; 
v_report_boxed_1755_ = lean_unbox(v_report_1743_);
v_res_1756_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f(v_e_1742_, v_report_boxed_1755_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_);
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
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(lean_object* v_e_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_){
_start:
{
uint8_t v___x_1768_; lean_object* v___x_1769_; 
v___x_1768_ = 0;
v___x_1769_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_1757_, v___x_1768_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1783_; 
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1772_ = v___x_1769_;
v_isShared_1773_ = v_isSharedCheck_1783_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1769_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1783_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
if (lean_obj_tag(v_a_1770_) == 0)
{
lean_object* v___x_1774_; lean_object* v___x_1776_; 
v___x_1774_ = lean_box(v___x_1768_);
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 0, v___x_1774_);
v___x_1776_ = v___x_1772_;
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
else
{
uint8_t v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1781_; 
lean_dec_ref(v_a_1770_);
v___x_1778_ = 1;
v___x_1779_ = lean_box(v___x_1778_);
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 0, v___x_1779_);
v___x_1781_ = v___x_1772_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1779_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
}
else
{
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1791_; 
v_a_1784_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1786_ = v___x_1769_;
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1769_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1789_; 
if (v_isShared_1787_ == 0)
{
v___x_1789_ = v___x_1786_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_a_1784_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg___boxed(lean_object* v_e_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(v_e_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_);
lean_dec(v_a_1801_);
lean_dec_ref(v_a_1800_);
lean_dec(v_a_1799_);
lean_dec_ref(v_a_1798_);
lean_dec(v_a_1797_);
lean_dec_ref(v_a_1796_);
lean_dec(v_a_1795_);
lean_dec_ref(v_a_1794_);
lean_dec(v_a_1793_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd(lean_object* v_e_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_){
_start:
{
lean_object* v___x_1816_; 
v___x_1816_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(v_e_1804_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___boxed(lean_object* v_e_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd(v_e_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_);
lean_dec(v_a_1827_);
lean_dec_ref(v_a_1826_);
lean_dec(v_a_1825_);
lean_dec_ref(v_a_1824_);
lean_dec(v_a_1823_);
lean_dec_ref(v_a_1822_);
lean_dec(v_a_1821_);
lean_dec_ref(v_a_1820_);
lean_dec(v_a_1819_);
lean_dec(v_a_1818_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(lean_object* v_e_1830_, uint8_t v_report_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_){
_start:
{
lean_object* v___x_1845_; 
lean_inc_ref(v_e_1830_);
v___x_1845_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1830_, v_a_1838_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1937_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1848_ = v___x_1845_;
v_isShared_1849_ = v_isSharedCheck_1937_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1845_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1937_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1855_; uint8_t v___x_1856_; 
v___x_1855_ = l_Lean_Expr_cleanupAnnotations(v_a_1846_);
v___x_1856_ = l_Lean_Expr_isApp(v___x_1855_);
if (v___x_1856_ == 0)
{
lean_dec_ref(v___x_1855_);
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
lean_dec_ref(v_e_1830_);
goto v___jp_1850_;
}
else
{
lean_object* v_arg_1857_; lean_object* v___x_1858_; uint8_t v___x_1859_; 
v_arg_1857_ = lean_ctor_get(v___x_1855_, 1);
lean_inc_ref(v_arg_1857_);
v___x_1858_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1855_);
v___x_1859_ = l_Lean_Expr_isApp(v___x_1858_);
if (v___x_1859_ == 0)
{
lean_dec_ref(v___x_1858_);
lean_dec_ref(v_arg_1857_);
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
lean_dec_ref(v_e_1830_);
goto v___jp_1850_;
}
else
{
lean_object* v_arg_1860_; lean_object* v___x_1861_; uint8_t v___x_1862_; 
v_arg_1860_ = lean_ctor_get(v___x_1858_, 1);
lean_inc_ref(v_arg_1860_);
v___x_1861_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1858_);
v___x_1862_ = l_Lean_Expr_isApp(v___x_1861_);
if (v___x_1862_ == 0)
{
lean_dec_ref(v___x_1861_);
lean_dec_ref(v_arg_1860_);
lean_dec_ref(v_arg_1857_);
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
lean_dec_ref(v_e_1830_);
goto v___jp_1850_;
}
else
{
lean_object* v_arg_1863_; lean_object* v___x_1864_; uint8_t v___x_1865_; 
v_arg_1863_ = lean_ctor_get(v___x_1861_, 1);
lean_inc_ref(v_arg_1863_);
v___x_1864_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1861_);
v___x_1865_ = l_Lean_Expr_isApp(v___x_1864_);
if (v___x_1865_ == 0)
{
lean_dec_ref(v___x_1864_);
lean_dec_ref(v_arg_1863_);
lean_dec_ref(v_arg_1860_);
lean_dec_ref(v_arg_1857_);
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
lean_dec_ref(v_e_1830_);
goto v___jp_1850_;
}
else
{
lean_object* v___x_1866_; uint8_t v___x_1867_; 
v___x_1866_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1864_);
v___x_1867_ = l_Lean_Expr_isApp(v___x_1866_);
if (v___x_1867_ == 0)
{
lean_dec_ref(v___x_1866_);
lean_dec_ref(v_arg_1863_);
lean_dec_ref(v_arg_1860_);
lean_dec_ref(v_arg_1857_);
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
lean_dec_ref(v_e_1830_);
goto v___jp_1850_;
}
else
{
lean_object* v___x_1868_; uint8_t v___x_1869_; 
v___x_1868_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1866_);
v___x_1869_ = l_Lean_Expr_isApp(v___x_1868_);
if (v___x_1869_ == 0)
{
lean_dec_ref(v___x_1868_);
lean_dec_ref(v_arg_1863_);
lean_dec_ref(v_arg_1860_);
lean_dec_ref(v_arg_1857_);
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
lean_dec_ref(v_e_1830_);
goto v___jp_1850_;
}
else
{
lean_object* v___x_1870_; lean_object* v___x_1871_; uint8_t v___x_1872_; 
v___x_1870_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1868_);
v___x_1871_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11));
v___x_1872_ = l_Lean_Expr_isConstOf(v___x_1870_, v___x_1871_);
lean_dec_ref(v___x_1870_);
if (v___x_1872_ == 0)
{
lean_dec_ref(v_arg_1863_);
lean_dec_ref(v_arg_1860_);
lean_dec_ref(v_arg_1857_);
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
lean_dec_ref(v_e_1830_);
goto v___jp_1850_;
}
else
{
lean_object* v___x_1873_; 
lean_del_object(v___x_1848_);
v___x_1873_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_1863_, v_a_1838_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_a_1874_; uint8_t v___x_1875_; 
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
lean_inc(v_a_1874_);
lean_dec_ref(v___x_1873_);
v___x_1875_ = lean_unbox(v_a_1874_);
lean_dec(v_a_1874_);
if (v___x_1875_ == 0)
{
lean_dec_ref(v_arg_1860_);
lean_dec_ref(v_arg_1857_);
if (v_report_1831_ == 0)
{
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
lean_dec_ref(v_e_1830_);
goto v___jp_1842_;
}
else
{
lean_object* v___x_1876_; 
v___x_1876_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1833_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; uint8_t v_verbose_1878_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
lean_inc(v_a_1877_);
lean_dec_ref(v___x_1876_);
v_verbose_1878_ = lean_ctor_get_uint8(v_a_1877_, sizeof(void*)*11 + 15);
lean_dec(v_a_1877_);
if (v_verbose_1878_ == 0)
{
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
lean_dec_ref(v_e_1830_);
goto v___jp_1842_;
}
else
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1879_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4);
v___x_1880_ = l_Lean_indentExpr(v_e_1830_);
v___x_1881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1879_);
lean_ctor_set(v___x_1881_, 1, v___x_1880_);
v___x_1882_ = l_Lean_Meta_Grind_reportIssue(v___x_1881_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_);
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_dec_ref(v___x_1882_);
goto v___jp_1842_;
}
else
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1890_; 
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1885_ = v___x_1882_;
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1882_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1886_ == 0)
{
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_a_1883_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
}
}
else
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
lean_dec_ref(v_e_1830_);
v_a_1891_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v___x_1876_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1876_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
}
else
{
lean_object* v___x_1899_; 
lean_dec_ref(v_e_1830_);
v___x_1899_ = l_Lean_Meta_getIntValue_x3f(v_arg_1860_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1920_; 
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1902_ = v___x_1899_;
v_isShared_1903_ = v_isSharedCheck_1920_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_dec(v___x_1899_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1920_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
if (lean_obj_tag(v_a_1900_) == 1)
{
lean_object* v_val_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1915_; 
v_val_1904_ = lean_ctor_get(v_a_1900_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v_a_1900_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1906_ = v_a_1900_;
v_isShared_1907_ = v_isSharedCheck_1915_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_val_1904_);
lean_dec(v_a_1900_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1915_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1908_; lean_object* v___x_1910_; 
v___x_1908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1908_, 0, v_val_1904_);
lean_ctor_set(v___x_1908_, 1, v_arg_1857_);
if (v_isShared_1907_ == 0)
{
lean_ctor_set(v___x_1906_, 0, v___x_1908_);
v___x_1910_ = v___x_1906_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1908_);
v___x_1910_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
lean_object* v___x_1912_; 
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v___x_1910_);
v___x_1912_ = v___x_1902_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v___x_1910_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
else
{
lean_object* v___x_1916_; lean_object* v___x_1918_; 
lean_dec(v_a_1900_);
lean_dec_ref(v_arg_1857_);
v___x_1916_ = lean_box(0);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v___x_1916_);
v___x_1918_ = v___x_1902_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v___x_1916_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
else
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1928_; 
lean_dec_ref(v_arg_1857_);
v_a_1921_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1923_ = v___x_1899_;
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1899_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1926_; 
if (v_isShared_1924_ == 0)
{
v___x_1926_ = v___x_1923_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1921_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
}
else
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
lean_dec_ref(v_arg_1860_);
lean_dec_ref(v_arg_1857_);
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
lean_dec_ref(v_e_1830_);
v_a_1929_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1931_ = v___x_1873_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1873_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1929_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
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
v___jp_1850_:
{
lean_object* v___x_1851_; lean_object* v___x_1853_; 
v___x_1851_ = lean_box(0);
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 0, v___x_1851_);
v___x_1853_ = v___x_1848_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1851_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
}
else
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
lean_dec_ref(v_e_1830_);
v_a_1938_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1940_ = v___x_1845_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1845_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1938_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
v___jp_1842_:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1843_ = lean_box(0);
v___x_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
return v___x_1844_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg___boxed(lean_object* v_e_1946_, lean_object* v_report_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_){
_start:
{
uint8_t v_report_boxed_1958_; lean_object* v_res_1959_; 
v_report_boxed_1958_ = lean_unbox(v_report_1947_);
v_res_1959_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1946_, v_report_boxed_1958_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_);
lean_dec(v_a_1952_);
lean_dec_ref(v_a_1951_);
lean_dec(v_a_1950_);
lean_dec_ref(v_a_1949_);
lean_dec(v_a_1948_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f(lean_object* v_e_1960_, uint8_t v_report_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_){
_start:
{
lean_object* v___x_1973_; 
v___x_1973_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1960_, v_report_1961_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___boxed(lean_object* v_e_1974_, lean_object* v_report_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_){
_start:
{
uint8_t v_report_boxed_1987_; lean_object* v_res_1988_; 
v_report_boxed_1987_ = lean_unbox(v_report_1975_);
v_res_1988_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f(v_e_1974_, v_report_boxed_1987_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_);
lean_dec(v_a_1981_);
lean_dec_ref(v_a_1980_);
lean_dec(v_a_1979_);
lean_dec_ref(v_a_1978_);
lean_dec(v_a_1977_);
lean_dec(v_a_1976_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(lean_object* v_e_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_){
_start:
{
uint8_t v___x_2000_; lean_object* v___x_2001_; 
v___x_2000_ = 0;
v___x_2001_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1989_, v___x_2000_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2015_; 
v_a_2002_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2004_ = v___x_2001_;
v_isShared_2005_ = v_isSharedCheck_2015_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_dec(v___x_2001_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2015_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
if (lean_obj_tag(v_a_2002_) == 0)
{
lean_object* v___x_2006_; lean_object* v___x_2008_; 
v___x_2006_ = lean_box(v___x_2000_);
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 0, v___x_2006_);
v___x_2008_ = v___x_2004_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_2006_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
else
{
uint8_t v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2013_; 
lean_dec_ref(v_a_2002_);
v___x_2010_ = 1;
v___x_2011_ = lean_box(v___x_2010_);
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 0, v___x_2011_);
v___x_2013_ = v___x_2004_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2011_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
else
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
v_a_2016_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_2001_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_2001_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_2016_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg___boxed(lean_object* v_e_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(v_e_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_);
lean_dec(v_a_2029_);
lean_dec_ref(v_a_2028_);
lean_dec(v_a_2027_);
lean_dec_ref(v_a_2026_);
lean_dec(v_a_2025_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul(lean_object* v_e_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_){
_start:
{
lean_object* v___x_2048_; 
v___x_2048_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(v_e_2036_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___boxed(lean_object* v_e_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul(v_e_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_);
lean_dec(v_a_2055_);
lean_dec_ref(v_a_2054_);
lean_dec(v_a_2053_);
lean_dec_ref(v_a_2052_);
lean_dec(v_a_2051_);
lean_dec(v_a_2050_);
return v_res_2061_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0(void){
_start:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2062_ = lean_unsigned_to_nat(1u);
v___x_2063_ = lean_nat_to_int(v___x_2062_);
return v___x_2063_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2(void){
_start:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2065_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__1));
v___x_2066_ = l_Lean_stringToMessageData(v___x_2065_);
return v___x_2066_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4(void){
_start:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2068_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__3));
v___x_2069_ = l_Lean_stringToMessageData(v___x_2068_);
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(lean_object* v_e_2070_, lean_object* v_p_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_){
_start:
{
lean_object* v___y_2084_; lean_object* v___y_2085_; lean_object* v___y_2086_; lean_object* v___y_2087_; lean_object* v___y_2088_; lean_object* v___y_2089_; lean_object* v___y_2090_; lean_object* v___y_2091_; lean_object* v___y_2092_; lean_object* v___y_2093_; uint8_t v___x_2113_; lean_object* v___x_2114_; 
v___x_2113_ = 1;
lean_inc(v_a_2081_);
lean_inc_ref(v_a_2080_);
lean_inc(v_a_2079_);
lean_inc_ref(v_a_2078_);
lean_inc_ref(v_e_2070_);
v___x_2114_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_2070_, v___x_2113_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; 
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_a_2115_);
lean_dec_ref(v___x_2114_);
if (lean_obj_tag(v_a_2115_) == 1)
{
lean_object* v_val_2116_; lean_object* v_fst_2117_; lean_object* v_snd_2118_; lean_object* v___x_2119_; 
lean_dec_ref(v_e_2070_);
v_val_2116_ = lean_ctor_get(v_a_2115_, 0);
lean_inc(v_val_2116_);
lean_dec_ref(v_a_2115_);
v_fst_2117_ = lean_ctor_get(v_val_2116_, 0);
lean_inc(v_fst_2117_);
v_snd_2118_ = lean_ctor_get(v_val_2116_, 1);
lean_inc(v_snd_2118_);
lean_dec(v_val_2116_);
v___x_2119_ = lean_grind_cutsat_mk_var(v_snd_2118_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2128_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2122_ = v___x_2119_;
v_isShared_2123_ = v_isSharedCheck_2128_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2119_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2128_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2124_; lean_object* v___x_2126_; 
v___x_2124_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2124_, 0, v_fst_2117_);
lean_ctor_set(v___x_2124_, 1, v_a_2120_);
lean_ctor_set(v___x_2124_, 2, v_p_2071_);
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 0, v___x_2124_);
v___x_2126_ = v___x_2122_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v___x_2124_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
else
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2136_; 
lean_dec(v_fst_2117_);
lean_dec_ref(v_p_2071_);
v_a_2129_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2131_ = v___x_2119_;
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2119_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2134_; 
if (v_isShared_2132_ == 0)
{
v___x_2134_ = v___x_2131_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_a_2129_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
}
else
{
lean_object* v___x_2137_; 
lean_dec(v_a_2115_);
lean_inc(v_a_2081_);
lean_inc_ref(v_a_2080_);
lean_inc(v_a_2079_);
lean_inc_ref(v_a_2078_);
lean_inc_ref(v_e_2070_);
v___x_2137_ = l_Lean_Meta_getIntValue_x3f(v_e_2070_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2179_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2140_ = v___x_2137_;
v_isShared_2141_ = v_isSharedCheck_2179_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2137_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2179_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
if (lean_obj_tag(v_a_2138_) == 1)
{
lean_object* v_val_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2178_; 
v_val_2142_ = lean_ctor_get(v_a_2138_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v_a_2138_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2144_ = v_a_2138_;
v_isShared_2145_ = v_isSharedCheck_2178_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_val_2142_);
lean_dec(v_a_2138_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2178_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
uint8_t v___x_2146_; 
v___x_2146_ = l_Int_Linear_Poly_isZero(v_p_2071_);
if (v___x_2146_ == 0)
{
lean_object* v___x_2147_; 
lean_del_object(v___x_2144_);
lean_dec(v_val_2142_);
lean_del_object(v___x_2140_);
v___x_2147_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2074_);
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_object* v_a_2148_; uint8_t v_verbose_2149_; 
v_a_2148_ = lean_ctor_get(v___x_2147_, 0);
lean_inc(v_a_2148_);
lean_dec_ref(v___x_2147_);
v_verbose_2149_ = lean_ctor_get_uint8(v_a_2148_, sizeof(void*)*11 + 15);
lean_dec(v_a_2148_);
if (v_verbose_2149_ == 0)
{
v___y_2084_ = v_a_2072_;
v___y_2085_ = v_a_2073_;
v___y_2086_ = v_a_2074_;
v___y_2087_ = v_a_2075_;
v___y_2088_ = v_a_2076_;
v___y_2089_ = v_a_2077_;
v___y_2090_ = v_a_2078_;
v___y_2091_ = v_a_2079_;
v___y_2092_ = v_a_2080_;
v___y_2093_ = v_a_2081_;
goto v___jp_2083_;
}
else
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2150_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2);
lean_inc_ref(v_e_2070_);
v___x_2151_ = l_Lean_indentExpr(v_e_2070_);
v___x_2152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2150_);
lean_ctor_set(v___x_2152_, 1, v___x_2151_);
v___x_2153_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4);
v___x_2154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2152_);
lean_ctor_set(v___x_2154_, 1, v___x_2153_);
v___x_2155_ = l_Lean_Meta_Grind_reportIssue(v___x_2154_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_dec_ref(v___x_2155_);
v___y_2084_ = v_a_2072_;
v___y_2085_ = v_a_2073_;
v___y_2086_ = v_a_2074_;
v___y_2087_ = v_a_2075_;
v___y_2088_ = v_a_2076_;
v___y_2089_ = v_a_2077_;
v___y_2090_ = v_a_2078_;
v___y_2091_ = v_a_2079_;
v___y_2092_ = v_a_2080_;
v___y_2093_ = v_a_2081_;
goto v___jp_2083_;
}
else
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2163_; 
lean_dec(v_a_2081_);
lean_dec_ref(v_a_2080_);
lean_dec(v_a_2079_);
lean_dec_ref(v_a_2078_);
lean_dec(v_a_2077_);
lean_dec_ref(v_a_2076_);
lean_dec(v_a_2075_);
lean_dec_ref(v_a_2074_);
lean_dec(v_a_2073_);
lean_dec(v_a_2072_);
lean_dec_ref(v_p_2071_);
lean_dec_ref(v_e_2070_);
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2158_ = v___x_2155_;
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2155_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2161_; 
if (v_isShared_2159_ == 0)
{
v___x_2161_ = v___x_2158_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_a_2156_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
}
else
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
lean_dec(v_a_2081_);
lean_dec_ref(v_a_2080_);
lean_dec(v_a_2079_);
lean_dec_ref(v_a_2078_);
lean_dec(v_a_2077_);
lean_dec_ref(v_a_2076_);
lean_dec(v_a_2075_);
lean_dec_ref(v_a_2074_);
lean_dec(v_a_2073_);
lean_dec(v_a_2072_);
lean_dec_ref(v_p_2071_);
lean_dec_ref(v_e_2070_);
v_a_2164_ = lean_ctor_get(v___x_2147_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_2147_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2147_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2164_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
else
{
lean_object* v___x_2173_; 
lean_dec(v_a_2081_);
lean_dec_ref(v_a_2080_);
lean_dec(v_a_2079_);
lean_dec_ref(v_a_2078_);
lean_dec(v_a_2077_);
lean_dec_ref(v_a_2076_);
lean_dec(v_a_2075_);
lean_dec_ref(v_a_2074_);
lean_dec(v_a_2073_);
lean_dec(v_a_2072_);
lean_dec_ref(v_p_2071_);
lean_dec_ref(v_e_2070_);
if (v_isShared_2145_ == 0)
{
lean_ctor_set_tag(v___x_2144_, 0);
v___x_2173_ = v___x_2144_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_val_2142_);
v___x_2173_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
lean_object* v___x_2175_; 
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 0, v___x_2173_);
v___x_2175_ = v___x_2140_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v___x_2173_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
}
}
else
{
lean_del_object(v___x_2140_);
lean_dec(v_a_2138_);
v___y_2084_ = v_a_2072_;
v___y_2085_ = v_a_2073_;
v___y_2086_ = v_a_2074_;
v___y_2087_ = v_a_2075_;
v___y_2088_ = v_a_2076_;
v___y_2089_ = v_a_2077_;
v___y_2090_ = v_a_2078_;
v___y_2091_ = v_a_2079_;
v___y_2092_ = v_a_2080_;
v___y_2093_ = v_a_2081_;
goto v___jp_2083_;
}
}
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
lean_dec(v_a_2081_);
lean_dec_ref(v_a_2080_);
lean_dec(v_a_2079_);
lean_dec_ref(v_a_2078_);
lean_dec(v_a_2077_);
lean_dec_ref(v_a_2076_);
lean_dec(v_a_2075_);
lean_dec_ref(v_a_2074_);
lean_dec(v_a_2073_);
lean_dec(v_a_2072_);
lean_dec_ref(v_p_2071_);
lean_dec_ref(v_e_2070_);
v_a_2180_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2137_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2137_);
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
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
lean_dec(v_a_2081_);
lean_dec_ref(v_a_2080_);
lean_dec(v_a_2079_);
lean_dec_ref(v_a_2078_);
lean_dec(v_a_2077_);
lean_dec_ref(v_a_2076_);
lean_dec(v_a_2075_);
lean_dec_ref(v_a_2074_);
lean_dec(v_a_2073_);
lean_dec(v_a_2072_);
lean_dec_ref(v_p_2071_);
lean_dec_ref(v_e_2070_);
v_a_2188_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___x_2114_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2114_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2193_; 
if (v_isShared_2191_ == 0)
{
v___x_2193_ = v___x_2190_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2188_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
v___jp_2083_:
{
lean_object* v___x_2094_; 
v___x_2094_ = lean_grind_cutsat_mk_var(v_e_2070_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2104_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2097_ = v___x_2094_;
v_isShared_2098_ = v_isSharedCheck_2104_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2094_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2104_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2102_; 
v___x_2099_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0);
v___x_2100_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2099_);
lean_ctor_set(v___x_2100_, 1, v_a_2095_);
lean_ctor_set(v___x_2100_, 2, v_p_2071_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 0, v___x_2100_);
v___x_2102_ = v___x_2097_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v___x_2100_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
else
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
lean_dec_ref(v_p_2071_);
v_a_2105_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2107_ = v___x_2094_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_2094_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___boxed(lean_object* v_e_2196_, lean_object* v_p_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_){
_start:
{
lean_object* v_res_2209_; 
v_res_2209_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_e_2196_, v_p_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_, v_a_2207_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go(lean_object* v_e_2210_, lean_object* v_p_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_){
_start:
{
uint8_t v___x_2223_; lean_object* v___x_2224_; 
v___x_2223_ = 1;
lean_inc_ref(v_e_2210_);
v___x_2224_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_2210_, v___x_2223_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v_a_2225_; 
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
lean_inc(v_a_2225_);
lean_dec_ref(v___x_2224_);
if (lean_obj_tag(v_a_2225_) == 1)
{
lean_object* v_val_2226_; lean_object* v_fst_2227_; lean_object* v_snd_2228_; lean_object* v___x_2229_; 
lean_dec_ref(v_e_2210_);
v_val_2226_ = lean_ctor_get(v_a_2225_, 0);
lean_inc(v_val_2226_);
lean_dec_ref(v_a_2225_);
v_fst_2227_ = lean_ctor_get(v_val_2226_, 0);
lean_inc(v_fst_2227_);
v_snd_2228_ = lean_ctor_get(v_val_2226_, 1);
lean_inc(v_snd_2228_);
lean_dec(v_val_2226_);
lean_inc(v_a_2221_);
lean_inc_ref(v_a_2220_);
lean_inc(v_a_2219_);
lean_inc_ref(v_a_2218_);
lean_inc(v_a_2217_);
lean_inc_ref(v_a_2216_);
lean_inc(v_a_2215_);
lean_inc_ref(v_a_2214_);
lean_inc(v_a_2213_);
lean_inc(v_a_2212_);
v___x_2229_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_snd_2228_, v_p_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v_a_2230_; 
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
lean_inc(v_a_2230_);
lean_dec_ref(v___x_2229_);
v_e_2210_ = v_fst_2227_;
v_p_2211_ = v_a_2230_;
goto _start;
}
else
{
lean_dec(v_fst_2227_);
lean_dec(v_a_2221_);
lean_dec_ref(v_a_2220_);
lean_dec(v_a_2219_);
lean_dec_ref(v_a_2218_);
lean_dec(v_a_2217_);
lean_dec_ref(v_a_2216_);
lean_dec(v_a_2215_);
lean_dec_ref(v_a_2214_);
lean_dec(v_a_2213_);
lean_dec(v_a_2212_);
return v___x_2229_;
}
}
else
{
lean_object* v___x_2232_; 
lean_dec(v_a_2225_);
v___x_2232_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_e_2210_, v_p_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
return v___x_2232_;
}
}
else
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2240_; 
lean_dec(v_a_2221_);
lean_dec_ref(v_a_2220_);
lean_dec(v_a_2219_);
lean_dec_ref(v_a_2218_);
lean_dec(v_a_2217_);
lean_dec_ref(v_a_2216_);
lean_dec(v_a_2215_);
lean_dec_ref(v_a_2214_);
lean_dec(v_a_2213_);
lean_dec(v_a_2212_);
lean_dec_ref(v_p_2211_);
lean_dec_ref(v_e_2210_);
v_a_2233_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2235_ = v___x_2224_;
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_2224_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2238_; 
if (v_isShared_2236_ == 0)
{
v___x_2238_ = v___x_2235_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_a_2233_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go___boxed(lean_object* v_e_2241_, lean_object* v_p_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go(v_e_2241_, v_p_2242_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_);
return v_res_2254_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0(void){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = lean_unsigned_to_nat(0u);
v___x_2256_ = lean_nat_to_int(v___x_2255_);
return v___x_2256_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1(void){
_start:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2257_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0);
v___x_2258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
return v___x_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly(lean_object* v_e_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_){
_start:
{
uint8_t v___x_2271_; lean_object* v___x_2272_; 
v___x_2271_ = 1;
lean_inc_ref(v_e_2259_);
v___x_2272_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_2259_, v___x_2271_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_object* v_a_2273_; 
v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
lean_inc(v_a_2273_);
lean_dec_ref(v___x_2272_);
if (lean_obj_tag(v_a_2273_) == 1)
{
lean_object* v_val_2274_; lean_object* v_fst_2275_; lean_object* v_snd_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
lean_dec_ref(v_e_2259_);
v_val_2274_ = lean_ctor_get(v_a_2273_, 0);
lean_inc(v_val_2274_);
lean_dec_ref(v_a_2273_);
v_fst_2275_ = lean_ctor_get(v_val_2274_, 0);
lean_inc(v_fst_2275_);
v_snd_2276_ = lean_ctor_get(v_val_2274_, 1);
lean_inc(v_snd_2276_);
lean_dec(v_val_2274_);
v___x_2277_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1);
lean_inc(v_a_2269_);
lean_inc_ref(v_a_2268_);
lean_inc(v_a_2267_);
lean_inc_ref(v_a_2266_);
lean_inc(v_a_2265_);
lean_inc_ref(v_a_2264_);
lean_inc(v_a_2263_);
lean_inc_ref(v_a_2262_);
lean_inc(v_a_2261_);
lean_inc(v_a_2260_);
v___x_2278_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_snd_2276_, v___x_2277_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; lean_object* v___x_2280_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
lean_inc(v_a_2279_);
lean_dec_ref(v___x_2278_);
v___x_2280_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go(v_fst_2275_, v_a_2279_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_);
return v___x_2280_;
}
else
{
lean_dec(v_fst_2275_);
lean_dec(v_a_2269_);
lean_dec_ref(v_a_2268_);
lean_dec(v_a_2267_);
lean_dec_ref(v_a_2266_);
lean_dec(v_a_2265_);
lean_dec_ref(v_a_2264_);
lean_dec(v_a_2263_);
lean_dec_ref(v_a_2262_);
lean_dec(v_a_2261_);
lean_dec(v_a_2260_);
return v___x_2278_;
}
}
else
{
lean_object* v___x_2281_; lean_object* v___x_2282_; 
lean_dec(v_a_2273_);
v___x_2281_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1);
v___x_2282_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_e_2259_, v___x_2281_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_);
return v___x_2282_;
}
}
else
{
lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2290_; 
lean_dec(v_a_2269_);
lean_dec_ref(v_a_2268_);
lean_dec(v_a_2267_);
lean_dec_ref(v_a_2266_);
lean_dec(v_a_2265_);
lean_dec_ref(v_a_2264_);
lean_dec(v_a_2263_);
lean_dec_ref(v_a_2262_);
lean_dec(v_a_2261_);
lean_dec(v_a_2260_);
lean_dec_ref(v_e_2259_);
v_a_2283_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2285_ = v___x_2272_;
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___x_2272_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2288_; 
if (v_isShared_2286_ == 0)
{
v___x_2288_ = v___x_2285_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_a_2283_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly___boxed(lean_object* v_e_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_e_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_);
return v_res_2303_;
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
