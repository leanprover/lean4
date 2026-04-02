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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHAddInt___redArg(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_a_91_);
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
lean_dec_ref(v_a_110_);
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
lean_dec_ref(v___x_128_);
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
size_t v_x_9049__boxed_335_; size_t v_x_9050__boxed_336_; lean_object* v_res_337_; 
v_x_9049__boxed_335_ = lean_unbox_usize(v_x_331_);
lean_dec(v_x_331_);
v_x_9050__boxed_336_ = lean_unbox_usize(v_x_332_);
lean_dec(v_x_332_);
v_res_337_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_x_330_, v_x_9049__boxed_335_, v_x_9050__boxed_336_, v_x_333_, v_x_334_);
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
size_t v_x_9271__boxed_434_; lean_object* v_res_435_; 
v_x_9271__boxed_434_ = lean_unbox_usize(v_x_432_);
lean_dec(v_x_432_);
v_res_435_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2___redArg(v_x_431_, v_x_9271__boxed_434_, v_x_433_);
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
lean_dec_ref(v_elimEqs_517_);
v___y_497_ = v___x_522_;
goto v___jp_496_;
}
v___jp_496_:
{
if (lean_obj_tag(v___y_497_) == 0)
{
v___y_477_ = v_a_448_;
v___y_478_ = v_a_456_;
goto v___jp_476_;
}
else
{
lean_object* v___x_498_; 
lean_dec_ref(v___y_497_);
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
lean_inc_ref(v___y_465_);
v___x_468_ = l_List_elem___redArg(v___y_465_, v_x_447_, v___y_467_);
if (v___x_468_ == 0)
{
lean_object* v___f_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
lean_del_object(v___x_462_);
v___f_469_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___lam__0), 4, 3);
lean_closure_set(v___f_469_, 0, v_x_447_);
lean_closure_set(v___f_469_, 1, v___y_467_);
lean_closure_set(v___f_469_, 2, v_a_460_);
v___x_470_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_471_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_470_, v___f_469_, v___y_466_);
return v___x_471_;
}
else
{
lean_object* v___x_472_; lean_object* v___x_474_; 
lean_dec(v___y_467_);
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
v___y_465_ = v___f_482_;
v___y_466_ = v___y_477_;
v___y_467_ = v___x_484_;
goto v___jp_464_;
}
else
{
lean_object* v_val_485_; 
v_val_485_ = lean_ctor_get(v___x_483_, 0);
lean_inc(v_val_485_);
lean_dec_ref(v___x_483_);
v___y_465_ = v___f_482_;
v___y_466_ = v___y_477_;
v___y_467_ = v_val_485_;
goto v___jp_464_;
}
}
else
{
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
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
lean_dec(v_a_551_);
lean_dec_ref(v_a_550_);
lean_dec(v_a_549_);
lean_dec_ref(v_a_548_);
lean_dec(v_a_547_);
lean_dec_ref(v_a_546_);
lean_dec(v_a_545_);
lean_dec_ref(v_a_544_);
lean_dec(v_a_543_);
lean_dec(v_a_542_);
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
size_t v_x_9526__boxed_580_; size_t v_x_9527__boxed_581_; lean_object* v_res_582_; 
v_x_9526__boxed_580_ = lean_unbox_usize(v_x_576_);
lean_dec(v_x_576_);
v_x_9527__boxed_581_ = lean_unbox_usize(v_x_577_);
lean_dec(v_x_577_);
v_res_582_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0(v_00_u03b2_574_, v_x_575_, v_x_9526__boxed_580_, v_x_9527__boxed_581_, v_x_578_, v_x_579_);
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
size_t v_x_9543__boxed_592_; lean_object* v_res_593_; 
v_x_9543__boxed_592_ = lean_unbox_usize(v_x_590_);
lean_dec(v_x_590_);
v_res_593_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2(v_00_u03b2_588_, v_x_589_, v_x_9543__boxed_592_, v_x_591_);
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
lean_dec(v_a_709_);
lean_dec_ref(v_a_708_);
lean_dec(v_a_707_);
lean_dec_ref(v_a_706_);
lean_dec(v_a_705_);
lean_dec_ref(v_a_704_);
lean_dec(v_a_703_);
lean_dec_ref(v_a_702_);
lean_dec(v_a_701_);
lean_dec(v_a_700_);
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
lean_dec(v_x_713_);
goto v___jp_733_;
}
else
{
lean_object* v___x_816_; 
lean_del_object(v___x_731_);
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
lean_inc_ref(v_arg_740_);
v___x_766_ = l_Lean_Meta_getIntValue_x3f(v_arg_740_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v___x_768_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_a_767_);
lean_dec_ref(v___x_766_);
v___x_768_ = l_Lean_Meta_getNatValue_x3f(v_arg_740_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
if (lean_obj_tag(v___x_768_) == 0)
{
if (lean_obj_tag(v_a_767_) == 0)
{
if (v___x_754_ == 0)
{
lean_dec_ref(v___x_768_);
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
lean_dec(v_x_713_);
return v___x_776_;
}
}
else
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
lean_dec(v_fst_772_);
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
lean_dec_ref(v_arg_740_);
lean_dec(v_x_713_);
goto v___jp_725_;
}
}
else
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
lean_dec(v_a_767_);
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
lean_dec(v_a_851_);
lean_dec_ref(v_a_850_);
lean_dec(v_a_849_);
lean_dec_ref(v_a_848_);
lean_dec(v_a_847_);
lean_dec_ref(v_a_846_);
lean_dec(v_a_845_);
lean_dec_ref(v_a_844_);
lean_dec(v_a_843_);
lean_dec(v_a_842_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7___redArg(lean_object* v_x_854_, lean_object* v_x_855_, lean_object* v_x_856_, lean_object* v_x_857_){
_start:
{
lean_object* v_ks_858_; lean_object* v_vs_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_883_; 
v_ks_858_ = lean_ctor_get(v_x_854_, 0);
v_vs_859_ = lean_ctor_get(v_x_854_, 1);
v_isSharedCheck_883_ = !lean_is_exclusive(v_x_854_);
if (v_isSharedCheck_883_ == 0)
{
v___x_861_ = v_x_854_;
v_isShared_862_ = v_isSharedCheck_883_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_vs_859_);
lean_inc(v_ks_858_);
lean_dec(v_x_854_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_883_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_863_; uint8_t v___x_864_; 
v___x_863_ = lean_array_get_size(v_ks_858_);
v___x_864_ = lean_nat_dec_lt(v_x_855_, v___x_863_);
if (v___x_864_ == 0)
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_868_; 
lean_dec(v_x_855_);
v___x_865_ = lean_array_push(v_ks_858_, v_x_856_);
v___x_866_ = lean_array_push(v_vs_859_, v_x_857_);
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 1, v___x_866_);
lean_ctor_set(v___x_861_, 0, v___x_865_);
v___x_868_ = v___x_861_;
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
else
{
lean_object* v_k_x27_870_; uint8_t v___x_871_; 
v_k_x27_870_ = lean_array_fget_borrowed(v_ks_858_, v_x_855_);
v___x_871_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_856_, v_k_x27_870_);
if (v___x_871_ == 0)
{
lean_object* v___x_873_; 
if (v_isShared_862_ == 0)
{
v___x_873_ = v___x_861_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_ks_858_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_vs_859_);
v___x_873_ = v_reuseFailAlloc_877_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = lean_unsigned_to_nat(1u);
v___x_875_ = lean_nat_add(v_x_855_, v___x_874_);
lean_dec(v_x_855_);
v_x_854_ = v___x_873_;
v_x_855_ = v___x_875_;
goto _start;
}
}
else
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_881_; 
v___x_878_ = lean_array_fset(v_ks_858_, v_x_855_, v_x_856_);
v___x_879_ = lean_array_fset(v_vs_859_, v_x_855_, v_x_857_);
lean_dec(v_x_855_);
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 1, v___x_879_);
lean_ctor_set(v___x_861_, 0, v___x_878_);
v___x_881_ = v___x_861_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_878_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v___x_879_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4___redArg(lean_object* v_n_884_, lean_object* v_k_885_, lean_object* v_v_886_){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = lean_unsigned_to_nat(0u);
v___x_888_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7___redArg(v_n_884_, v___x_887_, v_k_885_, v_v_886_);
return v___x_888_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(lean_object* v_x_890_, size_t v_x_891_, size_t v_x_892_, lean_object* v_x_893_, lean_object* v_x_894_){
_start:
{
if (lean_obj_tag(v_x_890_) == 0)
{
lean_object* v_es_895_; size_t v___x_896_; size_t v___x_897_; size_t v___x_898_; size_t v___x_899_; lean_object* v_j_900_; lean_object* v___x_901_; uint8_t v___x_902_; 
v_es_895_ = lean_ctor_get(v_x_890_, 0);
v___x_896_ = ((size_t)5ULL);
v___x_897_ = ((size_t)1ULL);
v___x_898_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1);
v___x_899_ = lean_usize_land(v_x_891_, v___x_898_);
v_j_900_ = lean_usize_to_nat(v___x_899_);
v___x_901_ = lean_array_get_size(v_es_895_);
v___x_902_ = lean_nat_dec_lt(v_j_900_, v___x_901_);
if (v___x_902_ == 0)
{
lean_dec(v_j_900_);
lean_dec(v_x_894_);
lean_dec_ref(v_x_893_);
return v_x_890_;
}
else
{
lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_939_; 
lean_inc_ref(v_es_895_);
v_isSharedCheck_939_ = !lean_is_exclusive(v_x_890_);
if (v_isSharedCheck_939_ == 0)
{
lean_object* v_unused_940_; 
v_unused_940_ = lean_ctor_get(v_x_890_, 0);
lean_dec(v_unused_940_);
v___x_904_ = v_x_890_;
v_isShared_905_ = v_isSharedCheck_939_;
goto v_resetjp_903_;
}
else
{
lean_dec(v_x_890_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_939_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v_v_906_; lean_object* v___x_907_; lean_object* v_xs_x27_908_; lean_object* v___y_910_; 
v_v_906_ = lean_array_fget(v_es_895_, v_j_900_);
v___x_907_ = lean_box(0);
v_xs_x27_908_ = lean_array_fset(v_es_895_, v_j_900_, v___x_907_);
switch(lean_obj_tag(v_v_906_))
{
case 0:
{
lean_object* v_key_915_; lean_object* v_val_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_926_; 
v_key_915_ = lean_ctor_get(v_v_906_, 0);
v_val_916_ = lean_ctor_get(v_v_906_, 1);
v_isSharedCheck_926_ = !lean_is_exclusive(v_v_906_);
if (v_isSharedCheck_926_ == 0)
{
v___x_918_ = v_v_906_;
v_isShared_919_ = v_isSharedCheck_926_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_val_916_);
lean_inc(v_key_915_);
lean_dec(v_v_906_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_926_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
uint8_t v___x_920_; 
v___x_920_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_893_, v_key_915_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; lean_object* v___x_922_; 
lean_del_object(v___x_918_);
v___x_921_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_915_, v_val_916_, v_x_893_, v_x_894_);
v___x_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_922_, 0, v___x_921_);
v___y_910_ = v___x_922_;
goto v___jp_909_;
}
else
{
lean_object* v___x_924_; 
lean_dec(v_val_916_);
lean_dec(v_key_915_);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 1, v_x_894_);
lean_ctor_set(v___x_918_, 0, v_x_893_);
v___x_924_ = v___x_918_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_x_893_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v_x_894_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
v___y_910_ = v___x_924_;
goto v___jp_909_;
}
}
}
}
case 1:
{
lean_object* v_node_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_937_; 
v_node_927_ = lean_ctor_get(v_v_906_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v_v_906_);
if (v_isSharedCheck_937_ == 0)
{
v___x_929_ = v_v_906_;
v_isShared_930_ = v_isSharedCheck_937_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_node_927_);
lean_dec(v_v_906_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_937_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
size_t v___x_931_; size_t v___x_932_; lean_object* v___x_933_; lean_object* v___x_935_; 
v___x_931_ = lean_usize_shift_right(v_x_891_, v___x_896_);
v___x_932_ = lean_usize_add(v_x_892_, v___x_897_);
v___x_933_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_node_927_, v___x_931_, v___x_932_, v_x_893_, v_x_894_);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 0, v___x_933_);
v___x_935_ = v___x_929_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v___x_933_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
v___y_910_ = v___x_935_;
goto v___jp_909_;
}
}
}
default: 
{
lean_object* v___x_938_; 
v___x_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_938_, 0, v_x_893_);
lean_ctor_set(v___x_938_, 1, v_x_894_);
v___y_910_ = v___x_938_;
goto v___jp_909_;
}
}
v___jp_909_:
{
lean_object* v___x_911_; lean_object* v___x_913_; 
v___x_911_ = lean_array_fset(v_xs_x27_908_, v_j_900_, v___y_910_);
lean_dec(v_j_900_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 0, v___x_911_);
v___x_913_ = v___x_904_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_911_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
}
else
{
lean_object* v_ks_941_; lean_object* v_vs_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_962_; 
v_ks_941_ = lean_ctor_get(v_x_890_, 0);
v_vs_942_ = lean_ctor_get(v_x_890_, 1);
v_isSharedCheck_962_ = !lean_is_exclusive(v_x_890_);
if (v_isSharedCheck_962_ == 0)
{
v___x_944_ = v_x_890_;
v_isShared_945_ = v_isSharedCheck_962_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_vs_942_);
lean_inc(v_ks_941_);
lean_dec(v_x_890_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_962_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_ks_941_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v_vs_942_);
v___x_947_ = v_reuseFailAlloc_961_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
lean_object* v_newNode_948_; uint8_t v___y_950_; size_t v___x_956_; uint8_t v___x_957_; 
v_newNode_948_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4___redArg(v___x_947_, v_x_893_, v_x_894_);
v___x_956_ = ((size_t)7ULL);
v___x_957_ = lean_usize_dec_le(v___x_956_, v_x_892_);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; lean_object* v___x_959_; uint8_t v___x_960_; 
v___x_958_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_948_);
v___x_959_ = lean_unsigned_to_nat(4u);
v___x_960_ = lean_nat_dec_lt(v___x_958_, v___x_959_);
lean_dec(v___x_958_);
v___y_950_ = v___x_960_;
goto v___jp_949_;
}
else
{
v___y_950_ = v___x_957_;
goto v___jp_949_;
}
v___jp_949_:
{
if (v___y_950_ == 0)
{
lean_object* v_ks_951_; lean_object* v_vs_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v_ks_951_ = lean_ctor_get(v_newNode_948_, 0);
lean_inc_ref(v_ks_951_);
v_vs_952_ = lean_ctor_get(v_newNode_948_, 1);
lean_inc_ref(v_vs_952_);
lean_dec_ref(v_newNode_948_);
v___x_953_ = lean_unsigned_to_nat(0u);
v___x_954_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg___closed__0);
v___x_955_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(v_x_892_, v_ks_951_, v_vs_952_, v___x_953_, v___x_954_);
lean_dec_ref(v_vs_952_);
lean_dec_ref(v_ks_951_);
return v___x_955_;
}
else
{
return v_newNode_948_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(size_t v_depth_963_, lean_object* v_keys_964_, lean_object* v_vals_965_, lean_object* v_i_966_, lean_object* v_entries_967_){
_start:
{
lean_object* v___x_968_; uint8_t v___x_969_; 
v___x_968_ = lean_array_get_size(v_keys_964_);
v___x_969_ = lean_nat_dec_lt(v_i_966_, v___x_968_);
if (v___x_969_ == 0)
{
lean_dec(v_i_966_);
return v_entries_967_;
}
else
{
lean_object* v_k_970_; lean_object* v_v_971_; uint64_t v___x_972_; size_t v_h_973_; size_t v___x_974_; lean_object* v___x_975_; size_t v___x_976_; size_t v___x_977_; size_t v___x_978_; size_t v_h_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v_k_970_ = lean_array_fget_borrowed(v_keys_964_, v_i_966_);
v_v_971_ = lean_array_fget_borrowed(v_vals_965_, v_i_966_);
v___x_972_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_970_);
v_h_973_ = lean_uint64_to_usize(v___x_972_);
v___x_974_ = ((size_t)5ULL);
v___x_975_ = lean_unsigned_to_nat(1u);
v___x_976_ = ((size_t)1ULL);
v___x_977_ = lean_usize_sub(v_depth_963_, v___x_976_);
v___x_978_ = lean_usize_mul(v___x_974_, v___x_977_);
v_h_979_ = lean_usize_shift_right(v_h_973_, v___x_978_);
v___x_980_ = lean_nat_add(v_i_966_, v___x_975_);
lean_dec(v_i_966_);
lean_inc(v_v_971_);
lean_inc(v_k_970_);
v___x_981_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_entries_967_, v_h_979_, v_depth_963_, v_k_970_, v_v_971_);
v_i_966_ = v___x_980_;
v_entries_967_ = v___x_981_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_983_, lean_object* v_keys_984_, lean_object* v_vals_985_, lean_object* v_i_986_, lean_object* v_entries_987_){
_start:
{
size_t v_depth_boxed_988_; lean_object* v_res_989_; 
v_depth_boxed_988_ = lean_unbox_usize(v_depth_983_);
lean_dec(v_depth_983_);
v_res_989_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(v_depth_boxed_988_, v_keys_984_, v_vals_985_, v_i_986_, v_entries_987_);
lean_dec_ref(v_vals_985_);
lean_dec_ref(v_keys_984_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg___boxed(lean_object* v_x_990_, lean_object* v_x_991_, lean_object* v_x_992_, lean_object* v_x_993_, lean_object* v_x_994_){
_start:
{
size_t v_x_34214__boxed_995_; size_t v_x_34215__boxed_996_; lean_object* v_res_997_; 
v_x_34214__boxed_995_ = lean_unbox_usize(v_x_991_);
lean_dec(v_x_991_);
v_x_34215__boxed_996_ = lean_unbox_usize(v_x_992_);
lean_dec(v_x_992_);
v_res_997_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_x_990_, v_x_34214__boxed_995_, v_x_34215__boxed_996_, v_x_993_, v_x_994_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg(lean_object* v_x_998_, lean_object* v_x_999_, lean_object* v_x_1000_){
_start:
{
uint64_t v___x_1001_; size_t v___x_1002_; size_t v___x_1003_; lean_object* v___x_1004_; 
v___x_1001_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_999_);
v___x_1002_ = lean_uint64_to_usize(v___x_1001_);
v___x_1003_ = ((size_t)1ULL);
v___x_1004_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_x_998_, v___x_1002_, v___x_1003_, v_x_999_, v_x_1000_);
return v___x_1004_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1005_ = lean_unsigned_to_nat(32u);
v___x_1006_ = lean_mk_empty_array_with_capacity(v___x_1005_);
v___x_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
return v___x_1007_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1(void){
_start:
{
size_t v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1008_ = ((size_t)5ULL);
v___x_1009_ = lean_unsigned_to_nat(0u);
v___x_1010_ = lean_unsigned_to_nat(32u);
v___x_1011_ = lean_mk_empty_array_with_capacity(v___x_1010_);
v___x_1012_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0);
v___x_1013_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
lean_ctor_set(v___x_1013_, 1, v___x_1011_);
lean_ctor_set(v___x_1013_, 2, v___x_1009_);
lean_ctor_set(v___x_1013_, 3, v___x_1009_);
lean_ctor_set_usize(v___x_1013_, 4, v___x_1008_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0(lean_object* v_expr_1014_, lean_object* v_size_1015_, lean_object* v_s_1016_){
_start:
{
lean_object* v_vars_1017_; lean_object* v_varMap_1018_; lean_object* v_vars_x27_1019_; lean_object* v_varMap_x27_1020_; lean_object* v_natToIntMap_1021_; lean_object* v_natDef_1022_; lean_object* v_dvds_1023_; lean_object* v_lowers_1024_; lean_object* v_uppers_1025_; lean_object* v_diseqs_1026_; lean_object* v_elimEqs_1027_; lean_object* v_elimStack_1028_; lean_object* v_occurs_1029_; lean_object* v_assignment_1030_; lean_object* v_nextCnstrId_1031_; uint8_t v_caseSplits_1032_; lean_object* v_conflict_x3f_1033_; lean_object* v_diseqSplits_1034_; lean_object* v_divMod_1035_; lean_object* v_toIntIds_1036_; lean_object* v_toIntInfos_1037_; lean_object* v_toIntTermMap_1038_; lean_object* v_toIntVarMap_1039_; uint8_t v_usedCommRing_1040_; lean_object* v_nonlinearOccs_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1059_; 
v_vars_1017_ = lean_ctor_get(v_s_1016_, 0);
v_varMap_1018_ = lean_ctor_get(v_s_1016_, 1);
v_vars_x27_1019_ = lean_ctor_get(v_s_1016_, 2);
v_varMap_x27_1020_ = lean_ctor_get(v_s_1016_, 3);
v_natToIntMap_1021_ = lean_ctor_get(v_s_1016_, 4);
v_natDef_1022_ = lean_ctor_get(v_s_1016_, 5);
v_dvds_1023_ = lean_ctor_get(v_s_1016_, 6);
v_lowers_1024_ = lean_ctor_get(v_s_1016_, 7);
v_uppers_1025_ = lean_ctor_get(v_s_1016_, 8);
v_diseqs_1026_ = lean_ctor_get(v_s_1016_, 9);
v_elimEqs_1027_ = lean_ctor_get(v_s_1016_, 10);
v_elimStack_1028_ = lean_ctor_get(v_s_1016_, 11);
v_occurs_1029_ = lean_ctor_get(v_s_1016_, 12);
v_assignment_1030_ = lean_ctor_get(v_s_1016_, 13);
v_nextCnstrId_1031_ = lean_ctor_get(v_s_1016_, 14);
v_caseSplits_1032_ = lean_ctor_get_uint8(v_s_1016_, sizeof(void*)*23);
v_conflict_x3f_1033_ = lean_ctor_get(v_s_1016_, 15);
v_diseqSplits_1034_ = lean_ctor_get(v_s_1016_, 16);
v_divMod_1035_ = lean_ctor_get(v_s_1016_, 17);
v_toIntIds_1036_ = lean_ctor_get(v_s_1016_, 18);
v_toIntInfos_1037_ = lean_ctor_get(v_s_1016_, 19);
v_toIntTermMap_1038_ = lean_ctor_get(v_s_1016_, 20);
v_toIntVarMap_1039_ = lean_ctor_get(v_s_1016_, 21);
v_usedCommRing_1040_ = lean_ctor_get_uint8(v_s_1016_, sizeof(void*)*23 + 1);
v_nonlinearOccs_1041_ = lean_ctor_get(v_s_1016_, 22);
v_isSharedCheck_1059_ = !lean_is_exclusive(v_s_1016_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1043_ = v_s_1016_;
v_isShared_1044_ = v_isSharedCheck_1059_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_nonlinearOccs_1041_);
lean_inc(v_toIntVarMap_1039_);
lean_inc(v_toIntTermMap_1038_);
lean_inc(v_toIntInfos_1037_);
lean_inc(v_toIntIds_1036_);
lean_inc(v_divMod_1035_);
lean_inc(v_diseqSplits_1034_);
lean_inc(v_conflict_x3f_1033_);
lean_inc(v_nextCnstrId_1031_);
lean_inc(v_assignment_1030_);
lean_inc(v_occurs_1029_);
lean_inc(v_elimStack_1028_);
lean_inc(v_elimEqs_1027_);
lean_inc(v_diseqs_1026_);
lean_inc(v_uppers_1025_);
lean_inc(v_lowers_1024_);
lean_inc(v_dvds_1023_);
lean_inc(v_natDef_1022_);
lean_inc(v_natToIntMap_1021_);
lean_inc(v_varMap_x27_1020_);
lean_inc(v_vars_x27_1019_);
lean_inc(v_varMap_1018_);
lean_inc(v_vars_1017_);
lean_dec(v_s_1016_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1059_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1057_; 
lean_inc_ref(v_expr_1014_);
v___x_1045_ = l_Lean_PersistentArray_push___redArg(v_vars_1017_, v_expr_1014_);
v___x_1046_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg(v_varMap_1018_, v_expr_1014_, v_size_1015_);
v___x_1047_ = lean_box(0);
v___x_1048_ = l_Lean_PersistentArray_push___redArg(v_dvds_1023_, v___x_1047_);
v___x_1049_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1);
v___x_1050_ = l_Lean_PersistentArray_push___redArg(v_lowers_1024_, v___x_1049_);
v___x_1051_ = l_Lean_PersistentArray_push___redArg(v_uppers_1025_, v___x_1049_);
v___x_1052_ = l_Lean_PersistentArray_push___redArg(v_diseqs_1026_, v___x_1049_);
v___x_1053_ = l_Lean_PersistentArray_push___redArg(v_elimEqs_1027_, v___x_1047_);
v___x_1054_ = lean_box(1);
v___x_1055_ = l_Lean_PersistentArray_push___redArg(v_occurs_1029_, v___x_1054_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 12, v___x_1055_);
lean_ctor_set(v___x_1043_, 10, v___x_1053_);
lean_ctor_set(v___x_1043_, 9, v___x_1052_);
lean_ctor_set(v___x_1043_, 8, v___x_1051_);
lean_ctor_set(v___x_1043_, 7, v___x_1050_);
lean_ctor_set(v___x_1043_, 6, v___x_1048_);
lean_ctor_set(v___x_1043_, 1, v___x_1046_);
lean_ctor_set(v___x_1043_, 0, v___x_1045_);
v___x_1057_ = v___x_1043_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v___x_1046_);
lean_ctor_set(v_reuseFailAlloc_1058_, 2, v_vars_x27_1019_);
lean_ctor_set(v_reuseFailAlloc_1058_, 3, v_varMap_x27_1020_);
lean_ctor_set(v_reuseFailAlloc_1058_, 4, v_natToIntMap_1021_);
lean_ctor_set(v_reuseFailAlloc_1058_, 5, v_natDef_1022_);
lean_ctor_set(v_reuseFailAlloc_1058_, 6, v___x_1048_);
lean_ctor_set(v_reuseFailAlloc_1058_, 7, v___x_1050_);
lean_ctor_set(v_reuseFailAlloc_1058_, 8, v___x_1051_);
lean_ctor_set(v_reuseFailAlloc_1058_, 9, v___x_1052_);
lean_ctor_set(v_reuseFailAlloc_1058_, 10, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1058_, 11, v_elimStack_1028_);
lean_ctor_set(v_reuseFailAlloc_1058_, 12, v___x_1055_);
lean_ctor_set(v_reuseFailAlloc_1058_, 13, v_assignment_1030_);
lean_ctor_set(v_reuseFailAlloc_1058_, 14, v_nextCnstrId_1031_);
lean_ctor_set(v_reuseFailAlloc_1058_, 15, v_conflict_x3f_1033_);
lean_ctor_set(v_reuseFailAlloc_1058_, 16, v_diseqSplits_1034_);
lean_ctor_set(v_reuseFailAlloc_1058_, 17, v_divMod_1035_);
lean_ctor_set(v_reuseFailAlloc_1058_, 18, v_toIntIds_1036_);
lean_ctor_set(v_reuseFailAlloc_1058_, 19, v_toIntInfos_1037_);
lean_ctor_set(v_reuseFailAlloc_1058_, 20, v_toIntTermMap_1038_);
lean_ctor_set(v_reuseFailAlloc_1058_, 21, v_toIntVarMap_1039_);
lean_ctor_set(v_reuseFailAlloc_1058_, 22, v_nonlinearOccs_1041_);
lean_ctor_set_uint8(v_reuseFailAlloc_1058_, sizeof(void*)*23, v_caseSplits_1032_);
lean_ctor_set_uint8(v_reuseFailAlloc_1058_, sizeof(void*)*23 + 1, v_usedCommRing_1040_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1060_, lean_object* v_vals_1061_, lean_object* v_i_1062_, lean_object* v_k_1063_){
_start:
{
lean_object* v___x_1064_; uint8_t v___x_1065_; 
v___x_1064_ = lean_array_get_size(v_keys_1060_);
v___x_1065_ = lean_nat_dec_lt(v_i_1062_, v___x_1064_);
if (v___x_1065_ == 0)
{
lean_object* v___x_1066_; 
lean_dec(v_i_1062_);
v___x_1066_ = lean_box(0);
return v___x_1066_;
}
else
{
lean_object* v_k_x27_1067_; uint8_t v___x_1068_; 
v_k_x27_1067_ = lean_array_fget_borrowed(v_keys_1060_, v_i_1062_);
v___x_1068_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_1063_, v_k_x27_1067_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = lean_unsigned_to_nat(1u);
v___x_1070_ = lean_nat_add(v_i_1062_, v___x_1069_);
lean_dec(v_i_1062_);
v_i_1062_ = v___x_1070_;
goto _start;
}
else
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = lean_array_fget_borrowed(v_vals_1061_, v_i_1062_);
lean_dec(v_i_1062_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(lean_object* v_x_1079_, size_t v_x_1080_, lean_object* v_x_1081_){
_start:
{
if (lean_obj_tag(v_x_1079_) == 0)
{
lean_object* v_es_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1103_; 
v_es_1082_ = lean_ctor_get(v_x_1079_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v_x_1079_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1084_ = v_x_1079_;
v_isShared_1085_ = v_isSharedCheck_1103_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_es_1082_);
lean_dec(v_x_1079_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1103_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1086_; size_t v___x_1087_; size_t v___x_1088_; size_t v___x_1089_; lean_object* v_j_1090_; lean_object* v___x_1091_; 
v___x_1086_ = lean_box(2);
v___x_1087_ = ((size_t)5ULL);
v___x_1088_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1);
v___x_1089_ = lean_usize_land(v_x_1080_, v___x_1088_);
v_j_1090_ = lean_usize_to_nat(v___x_1089_);
v___x_1091_ = lean_array_get(v___x_1086_, v_es_1082_, v_j_1090_);
lean_dec(v_j_1090_);
lean_dec_ref(v_es_1082_);
switch(lean_obj_tag(v___x_1091_))
{
case 0:
{
lean_object* v_key_1092_; lean_object* v_val_1093_; uint8_t v___x_1094_; 
v_key_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc(v_key_1092_);
v_val_1093_ = lean_ctor_get(v___x_1091_, 1);
lean_inc(v_val_1093_);
lean_dec_ref(v___x_1091_);
v___x_1094_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1081_, v_key_1092_);
lean_dec(v_key_1092_);
if (v___x_1094_ == 0)
{
lean_object* v___x_1095_; 
lean_dec(v_val_1093_);
lean_del_object(v___x_1084_);
v___x_1095_ = lean_box(0);
return v___x_1095_;
}
else
{
lean_object* v___x_1097_; 
if (v_isShared_1085_ == 0)
{
lean_ctor_set_tag(v___x_1084_, 1);
lean_ctor_set(v___x_1084_, 0, v_val_1093_);
v___x_1097_ = v___x_1084_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_val_1093_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
case 1:
{
lean_object* v_node_1099_; size_t v___x_1100_; 
lean_del_object(v___x_1084_);
v_node_1099_ = lean_ctor_get(v___x_1091_, 0);
lean_inc(v_node_1099_);
lean_dec_ref(v___x_1091_);
v___x_1100_ = lean_usize_shift_right(v_x_1080_, v___x_1087_);
v_x_1079_ = v_node_1099_;
v_x_1080_ = v___x_1100_;
goto _start;
}
default: 
{
lean_object* v___x_1102_; 
lean_del_object(v___x_1084_);
v___x_1102_ = lean_box(0);
return v___x_1102_;
}
}
}
}
else
{
lean_object* v_ks_1104_; lean_object* v_vs_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v_ks_1104_ = lean_ctor_get(v_x_1079_, 0);
lean_inc_ref(v_ks_1104_);
v_vs_1105_ = lean_ctor_get(v_x_1079_, 1);
lean_inc_ref(v_vs_1105_);
lean_dec_ref(v_x_1079_);
v___x_1106_ = lean_unsigned_to_nat(0u);
v___x_1107_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(v_ks_1104_, v_vs_1105_, v___x_1106_, v_x_1081_);
lean_dec_ref(v_vs_1105_);
lean_dec_ref(v_ks_1104_);
return v___x_1107_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg___boxed(lean_object* v_x_1108_, lean_object* v_x_1109_, lean_object* v_x_1110_){
_start:
{
size_t v_x_34473__boxed_1111_; lean_object* v_res_1112_; 
v_x_34473__boxed_1111_ = lean_unbox_usize(v_x_1109_);
lean_dec(v_x_1109_);
v_res_1112_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(v_x_1108_, v_x_34473__boxed_1111_, v_x_1110_);
lean_dec_ref(v_x_1110_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(lean_object* v_x_1113_, lean_object* v_x_1114_){
_start:
{
uint64_t v___x_1115_; size_t v___x_1116_; lean_object* v___x_1117_; 
v___x_1115_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1114_);
v___x_1116_ = lean_uint64_to_usize(v___x_1115_);
v___x_1117_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(v_x_1113_, v___x_1116_, v_x_1114_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg___boxed(lean_object* v_x_1118_, lean_object* v_x_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(v_x_1118_, v_x_1119_);
lean_dec_ref(v_x_1119_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4(lean_object* v_msgData_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v___x_1127_; lean_object* v_env_1128_; lean_object* v___x_1129_; lean_object* v_mctx_1130_; lean_object* v_lctx_1131_; lean_object* v_options_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1127_ = lean_st_ref_get(v___y_1125_);
v_env_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc_ref(v_env_1128_);
lean_dec(v___x_1127_);
v___x_1129_ = lean_st_ref_get(v___y_1123_);
v_mctx_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc_ref(v_mctx_1130_);
lean_dec(v___x_1129_);
v_lctx_1131_ = lean_ctor_get(v___y_1122_, 2);
v_options_1132_ = lean_ctor_get(v___y_1124_, 2);
lean_inc_ref(v_options_1132_);
lean_inc_ref(v_lctx_1131_);
v___x_1133_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1133_, 0, v_env_1128_);
lean_ctor_set(v___x_1133_, 1, v_mctx_1130_);
lean_ctor_set(v___x_1133_, 2, v_lctx_1131_);
lean_ctor_set(v___x_1133_, 3, v_options_1132_);
v___x_1134_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
lean_ctor_set(v___x_1134_, 1, v_msgData_1121_);
v___x_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4___boxed(lean_object* v_msgData_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4(v_msgData_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
return v_res_1142_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1143_; double v___x_1144_; 
v___x_1143_ = lean_unsigned_to_nat(0u);
v___x_1144_ = lean_float_of_nat(v___x_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(lean_object* v_cls_1148_, lean_object* v_msg_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v_ref_1155_; lean_object* v___x_1156_; lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1201_; 
v_ref_1155_ = lean_ctor_get(v___y_1152_, 5);
v___x_1156_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4(v_msg_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1159_ = v___x_1156_;
v_isShared_1160_ = v_isSharedCheck_1201_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1156_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1201_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1161_; lean_object* v_traceState_1162_; lean_object* v_env_1163_; lean_object* v_nextMacroScope_1164_; lean_object* v_ngen_1165_; lean_object* v_auxDeclNGen_1166_; lean_object* v_cache_1167_; lean_object* v_messages_1168_; lean_object* v_infoState_1169_; lean_object* v_snapshotTasks_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1200_; 
v___x_1161_ = lean_st_ref_take(v___y_1153_);
v_traceState_1162_ = lean_ctor_get(v___x_1161_, 4);
v_env_1163_ = lean_ctor_get(v___x_1161_, 0);
v_nextMacroScope_1164_ = lean_ctor_get(v___x_1161_, 1);
v_ngen_1165_ = lean_ctor_get(v___x_1161_, 2);
v_auxDeclNGen_1166_ = lean_ctor_get(v___x_1161_, 3);
v_cache_1167_ = lean_ctor_get(v___x_1161_, 5);
v_messages_1168_ = lean_ctor_get(v___x_1161_, 6);
v_infoState_1169_ = lean_ctor_get(v___x_1161_, 7);
v_snapshotTasks_1170_ = lean_ctor_get(v___x_1161_, 8);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1172_ = v___x_1161_;
v_isShared_1173_ = v_isSharedCheck_1200_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_snapshotTasks_1170_);
lean_inc(v_infoState_1169_);
lean_inc(v_messages_1168_);
lean_inc(v_cache_1167_);
lean_inc(v_traceState_1162_);
lean_inc(v_auxDeclNGen_1166_);
lean_inc(v_ngen_1165_);
lean_inc(v_nextMacroScope_1164_);
lean_inc(v_env_1163_);
lean_dec(v___x_1161_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1200_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
uint64_t v_tid_1174_; lean_object* v_traces_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1199_; 
v_tid_1174_ = lean_ctor_get_uint64(v_traceState_1162_, sizeof(void*)*1);
v_traces_1175_ = lean_ctor_get(v_traceState_1162_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v_traceState_1162_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1177_ = v_traceState_1162_;
v_isShared_1178_ = v_isSharedCheck_1199_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_traces_1175_);
lean_dec(v_traceState_1162_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1199_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1179_; double v___x_1180_; uint8_t v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1189_; 
v___x_1179_ = lean_box(0);
v___x_1180_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0);
v___x_1181_ = 0;
v___x_1182_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__1));
v___x_1183_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1183_, 0, v_cls_1148_);
lean_ctor_set(v___x_1183_, 1, v___x_1179_);
lean_ctor_set(v___x_1183_, 2, v___x_1182_);
lean_ctor_set_float(v___x_1183_, sizeof(void*)*3, v___x_1180_);
lean_ctor_set_float(v___x_1183_, sizeof(void*)*3 + 8, v___x_1180_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*3 + 16, v___x_1181_);
v___x_1184_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__2));
v___x_1185_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1183_);
lean_ctor_set(v___x_1185_, 1, v_a_1157_);
lean_ctor_set(v___x_1185_, 2, v___x_1184_);
lean_inc(v_ref_1155_);
v___x_1186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1186_, 0, v_ref_1155_);
lean_ctor_set(v___x_1186_, 1, v___x_1185_);
v___x_1187_ = l_Lean_PersistentArray_push___redArg(v_traces_1175_, v___x_1186_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v___x_1187_);
v___x_1189_ = v___x_1177_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1187_);
lean_ctor_set_uint64(v_reuseFailAlloc_1198_, sizeof(void*)*1, v_tid_1174_);
v___x_1189_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
lean_object* v___x_1191_; 
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 4, v___x_1189_);
v___x_1191_ = v___x_1172_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_env_1163_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v_nextMacroScope_1164_);
lean_ctor_set(v_reuseFailAlloc_1197_, 2, v_ngen_1165_);
lean_ctor_set(v_reuseFailAlloc_1197_, 3, v_auxDeclNGen_1166_);
lean_ctor_set(v_reuseFailAlloc_1197_, 4, v___x_1189_);
lean_ctor_set(v_reuseFailAlloc_1197_, 5, v_cache_1167_);
lean_ctor_set(v_reuseFailAlloc_1197_, 6, v_messages_1168_);
lean_ctor_set(v_reuseFailAlloc_1197_, 7, v_infoState_1169_);
lean_ctor_set(v_reuseFailAlloc_1197_, 8, v_snapshotTasks_1170_);
v___x_1191_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1195_; 
v___x_1192_ = lean_st_ref_set(v___y_1153_, v___x_1191_);
v___x_1193_ = lean_box(0);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v___x_1193_);
v___x_1195_ = v___x_1159_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v___x_1193_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___boxed(lean_object* v_cls_1202_, lean_object* v_msg_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(v_cls_1202_, v_msg_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
return v_res_1209_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7(void){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1222_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4));
v___x_1223_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__6));
v___x_1224_ = l_Lean_Name_append(v___x_1223_, v___x_1222_);
return v___x_1224_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9(void){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__8));
v___x_1227_ = l_Lean_stringToMessageData(v___x_1226_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* lean_grind_cutsat_mk_var(lean_object* v_expr_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_){
_start:
{
lean_object* v___x_1240_; 
v___x_1240_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1229_, v_a_1237_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1378_; 
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1243_ = v___x_1240_;
v_isShared_1244_ = v_isSharedCheck_1378_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1240_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1378_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v_varMap_1245_; lean_object* v___x_1246_; 
v_varMap_1245_ = lean_ctor_get(v_a_1241_, 1);
lean_inc_ref(v_varMap_1245_);
lean_dec(v_a_1241_);
v___x_1246_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(v_varMap_1245_, v_expr_1228_);
if (lean_obj_tag(v___x_1246_) == 1)
{
lean_object* v_val_1247_; lean_object* v___x_1249_; 
lean_dec(v_a_1238_);
lean_dec_ref(v_a_1237_);
lean_dec(v_a_1236_);
lean_dec_ref(v_a_1235_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
lean_dec(v_a_1232_);
lean_dec_ref(v_a_1231_);
lean_dec(v_a_1230_);
lean_dec(v_a_1229_);
lean_dec_ref(v_expr_1228_);
v_val_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_val_1247_);
lean_dec_ref(v___x_1246_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 0, v_val_1247_);
v___x_1249_ = v___x_1243_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_val_1247_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
else
{
lean_object* v___x_1251_; 
lean_dec(v___x_1246_);
lean_del_object(v___x_1243_);
v___x_1251_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1229_, v_a_1237_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v_a_1252_; lean_object* v_vars_1253_; lean_object* v_options_1254_; lean_object* v_size_1255_; lean_object* v_inheritedTraceOptions_1256_; uint8_t v_hasTrace_1257_; lean_object* v___f_1258_; lean_object* v___y_1260_; lean_object* v___y_1261_; lean_object* v___y_1262_; lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v___y_1265_; lean_object* v___y_1266_; lean_object* v___y_1267_; lean_object* v___y_1268_; lean_object* v___y_1269_; 
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_a_1252_);
lean_dec_ref(v___x_1251_);
v_vars_1253_ = lean_ctor_get(v_a_1252_, 0);
lean_inc_ref(v_vars_1253_);
lean_dec(v_a_1252_);
v_options_1254_ = lean_ctor_get(v_a_1237_, 2);
v_size_1255_ = lean_ctor_get(v_vars_1253_, 2);
lean_inc_n(v_size_1255_, 2);
lean_dec_ref(v_vars_1253_);
v_inheritedTraceOptions_1256_ = lean_ctor_get(v_a_1237_, 13);
v_hasTrace_1257_ = lean_ctor_get_uint8(v_options_1254_, sizeof(void*)*1);
lean_inc_ref(v_expr_1228_);
v___f_1258_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0), 3, 2);
lean_closure_set(v___f_1258_, 0, v_expr_1228_);
lean_closure_set(v___f_1258_, 1, v_size_1255_);
if (v_hasTrace_1257_ == 0)
{
v___y_1260_ = v_a_1229_;
v___y_1261_ = v_a_1230_;
v___y_1262_ = v_a_1231_;
v___y_1263_ = v_a_1232_;
v___y_1264_ = v_a_1233_;
v___y_1265_ = v_a_1234_;
v___y_1266_ = v_a_1235_;
v___y_1267_ = v_a_1236_;
v___y_1268_ = v_a_1237_;
v___y_1269_ = v_a_1238_;
goto v___jp_1259_;
}
else
{
lean_object* v___x_1351_; lean_object* v___x_1352_; uint8_t v___x_1353_; 
v___x_1351_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4));
v___x_1352_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7);
v___x_1353_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1256_, v_options_1254_, v___x_1352_);
if (v___x_1353_ == 0)
{
v___y_1260_ = v_a_1229_;
v___y_1261_ = v_a_1230_;
v___y_1262_ = v_a_1231_;
v___y_1263_ = v_a_1232_;
v___y_1264_ = v_a_1233_;
v___y_1265_ = v_a_1234_;
v___y_1266_ = v_a_1235_;
v___y_1267_ = v_a_1236_;
v___y_1268_ = v_a_1237_;
v___y_1269_ = v_a_1238_;
goto v___jp_1259_;
}
else
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
lean_inc_ref(v_expr_1228_);
v___x_1354_ = l_Lean_MessageData_ofExpr(v_expr_1228_);
v___x_1355_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9);
v___x_1356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1354_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
lean_inc(v_size_1255_);
v___x_1357_ = l_Nat_reprFast(v_size_1255_);
v___x_1358_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
v___x_1359_ = l_Lean_MessageData_ofFormat(v___x_1358_);
v___x_1360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1356_);
lean_ctor_set(v___x_1360_, 1, v___x_1359_);
v___x_1361_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(v___x_1351_, v___x_1360_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_dec_ref(v___x_1361_);
v___y_1260_ = v_a_1229_;
v___y_1261_ = v_a_1230_;
v___y_1262_ = v_a_1231_;
v___y_1263_ = v_a_1232_;
v___y_1264_ = v_a_1233_;
v___y_1265_ = v_a_1234_;
v___y_1266_ = v_a_1235_;
v___y_1267_ = v_a_1236_;
v___y_1268_ = v_a_1237_;
v___y_1269_ = v_a_1238_;
goto v___jp_1259_;
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
lean_dec_ref(v___f_1258_);
lean_dec(v_size_1255_);
lean_dec(v_a_1238_);
lean_dec_ref(v_a_1237_);
lean_dec(v_a_1236_);
lean_dec_ref(v_a_1235_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
lean_dec(v_a_1232_);
lean_dec_ref(v_a_1231_);
lean_dec(v_a_1230_);
lean_dec(v_a_1229_);
lean_dec_ref(v_expr_1228_);
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1361_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1361_);
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
}
v___jp_1259_:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1270_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_1271_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1270_, v___f_1258_, v___y_1260_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v___x_1272_; 
lean_dec_ref(v___x_1271_);
lean_inc_ref(v_expr_1228_);
v___x_1272_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_1270_, v_expr_1228_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v___x_1273_; 
lean_dec_ref(v___x_1272_);
lean_inc(v_size_1255_);
lean_inc_ref(v_expr_1228_);
v___x_1273_ = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(v_expr_1228_, v_size_1255_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v___x_1274_; 
lean_dec_ref(v___x_1273_);
lean_inc(v_size_1255_);
lean_inc_ref(v_expr_1228_);
v___x_1274_ = l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg(v_expr_1228_, v_size_1255_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v___x_1275_; 
lean_dec_ref(v___x_1274_);
lean_inc(v_size_1255_);
lean_inc_ref(v_expr_1228_);
v___x_1275_ = l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds(v_expr_1228_, v_size_1255_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v___x_1276_; 
lean_dec_ref(v___x_1275_);
lean_inc_ref(v_expr_1228_);
v___x_1276_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm(v_expr_1228_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1302_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1279_ = v___x_1276_;
v_isShared_1280_ = v_isSharedCheck_1302_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1276_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1302_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
uint8_t v___x_1281_; 
v___x_1281_ = lean_unbox(v_a_1277_);
lean_dec(v_a_1277_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1283_; 
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v_expr_1228_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 0, v_size_1255_);
v___x_1283_ = v___x_1279_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_size_1255_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
else
{
lean_object* v___x_1285_; 
lean_del_object(v___x_1279_);
lean_inc(v_size_1255_);
v___x_1285_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt(v_expr_1228_, v_size_1255_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec(v___y_1261_);
lean_dec(v___y_1260_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1292_ == 0)
{
lean_object* v_unused_1293_; 
v_unused_1293_ = lean_ctor_get(v___x_1285_, 0);
lean_dec(v_unused_1293_);
v___x_1287_ = v___x_1285_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_dec(v___x_1285_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 0, v_size_1255_);
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_size_1255_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
lean_dec(v_size_1255_);
v_a_1294_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1285_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1285_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
}
}
else
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec(v_size_1255_);
lean_dec_ref(v_expr_1228_);
v_a_1303_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v___x_1276_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1276_);
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
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec(v_size_1255_);
lean_dec_ref(v_expr_1228_);
v_a_1311_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v___x_1275_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1275_);
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
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec(v_size_1255_);
lean_dec_ref(v_expr_1228_);
v_a_1319_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1274_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1274_);
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
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec(v_size_1255_);
lean_dec_ref(v_expr_1228_);
v_a_1327_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1273_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1273_);
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
else
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1342_; 
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec(v_size_1255_);
lean_dec_ref(v_expr_1228_);
v_a_1335_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1337_ = v___x_1272_;
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1272_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1338_ == 0)
{
v___x_1340_ = v___x_1337_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1335_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec(v_size_1255_);
lean_dec_ref(v_expr_1228_);
v_a_1343_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1345_ = v___x_1271_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1271_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1343_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec(v_a_1238_);
lean_dec_ref(v_a_1237_);
lean_dec(v_a_1236_);
lean_dec_ref(v_a_1235_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
lean_dec(v_a_1232_);
lean_dec_ref(v_a_1231_);
lean_dec(v_a_1230_);
lean_dec(v_a_1229_);
lean_dec_ref(v_expr_1228_);
v_a_1370_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1251_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1251_);
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
}
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
lean_dec(v_a_1238_);
lean_dec_ref(v_a_1237_);
lean_dec(v_a_1236_);
lean_dec_ref(v_a_1235_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
lean_dec(v_a_1232_);
lean_dec_ref(v_a_1231_);
lean_dec(v_a_1230_);
lean_dec(v_a_1229_);
lean_dec_ref(v_expr_1228_);
v_a_1379_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v___x_1240_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1240_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1382_ == 0)
{
v___x_1384_ = v___x_1381_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_a_1379_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___boxed(lean_object* v_expr_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = lean_grind_cutsat_mk_var(v_expr_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0(lean_object* v_00_u03b2_1400_, lean_object* v_x_1401_, lean_object* v_x_1402_){
_start:
{
lean_object* v___x_1403_; 
v___x_1403_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(v_x_1401_, v_x_1402_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___boxed(lean_object* v_00_u03b2_1404_, lean_object* v_x_1405_, lean_object* v_x_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0(v_00_u03b2_1404_, v_x_1405_, v_x_1406_);
lean_dec_ref(v_x_1406_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1(lean_object* v_00_u03b2_1408_, lean_object* v_x_1409_, lean_object* v_x_1410_, lean_object* v_x_1411_){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg(v_x_1409_, v_x_1410_, v_x_1411_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2(lean_object* v_cls_1413_, lean_object* v_msg_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v___x_1426_; 
v___x_1426_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(v_cls_1413_, v_msg_1414_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
return v___x_1426_;
}
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0(lean_object* v_00_u03b2_1441_, lean_object* v_x_1442_, size_t v_x_1443_, lean_object* v_x_1444_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(v_x_1442_, v_x_1443_, v_x_1444_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1446_, lean_object* v_x_1447_, lean_object* v_x_1448_, lean_object* v_x_1449_){
_start:
{
size_t v_x_35069__boxed_1450_; lean_object* v_res_1451_; 
v_x_35069__boxed_1450_ = lean_unbox_usize(v_x_1448_);
lean_dec(v_x_1448_);
v_res_1451_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0(v_00_u03b2_1446_, v_x_1447_, v_x_35069__boxed_1450_, v_x_1449_);
lean_dec_ref(v_x_1449_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2(lean_object* v_00_u03b2_1452_, lean_object* v_x_1453_, size_t v_x_1454_, size_t v_x_1455_, lean_object* v_x_1456_, lean_object* v_x_1457_){
_start:
{
lean_object* v___x_1458_; 
v___x_1458_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_x_1453_, v_x_1454_, v_x_1455_, v_x_1456_, v_x_1457_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1459_, lean_object* v_x_1460_, lean_object* v_x_1461_, lean_object* v_x_1462_, lean_object* v_x_1463_, lean_object* v_x_1464_){
_start:
{
size_t v_x_35080__boxed_1465_; size_t v_x_35081__boxed_1466_; lean_object* v_res_1467_; 
v_x_35080__boxed_1465_ = lean_unbox_usize(v_x_1461_);
lean_dec(v_x_1461_);
v_x_35081__boxed_1466_ = lean_unbox_usize(v_x_1462_);
lean_dec(v_x_1462_);
v_res_1467_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2(v_00_u03b2_1459_, v_x_1460_, v_x_35080__boxed_1465_, v_x_35081__boxed_1466_, v_x_1463_, v_x_1464_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1468_, lean_object* v_keys_1469_, lean_object* v_vals_1470_, lean_object* v_heq_1471_, lean_object* v_i_1472_, lean_object* v_k_1473_){
_start:
{
lean_object* v___x_1474_; 
v___x_1474_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(v_keys_1469_, v_vals_1470_, v_i_1472_, v_k_1473_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1475_, lean_object* v_keys_1476_, lean_object* v_vals_1477_, lean_object* v_heq_1478_, lean_object* v_i_1479_, lean_object* v_k_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1(v_00_u03b2_1475_, v_keys_1476_, v_vals_1477_, v_heq_1478_, v_i_1479_, v_k_1480_);
lean_dec_ref(v_k_1480_);
lean_dec_ref(v_vals_1477_);
lean_dec_ref(v_keys_1476_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1482_, lean_object* v_n_1483_, lean_object* v_k_1484_, lean_object* v_v_1485_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4___redArg(v_n_1483_, v_k_1484_, v_v_1485_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1487_, size_t v_depth_1488_, lean_object* v_keys_1489_, lean_object* v_vals_1490_, lean_object* v_heq_1491_, lean_object* v_i_1492_, lean_object* v_entries_1493_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(v_depth_1488_, v_keys_1489_, v_vals_1490_, v_i_1492_, v_entries_1493_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1495_, lean_object* v_depth_1496_, lean_object* v_keys_1497_, lean_object* v_vals_1498_, lean_object* v_heq_1499_, lean_object* v_i_1500_, lean_object* v_entries_1501_){
_start:
{
size_t v_depth_boxed_1502_; lean_object* v_res_1503_; 
v_depth_boxed_1502_ = lean_unbox_usize(v_depth_1496_);
lean_dec(v_depth_1496_);
v_res_1503_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5(v_00_u03b2_1495_, v_depth_boxed_1502_, v_keys_1497_, v_vals_1498_, v_heq_1499_, v_i_1500_, v_entries_1501_);
lean_dec_ref(v_vals_1498_);
lean_dec_ref(v_keys_1497_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_1504_, lean_object* v_x_1505_, lean_object* v_x_1506_, lean_object* v_x_1507_, lean_object* v_x_1508_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7___redArg(v_x_1505_, v_x_1506_, v_x_1507_, v_x_1508_);
return v___x_1509_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2(void){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1513_ = lean_box(0);
v___x_1514_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__1));
v___x_1515_ = l_Lean_mkConst(v___x_1514_, v___x_1513_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(lean_object* v_e_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v___x_1522_; 
lean_inc(v_a_1520_);
lean_inc_ref(v_a_1519_);
lean_inc(v_a_1518_);
lean_inc_ref(v_a_1517_);
v___x_1522_ = lean_infer_type(v_e_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1523_);
lean_dec_ref(v___x_1522_);
v___x_1524_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2);
v___x_1525_ = l_Lean_Meta_isExprDefEq(v_a_1523_, v___x_1524_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
return v___x_1525_;
}
else
{
lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1533_; 
v_a_1526_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1528_ = v___x_1522_;
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_a_1526_);
lean_dec(v___x_1522_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1531_; 
if (v_isShared_1529_ == 0)
{
v___x_1531_ = v___x_1528_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_a_1526_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___boxed(lean_object* v_e_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(v_e_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_);
lean_dec(v_a_1538_);
lean_dec_ref(v_a_1537_);
lean_dec(v_a_1536_);
lean_dec_ref(v_a_1535_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt(lean_object* v_e_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_){
_start:
{
lean_object* v___x_1553_; 
v___x_1553_ = l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(v_e_1541_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___boxed(lean_object* v_e_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Lean_Meta_Grind_Arith_Cutsat_isInt(v_e_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_);
lean_dec(v_a_1564_);
lean_dec_ref(v_a_1563_);
lean_dec(v_a_1562_);
lean_dec_ref(v_a_1561_);
lean_dec(v_a_1560_);
lean_dec_ref(v_a_1559_);
lean_dec(v_a_1558_);
lean_dec_ref(v_a_1557_);
lean_dec(v_a_1556_);
lean_dec(v_a_1555_);
return v_res_1566_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4(void){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__3));
v___x_1574_ = l_Lean_stringToMessageData(v___x_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(lean_object* v_e_1575_, uint8_t v_report_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_){
_start:
{
lean_object* v___x_1587_; 
lean_inc_ref(v_e_1575_);
v___x_1587_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1575_, v_a_1580_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1658_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1590_ = v___x_1587_;
v_isShared_1591_ = v_isSharedCheck_1658_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1587_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1658_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1597_; uint8_t v___x_1598_; 
v___x_1597_ = l_Lean_Expr_cleanupAnnotations(v_a_1588_);
v___x_1598_ = l_Lean_Expr_isApp(v___x_1597_);
if (v___x_1598_ == 0)
{
lean_dec_ref(v___x_1597_);
lean_dec_ref(v_e_1575_);
goto v___jp_1592_;
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
lean_dec_ref(v_e_1575_);
goto v___jp_1592_;
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
lean_dec_ref(v_e_1575_);
goto v___jp_1592_;
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
lean_dec_ref(v_e_1575_);
goto v___jp_1592_;
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
lean_dec_ref(v_e_1575_);
goto v___jp_1592_;
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
lean_dec_ref(v_e_1575_);
goto v___jp_1592_;
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
lean_dec_ref(v_e_1575_);
goto v___jp_1592_;
}
else
{
lean_object* v___x_1615_; 
lean_del_object(v___x_1590_);
v___x_1615_ = l_Lean_Meta_Structural_isInstHAddInt___redArg(v_arg_1605_, v_a_1580_);
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
if (v_report_1576_ == 0)
{
lean_dec_ref(v_e_1575_);
goto v___jp_1584_;
}
else
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1577_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_a_1622_; uint8_t v___x_1623_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_a_1622_);
lean_dec_ref(v___x_1621_);
v___x_1623_ = lean_unbox(v_a_1622_);
lean_dec(v_a_1622_);
if (v___x_1623_ == 0)
{
lean_dec_ref(v_e_1575_);
goto v___jp_1584_;
}
else
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1624_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4);
v___x_1625_ = l_Lean_indentExpr(v_e_1575_);
v___x_1626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1624_);
lean_ctor_set(v___x_1626_, 1, v___x_1625_);
v___x_1627_ = l_Lean_Meta_Sym_reportIssue(v___x_1626_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_dec_ref(v___x_1627_);
goto v___jp_1584_;
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
lean_dec_ref(v_e_1575_);
v_a_1636_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1621_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1621_);
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
lean_dec_ref(v_e_1575_);
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
lean_dec_ref(v_e_1575_);
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
v___jp_1592_:
{
lean_object* v___x_1593_; lean_object* v___x_1595_; 
v___x_1593_ = lean_box(0);
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 0, v___x_1593_);
v___x_1595_ = v___x_1590_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1593_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
}
else
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1666_; 
lean_dec_ref(v_e_1575_);
v_a_1659_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1661_ = v___x_1587_;
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1587_);
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
v___jp_1584_:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = lean_box(0);
v___x_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1585_);
return v___x_1586_;
}
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f(lean_object* v_e_1678_, uint8_t v_report_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_){
_start:
{
lean_object* v___x_1691_; 
v___x_1691_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_1678_, v_report_1679_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___boxed(lean_object* v_e_1692_, lean_object* v_report_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_){
_start:
{
uint8_t v_report_boxed_1705_; lean_object* v_res_1706_; 
v_report_boxed_1705_ = lean_unbox(v_report_1693_);
v_res_1706_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f(v_e_1692_, v_report_boxed_1705_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_);
lean_dec(v_a_1703_);
lean_dec_ref(v_a_1702_);
lean_dec(v_a_1701_);
lean_dec_ref(v_a_1700_);
lean_dec(v_a_1699_);
lean_dec_ref(v_a_1698_);
lean_dec(v_a_1697_);
lean_dec_ref(v_a_1696_);
lean_dec(v_a_1695_);
lean_dec(v_a_1694_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(lean_object* v_e_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_){
_start:
{
uint8_t v___x_1715_; lean_object* v___x_1716_; 
v___x_1715_ = 0;
v___x_1716_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_1707_, v___x_1715_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1730_; 
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1719_ = v___x_1716_;
v_isShared_1720_ = v_isSharedCheck_1730_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1716_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1730_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
if (lean_obj_tag(v_a_1717_) == 0)
{
lean_object* v___x_1721_; lean_object* v___x_1723_; 
v___x_1721_ = lean_box(v___x_1715_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 0, v___x_1721_);
v___x_1723_ = v___x_1719_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1721_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
else
{
uint8_t v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1728_; 
lean_dec_ref(v_a_1717_);
v___x_1725_ = 1;
v___x_1726_ = lean_box(v___x_1725_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 0, v___x_1726_);
v___x_1728_ = v___x_1719_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1726_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
}
else
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1738_; 
v_a_1731_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1733_ = v___x_1716_;
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1716_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1736_; 
if (v_isShared_1734_ == 0)
{
v___x_1736_ = v___x_1733_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1731_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg___boxed(lean_object* v_e_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(v_e_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_);
lean_dec(v_a_1745_);
lean_dec_ref(v_a_1744_);
lean_dec(v_a_1743_);
lean_dec_ref(v_a_1742_);
lean_dec(v_a_1741_);
lean_dec_ref(v_a_1740_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd(lean_object* v_e_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(v_e_1748_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___boxed(lean_object* v_e_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd(v_e_1761_, v_a_1762_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_, v_a_1771_);
lean_dec(v_a_1771_);
lean_dec_ref(v_a_1770_);
lean_dec(v_a_1769_);
lean_dec_ref(v_a_1768_);
lean_dec(v_a_1767_);
lean_dec_ref(v_a_1766_);
lean_dec(v_a_1765_);
lean_dec_ref(v_a_1764_);
lean_dec(v_a_1763_);
lean_dec(v_a_1762_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(lean_object* v_e_1774_, uint8_t v_report_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_){
_start:
{
lean_object* v___x_1786_; 
lean_inc_ref(v_e_1774_);
v___x_1786_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1774_, v_a_1779_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1878_; 
v_a_1787_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1789_ = v___x_1786_;
v_isShared_1790_ = v_isSharedCheck_1878_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1786_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1878_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1796_; uint8_t v___x_1797_; 
v___x_1796_ = l_Lean_Expr_cleanupAnnotations(v_a_1787_);
v___x_1797_ = l_Lean_Expr_isApp(v___x_1796_);
if (v___x_1797_ == 0)
{
lean_dec_ref(v___x_1796_);
lean_dec_ref(v_e_1774_);
goto v___jp_1791_;
}
else
{
lean_object* v_arg_1798_; lean_object* v___x_1799_; uint8_t v___x_1800_; 
v_arg_1798_ = lean_ctor_get(v___x_1796_, 1);
lean_inc_ref(v_arg_1798_);
v___x_1799_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1796_);
v___x_1800_ = l_Lean_Expr_isApp(v___x_1799_);
if (v___x_1800_ == 0)
{
lean_dec_ref(v___x_1799_);
lean_dec_ref(v_arg_1798_);
lean_dec_ref(v_e_1774_);
goto v___jp_1791_;
}
else
{
lean_object* v_arg_1801_; lean_object* v___x_1802_; uint8_t v___x_1803_; 
v_arg_1801_ = lean_ctor_get(v___x_1799_, 1);
lean_inc_ref(v_arg_1801_);
v___x_1802_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1799_);
v___x_1803_ = l_Lean_Expr_isApp(v___x_1802_);
if (v___x_1803_ == 0)
{
lean_dec_ref(v___x_1802_);
lean_dec_ref(v_arg_1801_);
lean_dec_ref(v_arg_1798_);
lean_dec_ref(v_e_1774_);
goto v___jp_1791_;
}
else
{
lean_object* v_arg_1804_; lean_object* v___x_1805_; uint8_t v___x_1806_; 
v_arg_1804_ = lean_ctor_get(v___x_1802_, 1);
lean_inc_ref(v_arg_1804_);
v___x_1805_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1802_);
v___x_1806_ = l_Lean_Expr_isApp(v___x_1805_);
if (v___x_1806_ == 0)
{
lean_dec_ref(v___x_1805_);
lean_dec_ref(v_arg_1804_);
lean_dec_ref(v_arg_1801_);
lean_dec_ref(v_arg_1798_);
lean_dec_ref(v_e_1774_);
goto v___jp_1791_;
}
else
{
lean_object* v___x_1807_; uint8_t v___x_1808_; 
v___x_1807_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1805_);
v___x_1808_ = l_Lean_Expr_isApp(v___x_1807_);
if (v___x_1808_ == 0)
{
lean_dec_ref(v___x_1807_);
lean_dec_ref(v_arg_1804_);
lean_dec_ref(v_arg_1801_);
lean_dec_ref(v_arg_1798_);
lean_dec_ref(v_e_1774_);
goto v___jp_1791_;
}
else
{
lean_object* v___x_1809_; uint8_t v___x_1810_; 
v___x_1809_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1807_);
v___x_1810_ = l_Lean_Expr_isApp(v___x_1809_);
if (v___x_1810_ == 0)
{
lean_dec_ref(v___x_1809_);
lean_dec_ref(v_arg_1804_);
lean_dec_ref(v_arg_1801_);
lean_dec_ref(v_arg_1798_);
lean_dec_ref(v_e_1774_);
goto v___jp_1791_;
}
else
{
lean_object* v___x_1811_; lean_object* v___x_1812_; uint8_t v___x_1813_; 
v___x_1811_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1809_);
v___x_1812_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11));
v___x_1813_ = l_Lean_Expr_isConstOf(v___x_1811_, v___x_1812_);
lean_dec_ref(v___x_1811_);
if (v___x_1813_ == 0)
{
lean_dec_ref(v_arg_1804_);
lean_dec_ref(v_arg_1801_);
lean_dec_ref(v_arg_1798_);
lean_dec_ref(v_e_1774_);
goto v___jp_1791_;
}
else
{
lean_object* v___x_1814_; 
lean_del_object(v___x_1789_);
v___x_1814_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_1804_, v_a_1779_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; uint8_t v___x_1816_; 
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
lean_inc(v_a_1815_);
lean_dec_ref(v___x_1814_);
v___x_1816_ = lean_unbox(v_a_1815_);
lean_dec(v_a_1815_);
if (v___x_1816_ == 0)
{
lean_dec_ref(v_arg_1801_);
lean_dec_ref(v_arg_1798_);
if (v_report_1775_ == 0)
{
lean_dec_ref(v_e_1774_);
goto v___jp_1783_;
}
else
{
lean_object* v___x_1817_; 
v___x_1817_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1776_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v_a_1818_; uint8_t v___x_1819_; 
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
lean_inc(v_a_1818_);
lean_dec_ref(v___x_1817_);
v___x_1819_ = lean_unbox(v_a_1818_);
lean_dec(v_a_1818_);
if (v___x_1819_ == 0)
{
lean_dec_ref(v_e_1774_);
goto v___jp_1783_;
}
else
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1820_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4);
v___x_1821_ = l_Lean_indentExpr(v_e_1774_);
v___x_1822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1820_);
lean_ctor_set(v___x_1822_, 1, v___x_1821_);
v___x_1823_ = l_Lean_Meta_Sym_reportIssue(v___x_1822_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_);
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_dec_ref(v___x_1823_);
goto v___jp_1783_;
}
else
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1823_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1823_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
}
else
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1839_; 
lean_dec_ref(v_e_1774_);
v_a_1832_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1834_ = v___x_1817_;
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1817_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
if (v_isShared_1835_ == 0)
{
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1832_);
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
}
else
{
lean_object* v___x_1840_; 
lean_dec_ref(v_e_1774_);
v___x_1840_ = l_Lean_Meta_getIntValue_x3f(v_arg_1801_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1861_; 
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1843_ = v___x_1840_;
v_isShared_1844_ = v_isSharedCheck_1861_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1840_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1861_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
if (lean_obj_tag(v_a_1841_) == 1)
{
lean_object* v_val_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1856_; 
v_val_1845_ = lean_ctor_get(v_a_1841_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v_a_1841_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1847_ = v_a_1841_;
v_isShared_1848_ = v_isSharedCheck_1856_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_val_1845_);
lean_dec(v_a_1841_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1856_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1849_; lean_object* v___x_1851_; 
v___x_1849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1849_, 0, v_val_1845_);
lean_ctor_set(v___x_1849_, 1, v_arg_1798_);
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 0, v___x_1849_);
v___x_1851_ = v___x_1847_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1849_);
v___x_1851_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
lean_object* v___x_1853_; 
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 0, v___x_1851_);
v___x_1853_ = v___x_1843_;
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
lean_object* v___x_1857_; lean_object* v___x_1859_; 
lean_dec(v_a_1841_);
lean_dec_ref(v_arg_1798_);
v___x_1857_ = lean_box(0);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 0, v___x_1857_);
v___x_1859_ = v___x_1843_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v___x_1857_);
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
else
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
lean_dec_ref(v_arg_1798_);
v_a_1862_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1840_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1840_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
lean_dec_ref(v_arg_1801_);
lean_dec_ref(v_arg_1798_);
lean_dec_ref(v_e_1774_);
v_a_1870_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1814_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1814_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
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
v___jp_1791_:
{
lean_object* v___x_1792_; lean_object* v___x_1794_; 
v___x_1792_ = lean_box(0);
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 0, v___x_1792_);
v___x_1794_ = v___x_1789_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v___x_1792_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
else
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1886_; 
lean_dec_ref(v_e_1774_);
v_a_1879_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1881_ = v___x_1786_;
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1786_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1884_; 
if (v_isShared_1882_ == 0)
{
v___x_1884_ = v___x_1881_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_a_1879_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
}
}
}
v___jp_1783_:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1784_ = lean_box(0);
v___x_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1784_);
return v___x_1785_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg___boxed(lean_object* v_e_1887_, lean_object* v_report_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_){
_start:
{
uint8_t v_report_boxed_1896_; lean_object* v_res_1897_; 
v_report_boxed_1896_ = lean_unbox(v_report_1888_);
v_res_1897_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1887_, v_report_boxed_1896_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_);
lean_dec(v_a_1894_);
lean_dec_ref(v_a_1893_);
lean_dec(v_a_1892_);
lean_dec_ref(v_a_1891_);
lean_dec(v_a_1890_);
lean_dec_ref(v_a_1889_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f(lean_object* v_e_1898_, uint8_t v_report_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1898_, v_report_1899_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___boxed(lean_object* v_e_1912_, lean_object* v_report_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_){
_start:
{
uint8_t v_report_boxed_1925_; lean_object* v_res_1926_; 
v_report_boxed_1925_ = lean_unbox(v_report_1913_);
v_res_1926_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f(v_e_1912_, v_report_boxed_1925_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_);
lean_dec(v_a_1923_);
lean_dec_ref(v_a_1922_);
lean_dec(v_a_1921_);
lean_dec_ref(v_a_1920_);
lean_dec(v_a_1919_);
lean_dec_ref(v_a_1918_);
lean_dec(v_a_1917_);
lean_dec_ref(v_a_1916_);
lean_dec(v_a_1915_);
lean_dec(v_a_1914_);
return v_res_1926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(lean_object* v_e_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_){
_start:
{
uint8_t v___x_1935_; lean_object* v___x_1936_; 
v___x_1935_ = 0;
v___x_1936_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1927_, v___x_1935_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1950_; 
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1939_ = v___x_1936_;
v_isShared_1940_ = v_isSharedCheck_1950_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1936_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1950_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
if (lean_obj_tag(v_a_1937_) == 0)
{
lean_object* v___x_1941_; lean_object* v___x_1943_; 
v___x_1941_ = lean_box(v___x_1935_);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 0, v___x_1941_);
v___x_1943_ = v___x_1939_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v___x_1941_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
else
{
uint8_t v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1948_; 
lean_dec_ref(v_a_1937_);
v___x_1945_ = 1;
v___x_1946_ = lean_box(v___x_1945_);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 0, v___x_1946_);
v___x_1948_ = v___x_1939_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v___x_1946_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
else
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1958_; 
v_a_1951_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1953_ = v___x_1936_;
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1936_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1956_; 
if (v_isShared_1954_ == 0)
{
v___x_1956_ = v___x_1953_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_a_1951_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul(lean_object* v_e_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_){
_start:
{
lean_object* v___x_1980_; 
v___x_1980_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(v_e_1968_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_);
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___boxed(lean_object* v_e_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul(v_e_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_);
lean_dec(v_a_1991_);
lean_dec_ref(v_a_1990_);
lean_dec(v_a_1989_);
lean_dec_ref(v_a_1988_);
lean_dec(v_a_1987_);
lean_dec_ref(v_a_1986_);
lean_dec(v_a_1985_);
lean_dec_ref(v_a_1984_);
lean_dec(v_a_1983_);
lean_dec(v_a_1982_);
return v_res_1993_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0(void){
_start:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1994_ = lean_unsigned_to_nat(1u);
v___x_1995_ = lean_nat_to_int(v___x_1994_);
return v___x_1995_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2(void){
_start:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__1));
v___x_1998_ = l_Lean_stringToMessageData(v___x_1997_);
return v___x_1998_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4(void){
_start:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_2000_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__3));
v___x_2001_ = l_Lean_stringToMessageData(v___x_2000_);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(lean_object* v_e_2002_, lean_object* v_p_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_){
_start:
{
lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v___y_2021_; lean_object* v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; lean_object* v___y_2025_; uint8_t v___x_2045_; lean_object* v___x_2046_; 
v___x_2045_ = 1;
lean_inc_ref(v_e_2002_);
v___x_2046_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_2002_, v___x_2045_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_object* v_a_2047_; 
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc(v_a_2047_);
lean_dec_ref(v___x_2046_);
if (lean_obj_tag(v_a_2047_) == 1)
{
lean_object* v_val_2048_; lean_object* v_fst_2049_; lean_object* v_snd_2050_; lean_object* v___x_2051_; 
lean_dec_ref(v_e_2002_);
v_val_2048_ = lean_ctor_get(v_a_2047_, 0);
lean_inc(v_val_2048_);
lean_dec_ref(v_a_2047_);
v_fst_2049_ = lean_ctor_get(v_val_2048_, 0);
lean_inc(v_fst_2049_);
v_snd_2050_ = lean_ctor_get(v_val_2048_, 1);
lean_inc(v_snd_2050_);
lean_dec(v_val_2048_);
lean_inc(v_a_2013_);
lean_inc_ref(v_a_2012_);
lean_inc(v_a_2011_);
lean_inc_ref(v_a_2010_);
lean_inc(v_a_2009_);
lean_inc_ref(v_a_2008_);
lean_inc(v_a_2007_);
lean_inc_ref(v_a_2006_);
lean_inc(v_a_2005_);
lean_inc(v_a_2004_);
v___x_2051_ = lean_grind_cutsat_mk_var(v_snd_2050_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2060_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2054_ = v___x_2051_;
v_isShared_2055_ = v_isSharedCheck_2060_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2051_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2060_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2056_; lean_object* v___x_2058_; 
v___x_2056_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2056_, 0, v_fst_2049_);
lean_ctor_set(v___x_2056_, 1, v_a_2052_);
lean_ctor_set(v___x_2056_, 2, v_p_2003_);
if (v_isShared_2055_ == 0)
{
lean_ctor_set(v___x_2054_, 0, v___x_2056_);
v___x_2058_ = v___x_2054_;
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
lean_dec(v_fst_2049_);
lean_dec_ref(v_p_2003_);
v_a_2061_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_2051_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2051_);
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
lean_object* v___x_2069_; 
lean_dec(v_a_2047_);
lean_inc_ref(v_e_2002_);
v___x_2069_ = l_Lean_Meta_getIntValue_x3f(v_e_2002_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2111_; 
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2072_ = v___x_2069_;
v_isShared_2073_ = v_isSharedCheck_2111_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_2069_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2111_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
if (lean_obj_tag(v_a_2070_) == 1)
{
lean_object* v_val_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2110_; 
v_val_2074_ = lean_ctor_get(v_a_2070_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v_a_2070_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2076_ = v_a_2070_;
v_isShared_2077_ = v_isSharedCheck_2110_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_val_2074_);
lean_dec(v_a_2070_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2110_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
uint8_t v___x_2078_; 
v___x_2078_ = l_Int_Linear_Poly_isZero(v_p_2003_);
if (v___x_2078_ == 0)
{
lean_object* v___x_2079_; 
lean_del_object(v___x_2076_);
lean_dec(v_val_2074_);
lean_del_object(v___x_2072_);
v___x_2079_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_2008_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_a_2080_; uint8_t v___x_2081_; 
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
lean_inc(v_a_2080_);
lean_dec_ref(v___x_2079_);
v___x_2081_ = lean_unbox(v_a_2080_);
lean_dec(v_a_2080_);
if (v___x_2081_ == 0)
{
v___y_2016_ = v_a_2004_;
v___y_2017_ = v_a_2005_;
v___y_2018_ = v_a_2006_;
v___y_2019_ = v_a_2007_;
v___y_2020_ = v_a_2008_;
v___y_2021_ = v_a_2009_;
v___y_2022_ = v_a_2010_;
v___y_2023_ = v_a_2011_;
v___y_2024_ = v_a_2012_;
v___y_2025_ = v_a_2013_;
goto v___jp_2015_;
}
else
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2082_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2);
lean_inc_ref(v_e_2002_);
v___x_2083_ = l_Lean_indentExpr(v_e_2002_);
v___x_2084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2082_);
lean_ctor_set(v___x_2084_, 1, v___x_2083_);
v___x_2085_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4);
v___x_2086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2084_);
lean_ctor_set(v___x_2086_, 1, v___x_2085_);
v___x_2087_ = l_Lean_Meta_Sym_reportIssue(v___x_2086_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_dec_ref(v___x_2087_);
v___y_2016_ = v_a_2004_;
v___y_2017_ = v_a_2005_;
v___y_2018_ = v_a_2006_;
v___y_2019_ = v_a_2007_;
v___y_2020_ = v_a_2008_;
v___y_2021_ = v_a_2009_;
v___y_2022_ = v_a_2010_;
v___y_2023_ = v_a_2011_;
v___y_2024_ = v_a_2012_;
v___y_2025_ = v_a_2013_;
goto v___jp_2015_;
}
else
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2095_; 
lean_dec_ref(v_p_2003_);
lean_dec_ref(v_e_2002_);
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2090_ = v___x_2087_;
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2087_);
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
}
}
else
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
lean_dec_ref(v_p_2003_);
lean_dec_ref(v_e_2002_);
v_a_2096_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2098_ = v___x_2079_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2079_);
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
else
{
lean_object* v___x_2105_; 
lean_dec_ref(v_p_2003_);
lean_dec_ref(v_e_2002_);
if (v_isShared_2077_ == 0)
{
lean_ctor_set_tag(v___x_2076_, 0);
v___x_2105_ = v___x_2076_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_val_2074_);
v___x_2105_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
lean_object* v___x_2107_; 
if (v_isShared_2073_ == 0)
{
lean_ctor_set(v___x_2072_, 0, v___x_2105_);
v___x_2107_ = v___x_2072_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2105_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
}
else
{
lean_del_object(v___x_2072_);
lean_dec(v_a_2070_);
v___y_2016_ = v_a_2004_;
v___y_2017_ = v_a_2005_;
v___y_2018_ = v_a_2006_;
v___y_2019_ = v_a_2007_;
v___y_2020_ = v_a_2008_;
v___y_2021_ = v_a_2009_;
v___y_2022_ = v_a_2010_;
v___y_2023_ = v_a_2011_;
v___y_2024_ = v_a_2012_;
v___y_2025_ = v_a_2013_;
goto v___jp_2015_;
}
}
}
else
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
lean_dec_ref(v_p_2003_);
lean_dec_ref(v_e_2002_);
v_a_2112_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2069_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2069_);
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
lean_dec_ref(v_p_2003_);
lean_dec_ref(v_e_2002_);
v_a_2120_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2122_ = v___x_2046_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2046_);
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
v___jp_2015_:
{
lean_object* v___x_2026_; 
lean_inc(v___y_2025_);
lean_inc_ref(v___y_2024_);
lean_inc(v___y_2023_);
lean_inc_ref(v___y_2022_);
lean_inc(v___y_2021_);
lean_inc_ref(v___y_2020_);
lean_inc(v___y_2019_);
lean_inc_ref(v___y_2018_);
lean_inc(v___y_2017_);
lean_inc(v___y_2016_);
v___x_2026_ = lean_grind_cutsat_mk_var(v_e_2002_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2036_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2029_ = v___x_2026_;
v_isShared_2030_ = v_isSharedCheck_2036_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_2026_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2036_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2034_; 
v___x_2031_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0);
v___x_2032_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2031_);
lean_ctor_set(v___x_2032_, 1, v_a_2027_);
lean_ctor_set(v___x_2032_, 2, v_p_2003_);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 0, v___x_2032_);
v___x_2034_ = v___x_2029_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2032_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
else
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2044_; 
lean_dec_ref(v_p_2003_);
v_a_2037_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2039_ = v___x_2026_;
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_2026_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_a_2037_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___boxed(lean_object* v_e_2128_, lean_object* v_p_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_){
_start:
{
lean_object* v_res_2141_; 
v_res_2141_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_e_2128_, v_p_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_);
lean_dec(v_a_2139_);
lean_dec_ref(v_a_2138_);
lean_dec(v_a_2137_);
lean_dec_ref(v_a_2136_);
lean_dec(v_a_2135_);
lean_dec_ref(v_a_2134_);
lean_dec(v_a_2133_);
lean_dec_ref(v_a_2132_);
lean_dec(v_a_2131_);
lean_dec(v_a_2130_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go(lean_object* v_e_2142_, lean_object* v_p_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_){
_start:
{
uint8_t v___x_2155_; lean_object* v___x_2156_; 
v___x_2155_ = 1;
lean_inc_ref(v_e_2142_);
v___x_2156_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_2142_, v___x_2155_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_object* v_a_2157_; 
v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_a_2157_);
lean_dec_ref(v___x_2156_);
if (lean_obj_tag(v_a_2157_) == 1)
{
lean_object* v_val_2158_; lean_object* v_fst_2159_; lean_object* v_snd_2160_; lean_object* v___x_2161_; 
lean_dec_ref(v_e_2142_);
v_val_2158_ = lean_ctor_get(v_a_2157_, 0);
lean_inc(v_val_2158_);
lean_dec_ref(v_a_2157_);
v_fst_2159_ = lean_ctor_get(v_val_2158_, 0);
lean_inc(v_fst_2159_);
v_snd_2160_ = lean_ctor_get(v_val_2158_, 1);
lean_inc(v_snd_2160_);
lean_dec(v_val_2158_);
v___x_2161_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_snd_2160_, v_p_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_);
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_object* v_a_2162_; 
v_a_2162_ = lean_ctor_get(v___x_2161_, 0);
lean_inc(v_a_2162_);
lean_dec_ref(v___x_2161_);
v_e_2142_ = v_fst_2159_;
v_p_2143_ = v_a_2162_;
goto _start;
}
else
{
lean_dec(v_fst_2159_);
return v___x_2161_;
}
}
else
{
lean_object* v___x_2164_; 
lean_dec(v_a_2157_);
v___x_2164_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_e_2142_, v_p_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_);
return v___x_2164_;
}
}
else
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2172_; 
lean_dec_ref(v_p_2143_);
lean_dec_ref(v_e_2142_);
v_a_2165_ = lean_ctor_get(v___x_2156_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2167_ = v___x_2156_;
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2156_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2170_; 
if (v_isShared_2168_ == 0)
{
v___x_2170_ = v___x_2167_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2165_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go___boxed(lean_object* v_e_2173_, lean_object* v_p_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go(v_e_2173_, v_p_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_);
lean_dec(v_a_2184_);
lean_dec_ref(v_a_2183_);
lean_dec(v_a_2182_);
lean_dec_ref(v_a_2181_);
lean_dec(v_a_2180_);
lean_dec_ref(v_a_2179_);
lean_dec(v_a_2178_);
lean_dec_ref(v_a_2177_);
lean_dec(v_a_2176_);
lean_dec(v_a_2175_);
return v_res_2186_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0(void){
_start:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___x_2187_ = lean_unsigned_to_nat(0u);
v___x_2188_ = lean_nat_to_int(v___x_2187_);
return v___x_2188_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1(void){
_start:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2189_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0);
v___x_2190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2189_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly(lean_object* v_e_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_){
_start:
{
uint8_t v___x_2203_; lean_object* v___x_2204_; 
v___x_2203_ = 1;
lean_inc_ref(v_e_2191_);
v___x_2204_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_2191_, v___x_2203_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_a_2205_; 
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
lean_inc(v_a_2205_);
lean_dec_ref(v___x_2204_);
if (lean_obj_tag(v_a_2205_) == 1)
{
lean_object* v_val_2206_; lean_object* v_fst_2207_; lean_object* v_snd_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
lean_dec_ref(v_e_2191_);
v_val_2206_ = lean_ctor_get(v_a_2205_, 0);
lean_inc(v_val_2206_);
lean_dec_ref(v_a_2205_);
v_fst_2207_ = lean_ctor_get(v_val_2206_, 0);
lean_inc(v_fst_2207_);
v_snd_2208_ = lean_ctor_get(v_val_2206_, 1);
lean_inc(v_snd_2208_);
lean_dec(v_val_2206_);
v___x_2209_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1);
v___x_2210_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_snd_2208_, v___x_2209_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_);
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_object* v_a_2211_; lean_object* v___x_2212_; 
v_a_2211_ = lean_ctor_get(v___x_2210_, 0);
lean_inc(v_a_2211_);
lean_dec_ref(v___x_2210_);
v___x_2212_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go(v_fst_2207_, v_a_2211_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_);
return v___x_2212_;
}
else
{
lean_dec(v_fst_2207_);
return v___x_2210_;
}
}
else
{
lean_object* v___x_2213_; lean_object* v___x_2214_; 
lean_dec(v_a_2205_);
v___x_2213_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1);
v___x_2214_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_e_2191_, v___x_2213_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_);
return v___x_2214_;
}
}
else
{
lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2222_; 
lean_dec_ref(v_e_2191_);
v_a_2215_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2217_ = v___x_2204_;
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v___x_2204_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2220_; 
if (v_isShared_2218_ == 0)
{
v___x_2220_ = v___x_2217_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_a_2215_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly___boxed(lean_object* v_e_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_){
_start:
{
lean_object* v_res_2235_; 
v_res_2235_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_e_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_);
lean_dec(v_a_2233_);
lean_dec_ref(v_a_2232_);
lean_dec(v_a_2231_);
lean_dec_ref(v_a_2230_);
lean_dec(v_a_2229_);
lean_dec_ref(v_a_2228_);
lean_dec(v_a_2227_);
lean_dec_ref(v_a_2226_);
lean_dec(v_a_2225_);
lean_dec(v_a_2224_);
return v_res_2235_;
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
