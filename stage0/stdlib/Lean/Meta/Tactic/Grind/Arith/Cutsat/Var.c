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
size_t v_x_9052__boxed_335_; size_t v_x_9053__boxed_336_; lean_object* v_res_337_; 
v_x_9052__boxed_335_ = lean_unbox_usize(v_x_331_);
lean_dec(v_x_331_);
v_x_9053__boxed_336_ = lean_unbox_usize(v_x_332_);
lean_dec(v_x_332_);
v_res_337_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg(v_x_330_, v_x_9052__boxed_335_, v_x_9053__boxed_336_, v_x_333_, v_x_334_);
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
lean_object* v_es_405_; lean_object* v___x_406_; size_t v___x_407_; size_t v___x_408_; size_t v___x_409_; lean_object* v_j_410_; lean_object* v___x_411_; 
v_es_405_ = lean_ctor_get(v_x_402_, 0);
v___x_406_ = lean_box(2);
v___x_407_ = ((size_t)5ULL);
v___x_408_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1);
v___x_409_ = lean_usize_land(v_x_403_, v___x_408_);
v_j_410_ = lean_usize_to_nat(v___x_409_);
v___x_411_ = lean_array_get_borrowed(v___x_406_, v_es_405_, v_j_410_);
lean_dec(v_j_410_);
switch(lean_obj_tag(v___x_411_))
{
case 0:
{
lean_object* v_key_412_; lean_object* v_val_413_; uint8_t v___x_414_; 
v_key_412_ = lean_ctor_get(v___x_411_, 0);
v_val_413_ = lean_ctor_get(v___x_411_, 1);
v___x_414_ = lean_nat_dec_eq(v_x_404_, v_key_412_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; 
v___x_415_ = lean_box(0);
return v___x_415_;
}
else
{
lean_object* v___x_416_; 
lean_inc(v_val_413_);
v___x_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_416_, 0, v_val_413_);
return v___x_416_;
}
}
case 1:
{
lean_object* v_node_417_; size_t v___x_418_; 
v_node_417_ = lean_ctor_get(v___x_411_, 0);
v___x_418_ = lean_usize_shift_right(v_x_403_, v___x_407_);
v_x_402_ = v_node_417_;
v_x_403_ = v___x_418_;
goto _start;
}
default: 
{
lean_object* v___x_420_; 
v___x_420_ = lean_box(0);
return v___x_420_;
}
}
}
else
{
lean_object* v_ks_421_; lean_object* v_vs_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v_ks_421_ = lean_ctor_get(v_x_402_, 0);
v_vs_422_ = lean_ctor_get(v_x_402_, 1);
v___x_423_ = lean_unsigned_to_nat(0u);
v___x_424_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5___redArg(v_ks_421_, v_vs_422_, v___x_423_, v_x_404_);
return v___x_424_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2___redArg___boxed(lean_object* v_x_425_, lean_object* v_x_426_, lean_object* v_x_427_){
_start:
{
size_t v_x_9274__boxed_428_; lean_object* v_res_429_; 
v_x_9274__boxed_428_ = lean_unbox_usize(v_x_426_);
lean_dec(v_x_426_);
v_res_429_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2___redArg(v_x_425_, v_x_9274__boxed_428_, v_x_427_);
lean_dec(v_x_427_);
lean_dec_ref(v_x_425_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___redArg(lean_object* v_x_430_, lean_object* v_x_431_){
_start:
{
uint64_t v___x_432_; size_t v___x_433_; lean_object* v___x_434_; 
v___x_432_ = lean_uint64_of_nat(v_x_431_);
v___x_433_ = lean_uint64_to_usize(v___x_432_);
v___x_434_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2___redArg(v_x_430_, v___x_433_, v_x_431_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___redArg___boxed(lean_object* v_x_435_, lean_object* v_x_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___redArg(v_x_435_, v_x_436_);
lean_dec(v_x_436_);
lean_dec_ref(v_x_435_);
return v_res_437_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___closed__0(void){
_start:
{
lean_object* v___x_438_; lean_object* v___f_439_; 
v___x_438_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_439_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_439_, 0, v___x_438_);
return v___f_439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc(lean_object* v_arg_440_, lean_object* v_x_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_){
_start:
{
lean_object* v___x_453_; 
lean_inc(v_a_451_);
lean_inc_ref(v_a_450_);
lean_inc(v_a_449_);
lean_inc_ref(v_a_448_);
lean_inc(v_a_447_);
lean_inc_ref(v_a_446_);
lean_inc(v_a_445_);
lean_inc_ref(v_a_444_);
lean_inc(v_a_443_);
lean_inc(v_a_442_);
v___x_453_ = lean_grind_cutsat_mk_var(v_arg_440_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_);
if (lean_obj_tag(v___x_453_) == 0)
{
lean_object* v_a_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_525_; 
v_a_454_ = lean_ctor_get(v___x_453_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_525_ == 0)
{
v___x_456_ = v___x_453_;
v_isShared_457_ = v_isSharedCheck_525_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_a_454_);
lean_dec(v___x_453_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_525_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v___y_471_; lean_object* v___y_472_; lean_object* v___x_488_; 
v___x_488_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_442_, v_a_450_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; lean_object* v___y_491_; lean_object* v_elimEqs_511_; lean_object* v_size_512_; lean_object* v___x_513_; uint8_t v___x_514_; 
v_a_489_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_a_489_);
lean_dec_ref(v___x_488_);
v_elimEqs_511_ = lean_ctor_get(v_a_489_, 10);
lean_inc_ref(v_elimEqs_511_);
lean_dec(v_a_489_);
v_size_512_ = lean_ctor_get(v_elimEqs_511_, 2);
v___x_513_ = lean_box(0);
v___x_514_ = lean_nat_dec_lt(v_a_454_, v_size_512_);
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
v___x_516_ = l_Lean_PersistentArray_get_x21___redArg(v___x_513_, v_elimEqs_511_, v_a_454_);
lean_dec_ref(v_elimEqs_511_);
v___y_491_ = v___x_516_;
goto v___jp_490_;
}
v___jp_490_:
{
if (lean_obj_tag(v___y_491_) == 0)
{
v___y_471_ = v_a_442_;
v___y_472_ = v_a_450_;
goto v___jp_470_;
}
else
{
lean_object* v___x_492_; 
lean_dec_ref(v___y_491_);
lean_inc(v_a_451_);
lean_inc_ref(v_a_450_);
lean_inc(v_a_449_);
lean_inc_ref(v_a_448_);
lean_inc(v_a_447_);
lean_inc_ref(v_a_446_);
lean_inc(v_a_445_);
lean_inc_ref(v_a_444_);
lean_inc(v_a_443_);
lean_inc(v_a_442_);
lean_inc(v_x_441_);
lean_inc(v_a_454_);
v___x_492_ = lean_cutsat_propagate_nonlinear(v_a_454_, v_x_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_);
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
v___y_471_ = v_a_442_;
v___y_472_ = v_a_450_;
goto v___jp_470_;
}
else
{
lean_object* v___x_498_; lean_object* v___x_500_; 
lean_del_object(v___x_456_);
lean_dec(v_a_454_);
lean_dec(v_x_441_);
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
lean_del_object(v___x_456_);
lean_dec(v_a_454_);
lean_dec(v_x_441_);
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
lean_del_object(v___x_456_);
lean_dec(v_a_454_);
lean_dec(v_x_441_);
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
v___jp_458_:
{
uint8_t v___x_462_; 
lean_inc(v___y_461_);
lean_inc(v_x_441_);
lean_inc_ref(v___y_460_);
v___x_462_ = l_List_elem___redArg(v___y_460_, v_x_441_, v___y_461_);
if (v___x_462_ == 0)
{
lean_object* v___f_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
lean_del_object(v___x_456_);
v___f_463_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___lam__0), 4, 3);
lean_closure_set(v___f_463_, 0, v_x_441_);
lean_closure_set(v___f_463_, 1, v___y_461_);
lean_closure_set(v___f_463_, 2, v_a_454_);
v___x_464_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_465_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_464_, v___f_463_, v___y_459_);
return v___x_465_;
}
else
{
lean_object* v___x_466_; lean_object* v___x_468_; 
lean_dec(v___y_461_);
lean_dec(v_a_454_);
lean_dec(v_x_441_);
v___x_466_ = lean_box(0);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 0, v___x_466_);
v___x_468_ = v___x_456_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
v___jp_470_:
{
lean_object* v___x_473_; 
v___x_473_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v___y_471_, v___y_472_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; lean_object* v_nonlinearOccs_475_; lean_object* v___f_476_; lean_object* v___x_477_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
lean_inc(v_a_474_);
lean_dec_ref(v___x_473_);
v_nonlinearOccs_475_ = lean_ctor_get(v_a_474_, 22);
lean_inc_ref(v_nonlinearOccs_475_);
lean_dec(v_a_474_);
v___f_476_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc___closed__0);
v___x_477_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___redArg(v_nonlinearOccs_475_, v_a_454_);
lean_dec_ref(v_nonlinearOccs_475_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v___x_478_; 
v___x_478_ = lean_box(0);
v___y_459_ = v___y_471_;
v___y_460_ = v___f_476_;
v___y_461_ = v___x_478_;
goto v___jp_458_;
}
else
{
lean_object* v_val_479_; 
v_val_479_ = lean_ctor_get(v___x_477_, 0);
lean_inc(v_val_479_);
lean_dec_ref(v___x_477_);
v___y_459_ = v___y_471_;
v___y_460_ = v___f_476_;
v___y_461_ = v_val_479_;
goto v___jp_458_;
}
}
else
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
lean_del_object(v___x_456_);
lean_dec(v_a_454_);
lean_dec(v_x_441_);
v_a_480_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v___x_473_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_473_);
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
lean_dec(v_x_441_);
v_a_526_ = lean_ctor_get(v___x_453_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v___x_453_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_453_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1(lean_object* v_00_u03b2_553_, lean_object* v_x_554_, lean_object* v_x_555_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___redArg(v_x_554_, v_x_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1___boxed(lean_object* v_00_u03b2_557_, lean_object* v_x_558_, lean_object* v_x_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1(v_00_u03b2_557_, v_x_558_, v_x_559_);
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
size_t v_x_9517__boxed_574_; size_t v_x_9518__boxed_575_; lean_object* v_res_576_; 
v_x_9517__boxed_574_ = lean_unbox_usize(v_x_570_);
lean_dec(v_x_570_);
v_x_9518__boxed_575_ = lean_unbox_usize(v_x_571_);
lean_dec(v_x_571_);
v_res_576_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0(v_00_u03b2_568_, v_x_569_, v_x_9517__boxed_574_, v_x_9518__boxed_575_, v_x_572_, v_x_573_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2(lean_object* v_00_u03b2_577_, lean_object* v_x_578_, size_t v_x_579_, lean_object* v_x_580_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2___redArg(v_x_578_, v_x_579_, v_x_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2___boxed(lean_object* v_00_u03b2_582_, lean_object* v_x_583_, lean_object* v_x_584_, lean_object* v_x_585_){
_start:
{
size_t v_x_9534__boxed_586_; lean_object* v_res_587_; 
v_x_9534__boxed_586_ = lean_unbox_usize(v_x_584_);
lean_dec(v_x_584_);
v_res_587_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2(v_00_u03b2_582_, v_x_583_, v_x_9534__boxed_586_, v_x_585_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_610_, lean_object* v_keys_611_, lean_object* v_vals_612_, lean_object* v_heq_613_, lean_object* v_i_614_, lean_object* v_k_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5___redArg(v_keys_611_, v_vals_612_, v_i_614_, v_k_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_617_, lean_object* v_keys_618_, lean_object* v_vals_619_, lean_object* v_heq_620_, lean_object* v_i_621_, lean_object* v_k_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__1_spec__2_spec__5(v_00_u03b2_617_, v_keys_618_, v_vals_619_, v_heq_620_, v_i_621_, v_k_622_);
lean_dec(v_k_622_);
lean_dec_ref(v_vals_619_);
lean_dec_ref(v_keys_618_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_624_, lean_object* v_x_625_, lean_object* v_x_626_, lean_object* v_x_627_, lean_object* v_x_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0_spec__1_spec__3___redArg(v_x_625_, v_x_626_, v_x_627_, v_x_628_);
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
lean_dec_ref(v___x_643_);
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
lean_dec_ref(v___x_670_);
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
lean_dec_ref(v___x_674_);
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
lean_dec_ref(v___x_810_);
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
lean_dec_ref(v___x_814_);
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
lean_dec_ref(v___x_816_);
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
lean_dec_ref(v_a_815_);
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
lean_dec_ref(v___x_760_);
v___x_762_ = l_Lean_Meta_getNatValue_x3f(v_arg_734_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
if (lean_obj_tag(v___x_762_) == 0)
{
if (lean_obj_tag(v_a_761_) == 0)
{
if (v___x_748_ == 0)
{
lean_dec_ref(v___x_762_);
lean_dec_ref(v_arg_734_);
lean_dec(v_x_707_);
goto v___jp_719_;
}
else
{
lean_object* v_a_763_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_a_763_);
lean_dec_ref(v___x_762_);
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
lean_dec_ref(v___x_764_);
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
lean_dec_ref(v___x_767_);
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
lean_dec_ref(v___x_770_);
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
lean_dec_ref(v_a_763_);
lean_dec_ref(v_arg_734_);
lean_dec(v_x_707_);
goto v___jp_719_;
}
}
}
else
{
lean_dec_ref(v_a_761_);
lean_dec_ref(v___x_762_);
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
lean_object* v_ks_852_; lean_object* v_vs_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_877_; 
v_ks_852_ = lean_ctor_get(v_x_848_, 0);
v_vs_853_ = lean_ctor_get(v_x_848_, 1);
v_isSharedCheck_877_ = !lean_is_exclusive(v_x_848_);
if (v_isSharedCheck_877_ == 0)
{
v___x_855_ = v_x_848_;
v_isShared_856_ = v_isSharedCheck_877_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_vs_853_);
lean_inc(v_ks_852_);
lean_dec(v_x_848_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_877_;
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
lean_object* v_k_x27_864_; uint8_t v___x_865_; 
v_k_x27_864_ = lean_array_fget_borrowed(v_ks_852_, v_x_849_);
v___x_865_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_850_, v_k_x27_864_);
if (v___x_865_ == 0)
{
lean_object* v___x_867_; 
if (v_isShared_856_ == 0)
{
v___x_867_ = v___x_855_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_ks_852_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v_vs_853_);
v___x_867_ = v_reuseFailAlloc_871_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_868_ = lean_unsigned_to_nat(1u);
v___x_869_ = lean_nat_add(v_x_849_, v___x_868_);
lean_dec(v_x_849_);
v_x_848_ = v___x_867_;
v_x_849_ = v___x_869_;
goto _start;
}
}
else
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_875_; 
v___x_872_ = lean_array_fset(v_ks_852_, v_x_849_, v_x_850_);
v___x_873_ = lean_array_fset(v_vs_853_, v_x_849_, v_x_851_);
lean_dec(v_x_849_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 1, v___x_873_);
lean_ctor_set(v___x_855_, 0, v___x_872_);
v___x_875_ = v___x_855_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_872_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v___x_873_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4___redArg(lean_object* v_n_878_, lean_object* v_k_879_, lean_object* v_v_880_){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = lean_unsigned_to_nat(0u);
v___x_882_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7___redArg(v_n_878_, v___x_881_, v_k_879_, v_v_880_);
return v___x_882_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(lean_object* v_x_884_, size_t v_x_885_, size_t v_x_886_, lean_object* v_x_887_, lean_object* v_x_888_){
_start:
{
if (lean_obj_tag(v_x_884_) == 0)
{
lean_object* v_es_889_; size_t v___x_890_; size_t v___x_891_; size_t v___x_892_; size_t v___x_893_; lean_object* v_j_894_; lean_object* v___x_895_; uint8_t v___x_896_; 
v_es_889_ = lean_ctor_get(v_x_884_, 0);
v___x_890_ = ((size_t)5ULL);
v___x_891_ = ((size_t)1ULL);
v___x_892_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1);
v___x_893_ = lean_usize_land(v_x_885_, v___x_892_);
v_j_894_ = lean_usize_to_nat(v___x_893_);
v___x_895_ = lean_array_get_size(v_es_889_);
v___x_896_ = lean_nat_dec_lt(v_j_894_, v___x_895_);
if (v___x_896_ == 0)
{
lean_dec(v_j_894_);
lean_dec(v_x_888_);
lean_dec_ref(v_x_887_);
return v_x_884_;
}
else
{
lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_933_; 
lean_inc_ref(v_es_889_);
v_isSharedCheck_933_ = !lean_is_exclusive(v_x_884_);
if (v_isSharedCheck_933_ == 0)
{
lean_object* v_unused_934_; 
v_unused_934_ = lean_ctor_get(v_x_884_, 0);
lean_dec(v_unused_934_);
v___x_898_ = v_x_884_;
v_isShared_899_ = v_isSharedCheck_933_;
goto v_resetjp_897_;
}
else
{
lean_dec(v_x_884_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_933_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v_v_900_; lean_object* v___x_901_; lean_object* v_xs_x27_902_; lean_object* v___y_904_; 
v_v_900_ = lean_array_fget(v_es_889_, v_j_894_);
v___x_901_ = lean_box(0);
v_xs_x27_902_ = lean_array_fset(v_es_889_, v_j_894_, v___x_901_);
switch(lean_obj_tag(v_v_900_))
{
case 0:
{
lean_object* v_key_909_; lean_object* v_val_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_920_; 
v_key_909_ = lean_ctor_get(v_v_900_, 0);
v_val_910_ = lean_ctor_get(v_v_900_, 1);
v_isSharedCheck_920_ = !lean_is_exclusive(v_v_900_);
if (v_isSharedCheck_920_ == 0)
{
v___x_912_ = v_v_900_;
v_isShared_913_ = v_isSharedCheck_920_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_val_910_);
lean_inc(v_key_909_);
lean_dec(v_v_900_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_920_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
uint8_t v___x_914_; 
v___x_914_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_887_, v_key_909_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; lean_object* v___x_916_; 
lean_del_object(v___x_912_);
v___x_915_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_909_, v_val_910_, v_x_887_, v_x_888_);
v___x_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
v___y_904_ = v___x_916_;
goto v___jp_903_;
}
else
{
lean_object* v___x_918_; 
lean_dec(v_val_910_);
lean_dec(v_key_909_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 1, v_x_888_);
lean_ctor_set(v___x_912_, 0, v_x_887_);
v___x_918_ = v___x_912_;
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
v___y_904_ = v___x_918_;
goto v___jp_903_;
}
}
}
}
case 1:
{
lean_object* v_node_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_931_; 
v_node_921_ = lean_ctor_get(v_v_900_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v_v_900_);
if (v_isSharedCheck_931_ == 0)
{
v___x_923_ = v_v_900_;
v_isShared_924_ = v_isSharedCheck_931_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_node_921_);
lean_dec(v_v_900_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_931_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
size_t v___x_925_; size_t v___x_926_; lean_object* v___x_927_; lean_object* v___x_929_; 
v___x_925_ = lean_usize_shift_right(v_x_885_, v___x_890_);
v___x_926_ = lean_usize_add(v_x_886_, v___x_891_);
v___x_927_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_node_921_, v___x_925_, v___x_926_, v_x_887_, v_x_888_);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 0, v___x_927_);
v___x_929_ = v___x_923_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_927_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
v___y_904_ = v___x_929_;
goto v___jp_903_;
}
}
}
default: 
{
lean_object* v___x_932_; 
v___x_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_932_, 0, v_x_887_);
lean_ctor_set(v___x_932_, 1, v_x_888_);
v___y_904_ = v___x_932_;
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
lean_object* v_ks_935_; lean_object* v_vs_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_956_; 
v_ks_935_ = lean_ctor_get(v_x_884_, 0);
v_vs_936_ = lean_ctor_get(v_x_884_, 1);
v_isSharedCheck_956_ = !lean_is_exclusive(v_x_884_);
if (v_isSharedCheck_956_ == 0)
{
v___x_938_ = v_x_884_;
v_isShared_939_ = v_isSharedCheck_956_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_vs_936_);
lean_inc(v_ks_935_);
lean_dec(v_x_884_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_956_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
if (v_isShared_939_ == 0)
{
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_ks_935_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v_vs_936_);
v___x_941_ = v_reuseFailAlloc_955_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
lean_object* v_newNode_942_; uint8_t v___y_944_; size_t v___x_950_; uint8_t v___x_951_; 
v_newNode_942_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4___redArg(v___x_941_, v_x_887_, v_x_888_);
v___x_950_ = ((size_t)7ULL);
v___x_951_ = lean_usize_dec_le(v___x_950_, v_x_886_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; lean_object* v___x_953_; uint8_t v___x_954_; 
v___x_952_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_942_);
v___x_953_ = lean_unsigned_to_nat(4u);
v___x_954_ = lean_nat_dec_lt(v___x_952_, v___x_953_);
lean_dec(v___x_952_);
v___y_944_ = v___x_954_;
goto v___jp_943_;
}
else
{
v___y_944_ = v___x_951_;
goto v___jp_943_;
}
v___jp_943_:
{
if (v___y_944_ == 0)
{
lean_object* v_ks_945_; lean_object* v_vs_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v_ks_945_ = lean_ctor_get(v_newNode_942_, 0);
lean_inc_ref(v_ks_945_);
v_vs_946_ = lean_ctor_get(v_newNode_942_, 1);
lean_inc_ref(v_vs_946_);
lean_dec_ref(v_newNode_942_);
v___x_947_ = lean_unsigned_to_nat(0u);
v___x_948_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg___closed__0);
v___x_949_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(v_x_886_, v_ks_945_, v_vs_946_, v___x_947_, v___x_948_);
lean_dec_ref(v_vs_946_);
lean_dec_ref(v_ks_945_);
return v___x_949_;
}
else
{
return v_newNode_942_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(size_t v_depth_957_, lean_object* v_keys_958_, lean_object* v_vals_959_, lean_object* v_i_960_, lean_object* v_entries_961_){
_start:
{
lean_object* v___x_962_; uint8_t v___x_963_; 
v___x_962_ = lean_array_get_size(v_keys_958_);
v___x_963_ = lean_nat_dec_lt(v_i_960_, v___x_962_);
if (v___x_963_ == 0)
{
lean_dec(v_i_960_);
return v_entries_961_;
}
else
{
lean_object* v_k_964_; lean_object* v_v_965_; uint64_t v___x_966_; size_t v_h_967_; size_t v___x_968_; lean_object* v___x_969_; size_t v___x_970_; size_t v___x_971_; size_t v___x_972_; size_t v_h_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v_k_964_ = lean_array_fget_borrowed(v_keys_958_, v_i_960_);
v_v_965_ = lean_array_fget_borrowed(v_vals_959_, v_i_960_);
v___x_966_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_964_);
v_h_967_ = lean_uint64_to_usize(v___x_966_);
v___x_968_ = ((size_t)5ULL);
v___x_969_ = lean_unsigned_to_nat(1u);
v___x_970_ = ((size_t)1ULL);
v___x_971_ = lean_usize_sub(v_depth_957_, v___x_970_);
v___x_972_ = lean_usize_mul(v___x_968_, v___x_971_);
v_h_973_ = lean_usize_shift_right(v_h_967_, v___x_972_);
v___x_974_ = lean_nat_add(v_i_960_, v___x_969_);
lean_dec(v_i_960_);
lean_inc(v_v_965_);
lean_inc(v_k_964_);
v___x_975_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_entries_961_, v_h_973_, v_depth_957_, v_k_964_, v_v_965_);
v_i_960_ = v___x_974_;
v_entries_961_ = v___x_975_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_977_, lean_object* v_keys_978_, lean_object* v_vals_979_, lean_object* v_i_980_, lean_object* v_entries_981_){
_start:
{
size_t v_depth_boxed_982_; lean_object* v_res_983_; 
v_depth_boxed_982_ = lean_unbox_usize(v_depth_977_);
lean_dec(v_depth_977_);
v_res_983_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(v_depth_boxed_982_, v_keys_978_, v_vals_979_, v_i_980_, v_entries_981_);
lean_dec_ref(v_vals_979_);
lean_dec_ref(v_keys_978_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg___boxed(lean_object* v_x_984_, lean_object* v_x_985_, lean_object* v_x_986_, lean_object* v_x_987_, lean_object* v_x_988_){
_start:
{
size_t v_x_32824__boxed_989_; size_t v_x_32825__boxed_990_; lean_object* v_res_991_; 
v_x_32824__boxed_989_ = lean_unbox_usize(v_x_985_);
lean_dec(v_x_985_);
v_x_32825__boxed_990_ = lean_unbox_usize(v_x_986_);
lean_dec(v_x_986_);
v_res_991_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_x_984_, v_x_32824__boxed_989_, v_x_32825__boxed_990_, v_x_987_, v_x_988_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg(lean_object* v_x_992_, lean_object* v_x_993_, lean_object* v_x_994_){
_start:
{
uint64_t v___x_995_; size_t v___x_996_; size_t v___x_997_; lean_object* v___x_998_; 
v___x_995_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_993_);
v___x_996_ = lean_uint64_to_usize(v___x_995_);
v___x_997_ = ((size_t)1ULL);
v___x_998_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_x_992_, v___x_996_, v___x_997_, v_x_993_, v_x_994_);
return v___x_998_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_999_ = lean_unsigned_to_nat(32u);
v___x_1000_ = lean_mk_empty_array_with_capacity(v___x_999_);
v___x_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
return v___x_1001_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1(void){
_start:
{
size_t v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1002_ = ((size_t)5ULL);
v___x_1003_ = lean_unsigned_to_nat(0u);
v___x_1004_ = lean_unsigned_to_nat(32u);
v___x_1005_ = lean_mk_empty_array_with_capacity(v___x_1004_);
v___x_1006_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__0);
v___x_1007_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
lean_ctor_set(v___x_1007_, 1, v___x_1005_);
lean_ctor_set(v___x_1007_, 2, v___x_1003_);
lean_ctor_set(v___x_1007_, 3, v___x_1003_);
lean_ctor_set_usize(v___x_1007_, 4, v___x_1002_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0(lean_object* v_expr_1008_, lean_object* v_size_1009_, lean_object* v_s_1010_){
_start:
{
lean_object* v_vars_1011_; lean_object* v_varMap_1012_; lean_object* v_vars_x27_1013_; lean_object* v_varMap_x27_1014_; lean_object* v_natToIntMap_1015_; lean_object* v_natDef_1016_; lean_object* v_dvds_1017_; lean_object* v_lowers_1018_; lean_object* v_uppers_1019_; lean_object* v_diseqs_1020_; lean_object* v_elimEqs_1021_; lean_object* v_elimStack_1022_; lean_object* v_occurs_1023_; lean_object* v_assignment_1024_; lean_object* v_nextCnstrId_1025_; uint8_t v_caseSplits_1026_; lean_object* v_conflict_x3f_1027_; lean_object* v_diseqSplits_1028_; lean_object* v_divMod_1029_; lean_object* v_toIntIds_1030_; lean_object* v_toIntInfos_1031_; lean_object* v_toIntTermMap_1032_; lean_object* v_toIntVarMap_1033_; uint8_t v_usedCommRing_1034_; lean_object* v_nonlinearOccs_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1053_; 
v_vars_1011_ = lean_ctor_get(v_s_1010_, 0);
v_varMap_1012_ = lean_ctor_get(v_s_1010_, 1);
v_vars_x27_1013_ = lean_ctor_get(v_s_1010_, 2);
v_varMap_x27_1014_ = lean_ctor_get(v_s_1010_, 3);
v_natToIntMap_1015_ = lean_ctor_get(v_s_1010_, 4);
v_natDef_1016_ = lean_ctor_get(v_s_1010_, 5);
v_dvds_1017_ = lean_ctor_get(v_s_1010_, 6);
v_lowers_1018_ = lean_ctor_get(v_s_1010_, 7);
v_uppers_1019_ = lean_ctor_get(v_s_1010_, 8);
v_diseqs_1020_ = lean_ctor_get(v_s_1010_, 9);
v_elimEqs_1021_ = lean_ctor_get(v_s_1010_, 10);
v_elimStack_1022_ = lean_ctor_get(v_s_1010_, 11);
v_occurs_1023_ = lean_ctor_get(v_s_1010_, 12);
v_assignment_1024_ = lean_ctor_get(v_s_1010_, 13);
v_nextCnstrId_1025_ = lean_ctor_get(v_s_1010_, 14);
v_caseSplits_1026_ = lean_ctor_get_uint8(v_s_1010_, sizeof(void*)*23);
v_conflict_x3f_1027_ = lean_ctor_get(v_s_1010_, 15);
v_diseqSplits_1028_ = lean_ctor_get(v_s_1010_, 16);
v_divMod_1029_ = lean_ctor_get(v_s_1010_, 17);
v_toIntIds_1030_ = lean_ctor_get(v_s_1010_, 18);
v_toIntInfos_1031_ = lean_ctor_get(v_s_1010_, 19);
v_toIntTermMap_1032_ = lean_ctor_get(v_s_1010_, 20);
v_toIntVarMap_1033_ = lean_ctor_get(v_s_1010_, 21);
v_usedCommRing_1034_ = lean_ctor_get_uint8(v_s_1010_, sizeof(void*)*23 + 1);
v_nonlinearOccs_1035_ = lean_ctor_get(v_s_1010_, 22);
v_isSharedCheck_1053_ = !lean_is_exclusive(v_s_1010_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1037_ = v_s_1010_;
v_isShared_1038_ = v_isSharedCheck_1053_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_nonlinearOccs_1035_);
lean_inc(v_toIntVarMap_1033_);
lean_inc(v_toIntTermMap_1032_);
lean_inc(v_toIntInfos_1031_);
lean_inc(v_toIntIds_1030_);
lean_inc(v_divMod_1029_);
lean_inc(v_diseqSplits_1028_);
lean_inc(v_conflict_x3f_1027_);
lean_inc(v_nextCnstrId_1025_);
lean_inc(v_assignment_1024_);
lean_inc(v_occurs_1023_);
lean_inc(v_elimStack_1022_);
lean_inc(v_elimEqs_1021_);
lean_inc(v_diseqs_1020_);
lean_inc(v_uppers_1019_);
lean_inc(v_lowers_1018_);
lean_inc(v_dvds_1017_);
lean_inc(v_natDef_1016_);
lean_inc(v_natToIntMap_1015_);
lean_inc(v_varMap_x27_1014_);
lean_inc(v_vars_x27_1013_);
lean_inc(v_varMap_1012_);
lean_inc(v_vars_1011_);
lean_dec(v_s_1010_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1053_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1051_; 
lean_inc_ref(v_expr_1008_);
v___x_1039_ = l_Lean_PersistentArray_push___redArg(v_vars_1011_, v_expr_1008_);
v___x_1040_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg(v_varMap_1012_, v_expr_1008_, v_size_1009_);
v___x_1041_ = lean_box(0);
v___x_1042_ = l_Lean_PersistentArray_push___redArg(v_dvds_1017_, v___x_1041_);
v___x_1043_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0___closed__1);
v___x_1044_ = l_Lean_PersistentArray_push___redArg(v_lowers_1018_, v___x_1043_);
v___x_1045_ = l_Lean_PersistentArray_push___redArg(v_uppers_1019_, v___x_1043_);
v___x_1046_ = l_Lean_PersistentArray_push___redArg(v_diseqs_1020_, v___x_1043_);
v___x_1047_ = l_Lean_PersistentArray_push___redArg(v_elimEqs_1021_, v___x_1041_);
v___x_1048_ = lean_box(1);
v___x_1049_ = l_Lean_PersistentArray_push___redArg(v_occurs_1023_, v___x_1048_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 12, v___x_1049_);
lean_ctor_set(v___x_1037_, 10, v___x_1047_);
lean_ctor_set(v___x_1037_, 9, v___x_1046_);
lean_ctor_set(v___x_1037_, 8, v___x_1045_);
lean_ctor_set(v___x_1037_, 7, v___x_1044_);
lean_ctor_set(v___x_1037_, 6, v___x_1042_);
lean_ctor_set(v___x_1037_, 1, v___x_1040_);
lean_ctor_set(v___x_1037_, 0, v___x_1039_);
v___x_1051_ = v___x_1037_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v___x_1040_);
lean_ctor_set(v_reuseFailAlloc_1052_, 2, v_vars_x27_1013_);
lean_ctor_set(v_reuseFailAlloc_1052_, 3, v_varMap_x27_1014_);
lean_ctor_set(v_reuseFailAlloc_1052_, 4, v_natToIntMap_1015_);
lean_ctor_set(v_reuseFailAlloc_1052_, 5, v_natDef_1016_);
lean_ctor_set(v_reuseFailAlloc_1052_, 6, v___x_1042_);
lean_ctor_set(v_reuseFailAlloc_1052_, 7, v___x_1044_);
lean_ctor_set(v_reuseFailAlloc_1052_, 8, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1052_, 9, v___x_1046_);
lean_ctor_set(v_reuseFailAlloc_1052_, 10, v___x_1047_);
lean_ctor_set(v_reuseFailAlloc_1052_, 11, v_elimStack_1022_);
lean_ctor_set(v_reuseFailAlloc_1052_, 12, v___x_1049_);
lean_ctor_set(v_reuseFailAlloc_1052_, 13, v_assignment_1024_);
lean_ctor_set(v_reuseFailAlloc_1052_, 14, v_nextCnstrId_1025_);
lean_ctor_set(v_reuseFailAlloc_1052_, 15, v_conflict_x3f_1027_);
lean_ctor_set(v_reuseFailAlloc_1052_, 16, v_diseqSplits_1028_);
lean_ctor_set(v_reuseFailAlloc_1052_, 17, v_divMod_1029_);
lean_ctor_set(v_reuseFailAlloc_1052_, 18, v_toIntIds_1030_);
lean_ctor_set(v_reuseFailAlloc_1052_, 19, v_toIntInfos_1031_);
lean_ctor_set(v_reuseFailAlloc_1052_, 20, v_toIntTermMap_1032_);
lean_ctor_set(v_reuseFailAlloc_1052_, 21, v_toIntVarMap_1033_);
lean_ctor_set(v_reuseFailAlloc_1052_, 22, v_nonlinearOccs_1035_);
lean_ctor_set_uint8(v_reuseFailAlloc_1052_, sizeof(void*)*23, v_caseSplits_1026_);
lean_ctor_set_uint8(v_reuseFailAlloc_1052_, sizeof(void*)*23 + 1, v_usedCommRing_1034_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1054_, lean_object* v_vals_1055_, lean_object* v_i_1056_, lean_object* v_k_1057_){
_start:
{
lean_object* v___x_1058_; uint8_t v___x_1059_; 
v___x_1058_ = lean_array_get_size(v_keys_1054_);
v___x_1059_ = lean_nat_dec_lt(v_i_1056_, v___x_1058_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1060_; 
lean_dec(v_i_1056_);
v___x_1060_ = lean_box(0);
return v___x_1060_;
}
else
{
lean_object* v_k_x27_1061_; uint8_t v___x_1062_; 
v_k_x27_1061_ = lean_array_fget_borrowed(v_keys_1054_, v_i_1056_);
v___x_1062_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_1057_, v_k_x27_1061_);
if (v___x_1062_ == 0)
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = lean_unsigned_to_nat(1u);
v___x_1064_ = lean_nat_add(v_i_1056_, v___x_1063_);
lean_dec(v_i_1056_);
v_i_1056_ = v___x_1064_;
goto _start;
}
else
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = lean_array_fget_borrowed(v_vals_1055_, v_i_1056_);
lean_dec(v_i_1056_);
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
lean_object* v_es_1076_; lean_object* v___x_1077_; size_t v___x_1078_; size_t v___x_1079_; size_t v___x_1080_; lean_object* v_j_1081_; lean_object* v___x_1082_; 
v_es_1076_ = lean_ctor_get(v_x_1073_, 0);
v___x_1077_ = lean_box(2);
v___x_1078_ = ((size_t)5ULL);
v___x_1079_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOcc_spec__0_spec__0___redArg___closed__1);
v___x_1080_ = lean_usize_land(v_x_1074_, v___x_1079_);
v_j_1081_ = lean_usize_to_nat(v___x_1080_);
v___x_1082_ = lean_array_get_borrowed(v___x_1077_, v_es_1076_, v_j_1081_);
lean_dec(v_j_1081_);
switch(lean_obj_tag(v___x_1082_))
{
case 0:
{
lean_object* v_key_1083_; lean_object* v_val_1084_; uint8_t v___x_1085_; 
v_key_1083_ = lean_ctor_get(v___x_1082_, 0);
v_val_1084_ = lean_ctor_get(v___x_1082_, 1);
v___x_1085_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1075_, v_key_1083_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1086_; 
v___x_1086_ = lean_box(0);
return v___x_1086_;
}
else
{
lean_object* v___x_1087_; 
lean_inc(v_val_1084_);
v___x_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1087_, 0, v_val_1084_);
return v___x_1087_;
}
}
case 1:
{
lean_object* v_node_1088_; size_t v___x_1089_; 
v_node_1088_ = lean_ctor_get(v___x_1082_, 0);
v___x_1089_ = lean_usize_shift_right(v_x_1074_, v___x_1078_);
v_x_1073_ = v_node_1088_;
v_x_1074_ = v___x_1089_;
goto _start;
}
default: 
{
lean_object* v___x_1091_; 
v___x_1091_ = lean_box(0);
return v___x_1091_;
}
}
}
else
{
lean_object* v_ks_1092_; lean_object* v_vs_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v_ks_1092_ = lean_ctor_get(v_x_1073_, 0);
v_vs_1093_ = lean_ctor_get(v_x_1073_, 1);
v___x_1094_ = lean_unsigned_to_nat(0u);
v___x_1095_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(v_ks_1092_, v_vs_1093_, v___x_1094_, v_x_1075_);
return v___x_1095_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg___boxed(lean_object* v_x_1096_, lean_object* v_x_1097_, lean_object* v_x_1098_){
_start:
{
size_t v_x_33083__boxed_1099_; lean_object* v_res_1100_; 
v_x_33083__boxed_1099_ = lean_unbox_usize(v_x_1097_);
lean_dec(v_x_1097_);
v_res_1100_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(v_x_1096_, v_x_33083__boxed_1099_, v_x_1098_);
lean_dec_ref(v_x_1098_);
lean_dec_ref(v_x_1096_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(lean_object* v_x_1101_, lean_object* v_x_1102_){
_start:
{
uint64_t v___x_1103_; size_t v___x_1104_; lean_object* v___x_1105_; 
v___x_1103_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1102_);
v___x_1104_ = lean_uint64_to_usize(v___x_1103_);
v___x_1105_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(v_x_1101_, v___x_1104_, v_x_1102_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg___boxed(lean_object* v_x_1106_, lean_object* v_x_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(v_x_1106_, v_x_1107_);
lean_dec_ref(v_x_1107_);
lean_dec_ref(v_x_1106_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2_spec__4(lean_object* v_msgData_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v___x_1115_; lean_object* v_env_1116_; lean_object* v___x_1117_; lean_object* v_mctx_1118_; lean_object* v_lctx_1119_; lean_object* v_options_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1115_ = lean_st_ref_get(v___y_1113_);
v_env_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc_ref(v_env_1116_);
lean_dec(v___x_1115_);
v___x_1117_ = lean_st_ref_get(v___y_1111_);
v_mctx_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc_ref(v_mctx_1118_);
lean_dec(v___x_1117_);
v_lctx_1119_ = lean_ctor_get(v___y_1110_, 2);
v_options_1120_ = lean_ctor_get(v___y_1112_, 2);
lean_inc_ref(v_options_1120_);
lean_inc_ref(v_lctx_1119_);
v___x_1121_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1121_, 0, v_env_1116_);
lean_ctor_set(v___x_1121_, 1, v_mctx_1118_);
lean_ctor_set(v___x_1121_, 2, v_lctx_1119_);
lean_ctor_set(v___x_1121_, 3, v_options_1120_);
v___x_1122_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1121_);
lean_ctor_set(v___x_1122_, 1, v_msgData_1109_);
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
v_ref_1143_ = lean_ctor_get(v___y_1140_, 5);
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
lean_object* v___x_1167_; double v___x_1168_; uint8_t v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1167_ = lean_box(0);
v___x_1168_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__0);
v___x_1169_ = 0;
v___x_1170_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__1));
v___x_1171_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1171_, 0, v_cls_1136_);
lean_ctor_set(v___x_1171_, 1, v___x_1167_);
lean_ctor_set(v___x_1171_, 2, v___x_1170_);
lean_ctor_set_float(v___x_1171_, sizeof(void*)*3, v___x_1168_);
lean_ctor_set_float(v___x_1171_, sizeof(void*)*3 + 8, v___x_1168_);
lean_ctor_set_uint8(v___x_1171_, sizeof(void*)*3 + 16, v___x_1169_);
v___x_1172_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg___closed__2));
v___x_1173_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1171_);
lean_ctor_set(v___x_1173_, 1, v_a_1145_);
lean_ctor_set(v___x_1173_, 2, v___x_1172_);
lean_inc(v_ref_1143_);
v___x_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1174_, 0, v_ref_1143_);
lean_ctor_set(v___x_1174_, 1, v___x_1173_);
v___x_1175_ = l_Lean_PersistentArray_push___redArg(v_traces_1163_, v___x_1174_);
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 0, v___x_1175_);
v___x_1177_ = v___x_1165_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1175_);
lean_ctor_set_uint64(v_reuseFailAlloc_1186_, sizeof(void*)*1, v_tid_1162_);
v___x_1177_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
lean_object* v___x_1179_; 
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 4, v___x_1177_);
v___x_1179_ = v___x_1160_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_env_1151_);
lean_ctor_set(v_reuseFailAlloc_1185_, 1, v_nextMacroScope_1152_);
lean_ctor_set(v_reuseFailAlloc_1185_, 2, v_ngen_1153_);
lean_ctor_set(v_reuseFailAlloc_1185_, 3, v_auxDeclNGen_1154_);
lean_ctor_set(v_reuseFailAlloc_1185_, 4, v___x_1177_);
lean_ctor_set(v_reuseFailAlloc_1185_, 5, v_cache_1155_);
lean_ctor_set(v_reuseFailAlloc_1185_, 6, v_messages_1156_);
lean_ctor_set(v_reuseFailAlloc_1185_, 7, v_infoState_1157_);
lean_ctor_set(v_reuseFailAlloc_1185_, 8, v_snapshotTasks_1158_);
v___x_1179_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1183_; 
v___x_1180_ = lean_st_ref_set(v___y_1141_, v___x_1179_);
v___x_1181_ = lean_box(0);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 0, v___x_1181_);
v___x_1183_ = v___x_1147_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1181_);
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
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1366_; 
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1231_ = v___x_1228_;
v_isShared_1232_ = v_isSharedCheck_1366_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1228_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1366_;
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
lean_dec_ref(v___x_1234_);
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
lean_object* v_a_1240_; lean_object* v_vars_1241_; lean_object* v_options_1242_; lean_object* v_size_1243_; lean_object* v_inheritedTraceOptions_1244_; uint8_t v_hasTrace_1245_; lean_object* v___f_1246_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; 
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
lean_inc(v_a_1240_);
lean_dec_ref(v___x_1239_);
v_vars_1241_ = lean_ctor_get(v_a_1240_, 0);
lean_inc_ref(v_vars_1241_);
lean_dec(v_a_1240_);
v_options_1242_ = lean_ctor_get(v_a_1225_, 2);
v_size_1243_ = lean_ctor_get(v_vars_1241_, 2);
lean_inc_n(v_size_1243_, 2);
lean_dec_ref(v_vars_1241_);
v_inheritedTraceOptions_1244_ = lean_ctor_get(v_a_1225_, 13);
v_hasTrace_1245_ = lean_ctor_get_uint8(v_options_1242_, sizeof(void*)*1);
lean_inc_ref(v_expr_1216_);
v___f_1246_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___lam__0), 3, 2);
lean_closure_set(v___f_1246_, 0, v_expr_1216_);
lean_closure_set(v___f_1246_, 1, v_size_1243_);
if (v_hasTrace_1245_ == 0)
{
v___y_1248_ = v_a_1217_;
v___y_1249_ = v_a_1218_;
v___y_1250_ = v_a_1219_;
v___y_1251_ = v_a_1220_;
v___y_1252_ = v_a_1221_;
v___y_1253_ = v_a_1222_;
v___y_1254_ = v_a_1223_;
v___y_1255_ = v_a_1224_;
v___y_1256_ = v_a_1225_;
v___y_1257_ = v_a_1226_;
goto v___jp_1247_;
}
else
{
lean_object* v___x_1339_; lean_object* v___x_1340_; uint8_t v___x_1341_; 
v___x_1339_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4));
v___x_1340_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7);
v___x_1341_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1244_, v_options_1242_, v___x_1340_);
if (v___x_1341_ == 0)
{
v___y_1248_ = v_a_1217_;
v___y_1249_ = v_a_1218_;
v___y_1250_ = v_a_1219_;
v___y_1251_ = v_a_1220_;
v___y_1252_ = v_a_1221_;
v___y_1253_ = v_a_1222_;
v___y_1254_ = v_a_1223_;
v___y_1255_ = v_a_1224_;
v___y_1256_ = v_a_1225_;
v___y_1257_ = v_a_1226_;
goto v___jp_1247_;
}
else
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
lean_inc_ref(v_expr_1216_);
v___x_1342_ = l_Lean_MessageData_ofExpr(v_expr_1216_);
v___x_1343_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9);
v___x_1344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1342_);
lean_ctor_set(v___x_1344_, 1, v___x_1343_);
lean_inc(v_size_1243_);
v___x_1345_ = l_Nat_reprFast(v_size_1243_);
v___x_1346_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
v___x_1347_ = l_Lean_MessageData_ofFormat(v___x_1346_);
v___x_1348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1344_);
lean_ctor_set(v___x_1348_, 1, v___x_1347_);
v___x_1349_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(v___x_1339_, v___x_1348_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_dec_ref(v___x_1349_);
v___y_1248_ = v_a_1217_;
v___y_1249_ = v_a_1218_;
v___y_1250_ = v_a_1219_;
v___y_1251_ = v_a_1220_;
v___y_1252_ = v_a_1221_;
v___y_1253_ = v_a_1222_;
v___y_1254_ = v_a_1223_;
v___y_1255_ = v_a_1224_;
v___y_1256_ = v_a_1225_;
v___y_1257_ = v_a_1226_;
goto v___jp_1247_;
}
else
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
lean_dec_ref(v___f_1246_);
lean_dec(v_size_1243_);
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
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1352_ = v___x_1349_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1349_);
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
v___jp_1247_:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_1259_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1258_, v___f_1246_, v___y_1248_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v___x_1260_; 
lean_dec_ref(v___x_1259_);
lean_inc_ref(v_expr_1216_);
v___x_1260_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_1258_, v_expr_1216_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v___x_1261_; 
lean_dec_ref(v___x_1260_);
lean_inc(v_size_1243_);
lean_inc_ref(v_expr_1216_);
v___x_1261_ = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(v_expr_1216_, v_size_1243_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v___x_1262_; 
lean_dec_ref(v___x_1261_);
lean_inc(v_size_1243_);
lean_inc_ref(v_expr_1216_);
v___x_1262_ = l_Lean_Meta_Grind_Arith_Cutsat_assertNonneg(v_expr_1216_, v_size_1243_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v___x_1263_; 
lean_dec_ref(v___x_1262_);
lean_inc(v_size_1243_);
lean_inc_ref(v_expr_1216_);
v___x_1263_ = l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds(v_expr_1216_, v_size_1243_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v___x_1264_; 
lean_dec_ref(v___x_1263_);
lean_inc_ref(v_expr_1216_);
v___x_1264_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm(v_expr_1216_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
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
lean_dec_ref(v_expr_1216_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 0, v_size_1243_);
v___x_1271_ = v___x_1267_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_size_1243_);
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
lean_inc(v_size_1243_);
v___x_1273_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_registerNonlinearOccsAt(v_expr_1216_, v_size_1243_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
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
lean_ctor_set(v___x_1275_, 0, v_size_1243_);
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_size_1243_);
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
lean_dec(v_size_1243_);
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
else
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1338_; 
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
lean_dec_ref(v_expr_1216_);
v_a_1331_ = lean_ctor_get(v___x_1259_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1333_ = v___x_1259_;
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1259_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1336_; 
if (v_isShared_1334_ == 0)
{
v___x_1336_ = v___x_1333_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_a_1331_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
}
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1365_; 
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
v_a_1358_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1360_ = v___x_1239_;
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1239_);
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
}
else
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
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
v_a_1367_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1369_ = v___x_1228_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1228_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1367_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___boxed(lean_object* v_expr_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = lean_grind_cutsat_mk_var(v_expr_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0(lean_object* v_00_u03b2_1388_, lean_object* v_x_1389_, lean_object* v_x_1390_){
_start:
{
lean_object* v___x_1391_; 
v___x_1391_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___redArg(v_x_1389_, v_x_1390_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0___boxed(lean_object* v_00_u03b2_1392_, lean_object* v_x_1393_, lean_object* v_x_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0(v_00_u03b2_1392_, v_x_1393_, v_x_1394_);
lean_dec_ref(v_x_1394_);
lean_dec_ref(v_x_1393_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1(lean_object* v_00_u03b2_1396_, lean_object* v_x_1397_, lean_object* v_x_1398_, lean_object* v_x_1399_){
_start:
{
lean_object* v___x_1400_; 
v___x_1400_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1___redArg(v_x_1397_, v_x_1398_, v_x_1399_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2(lean_object* v_cls_1401_, lean_object* v_msg_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v___x_1414_; 
v___x_1414_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___redArg(v_cls_1401_, v_msg_1402_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2___boxed(lean_object* v_cls_1415_, lean_object* v_msg_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__2(v_cls_1415_, v_msg_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec(v___y_1417_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0(lean_object* v_00_u03b2_1429_, lean_object* v_x_1430_, size_t v_x_1431_, lean_object* v_x_1432_){
_start:
{
lean_object* v___x_1433_; 
v___x_1433_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___redArg(v_x_1430_, v_x_1431_, v_x_1432_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1434_, lean_object* v_x_1435_, lean_object* v_x_1436_, lean_object* v_x_1437_){
_start:
{
size_t v_x_33667__boxed_1438_; lean_object* v_res_1439_; 
v_x_33667__boxed_1438_ = lean_unbox_usize(v_x_1436_);
lean_dec(v_x_1436_);
v_res_1439_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0(v_00_u03b2_1434_, v_x_1435_, v_x_33667__boxed_1438_, v_x_1437_);
lean_dec_ref(v_x_1437_);
lean_dec_ref(v_x_1435_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2(lean_object* v_00_u03b2_1440_, lean_object* v_x_1441_, size_t v_x_1442_, size_t v_x_1443_, lean_object* v_x_1444_, lean_object* v_x_1445_){
_start:
{
lean_object* v___x_1446_; 
v___x_1446_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___redArg(v_x_1441_, v_x_1442_, v_x_1443_, v_x_1444_, v_x_1445_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1447_, lean_object* v_x_1448_, lean_object* v_x_1449_, lean_object* v_x_1450_, lean_object* v_x_1451_, lean_object* v_x_1452_){
_start:
{
size_t v_x_33678__boxed_1453_; size_t v_x_33679__boxed_1454_; lean_object* v_res_1455_; 
v_x_33678__boxed_1453_ = lean_unbox_usize(v_x_1449_);
lean_dec(v_x_1449_);
v_x_33679__boxed_1454_ = lean_unbox_usize(v_x_1450_);
lean_dec(v_x_1450_);
v_res_1455_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2(v_00_u03b2_1447_, v_x_1448_, v_x_33678__boxed_1453_, v_x_33679__boxed_1454_, v_x_1451_, v_x_1452_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1456_, lean_object* v_keys_1457_, lean_object* v_vals_1458_, lean_object* v_heq_1459_, lean_object* v_i_1460_, lean_object* v_k_1461_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___redArg(v_keys_1457_, v_vals_1458_, v_i_1460_, v_k_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1463_, lean_object* v_keys_1464_, lean_object* v_vals_1465_, lean_object* v_heq_1466_, lean_object* v_i_1467_, lean_object* v_k_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__0_spec__0_spec__1(v_00_u03b2_1463_, v_keys_1464_, v_vals_1465_, v_heq_1466_, v_i_1467_, v_k_1468_);
lean_dec_ref(v_k_1468_);
lean_dec_ref(v_vals_1465_);
lean_dec_ref(v_keys_1464_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1470_, lean_object* v_n_1471_, lean_object* v_k_1472_, lean_object* v_v_1473_){
_start:
{
lean_object* v___x_1474_; 
v___x_1474_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4___redArg(v_n_1471_, v_k_1472_, v_v_1473_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1475_, size_t v_depth_1476_, lean_object* v_keys_1477_, lean_object* v_vals_1478_, lean_object* v_heq_1479_, lean_object* v_i_1480_, lean_object* v_entries_1481_){
_start:
{
lean_object* v___x_1482_; 
v___x_1482_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___redArg(v_depth_1476_, v_keys_1477_, v_vals_1478_, v_i_1480_, v_entries_1481_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1483_, lean_object* v_depth_1484_, lean_object* v_keys_1485_, lean_object* v_vals_1486_, lean_object* v_heq_1487_, lean_object* v_i_1488_, lean_object* v_entries_1489_){
_start:
{
size_t v_depth_boxed_1490_; lean_object* v_res_1491_; 
v_depth_boxed_1490_ = lean_unbox_usize(v_depth_1484_);
lean_dec(v_depth_1484_);
v_res_1491_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__5(v_00_u03b2_1483_, v_depth_boxed_1490_, v_keys_1485_, v_vals_1486_, v_heq_1487_, v_i_1488_, v_entries_1489_);
lean_dec_ref(v_vals_1486_);
lean_dec_ref(v_keys_1485_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_1492_, lean_object* v_x_1493_, lean_object* v_x_1494_, lean_object* v_x_1495_, lean_object* v_x_1496_){
_start:
{
lean_object* v___x_1497_; 
v___x_1497_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Cutsat_mkVarImpl_spec__1_spec__2_spec__4_spec__7___redArg(v_x_1493_, v_x_1494_, v_x_1495_, v_x_1496_);
return v___x_1497_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2(void){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1501_ = lean_box(0);
v___x_1502_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__1));
v___x_1503_ = l_Lean_mkConst(v___x_1502_, v___x_1501_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(lean_object* v_e_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_){
_start:
{
lean_object* v___x_1510_; 
lean_inc(v_a_1508_);
lean_inc_ref(v_a_1507_);
lean_inc(v_a_1506_);
lean_inc_ref(v_a_1505_);
v___x_1510_ = lean_infer_type(v_e_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v_a_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v_a_1511_ = lean_ctor_get(v___x_1510_, 0);
lean_inc(v_a_1511_);
lean_dec_ref(v___x_1510_);
v___x_1512_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2);
v___x_1513_ = l_Lean_Meta_isExprDefEq(v_a_1511_, v___x_1512_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_);
return v___x_1513_;
}
else
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1521_; 
v_a_1514_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1516_ = v___x_1510_;
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1510_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1521_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1517_ == 0)
{
v___x_1519_ = v___x_1516_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1514_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___boxed(lean_object* v_e_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(v_e_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
lean_dec(v_a_1526_);
lean_dec_ref(v_a_1525_);
lean_dec(v_a_1524_);
lean_dec_ref(v_a_1523_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt(lean_object* v_e_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_){
_start:
{
lean_object* v___x_1541_; 
v___x_1541_ = l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(v_e_1529_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___boxed(lean_object* v_e_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_Lean_Meta_Grind_Arith_Cutsat_isInt(v_e_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_);
lean_dec(v_a_1552_);
lean_dec_ref(v_a_1551_);
lean_dec(v_a_1550_);
lean_dec_ref(v_a_1549_);
lean_dec(v_a_1548_);
lean_dec_ref(v_a_1547_);
lean_dec(v_a_1546_);
lean_dec_ref(v_a_1545_);
lean_dec(v_a_1544_);
lean_dec(v_a_1543_);
return v_res_1554_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4(void){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__3));
v___x_1562_ = l_Lean_stringToMessageData(v___x_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(lean_object* v_e_1563_, uint8_t v_report_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_){
_start:
{
lean_object* v___x_1575_; 
lean_inc_ref(v_e_1563_);
v___x_1575_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1563_, v_a_1568_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1646_; 
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1578_ = v___x_1575_;
v_isShared_1579_ = v_isSharedCheck_1646_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1575_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1646_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1585_; uint8_t v___x_1586_; 
v___x_1585_ = l_Lean_Expr_cleanupAnnotations(v_a_1576_);
v___x_1586_ = l_Lean_Expr_isApp(v___x_1585_);
if (v___x_1586_ == 0)
{
lean_dec_ref(v___x_1585_);
lean_dec_ref(v_e_1563_);
goto v___jp_1580_;
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
lean_dec_ref(v_e_1563_);
goto v___jp_1580_;
}
else
{
lean_object* v_arg_1590_; lean_object* v___x_1591_; uint8_t v___x_1592_; 
v_arg_1590_ = lean_ctor_get(v___x_1588_, 1);
lean_inc_ref(v_arg_1590_);
v___x_1591_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1588_);
v___x_1592_ = l_Lean_Expr_isApp(v___x_1591_);
if (v___x_1592_ == 0)
{
lean_dec_ref(v___x_1591_);
lean_dec_ref(v_arg_1590_);
lean_dec_ref(v_arg_1587_);
lean_dec_ref(v_e_1563_);
goto v___jp_1580_;
}
else
{
lean_object* v_arg_1593_; lean_object* v___x_1594_; uint8_t v___x_1595_; 
v_arg_1593_ = lean_ctor_get(v___x_1591_, 1);
lean_inc_ref(v_arg_1593_);
v___x_1594_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1591_);
v___x_1595_ = l_Lean_Expr_isApp(v___x_1594_);
if (v___x_1595_ == 0)
{
lean_dec_ref(v___x_1594_);
lean_dec_ref(v_arg_1593_);
lean_dec_ref(v_arg_1590_);
lean_dec_ref(v_arg_1587_);
lean_dec_ref(v_e_1563_);
goto v___jp_1580_;
}
else
{
lean_object* v___x_1596_; uint8_t v___x_1597_; 
v___x_1596_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1594_);
v___x_1597_ = l_Lean_Expr_isApp(v___x_1596_);
if (v___x_1597_ == 0)
{
lean_dec_ref(v___x_1596_);
lean_dec_ref(v_arg_1593_);
lean_dec_ref(v_arg_1590_);
lean_dec_ref(v_arg_1587_);
lean_dec_ref(v_e_1563_);
goto v___jp_1580_;
}
else
{
lean_object* v___x_1598_; uint8_t v___x_1599_; 
v___x_1598_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1596_);
v___x_1599_ = l_Lean_Expr_isApp(v___x_1598_);
if (v___x_1599_ == 0)
{
lean_dec_ref(v___x_1598_);
lean_dec_ref(v_arg_1593_);
lean_dec_ref(v_arg_1590_);
lean_dec_ref(v_arg_1587_);
lean_dec_ref(v_e_1563_);
goto v___jp_1580_;
}
else
{
lean_object* v___x_1600_; lean_object* v___x_1601_; uint8_t v___x_1602_; 
v___x_1600_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1598_);
v___x_1601_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__2));
v___x_1602_ = l_Lean_Expr_isConstOf(v___x_1600_, v___x_1601_);
lean_dec_ref(v___x_1600_);
if (v___x_1602_ == 0)
{
lean_dec_ref(v_arg_1593_);
lean_dec_ref(v_arg_1590_);
lean_dec_ref(v_arg_1587_);
lean_dec_ref(v_e_1563_);
goto v___jp_1580_;
}
else
{
lean_object* v___x_1603_; 
lean_del_object(v___x_1578_);
v___x_1603_ = l_Lean_Meta_Structural_isInstHAddInt___redArg(v_arg_1593_, v_a_1568_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1637_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1606_ = v___x_1603_;
v_isShared_1607_ = v_isSharedCheck_1637_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1603_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1637_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
uint8_t v___x_1608_; 
v___x_1608_ = lean_unbox(v_a_1604_);
lean_dec(v_a_1604_);
if (v___x_1608_ == 0)
{
lean_del_object(v___x_1606_);
lean_dec_ref(v_arg_1590_);
lean_dec_ref(v_arg_1587_);
if (v_report_1564_ == 0)
{
lean_dec_ref(v_e_1563_);
goto v___jp_1572_;
}
else
{
lean_object* v___x_1609_; 
v___x_1609_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1565_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; uint8_t v___x_1611_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1610_);
lean_dec_ref(v___x_1609_);
v___x_1611_ = lean_unbox(v_a_1610_);
lean_dec(v_a_1610_);
if (v___x_1611_ == 0)
{
lean_dec_ref(v_e_1563_);
goto v___jp_1572_;
}
else
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1612_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4);
v___x_1613_ = l_Lean_indentExpr(v_e_1563_);
v___x_1614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1612_);
lean_ctor_set(v___x_1614_, 1, v___x_1613_);
v___x_1615_ = l_Lean_Meta_Sym_reportIssue(v___x_1614_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_dec_ref(v___x_1615_);
goto v___jp_1572_;
}
else
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1623_; 
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1618_ = v___x_1615_;
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1615_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1619_ == 0)
{
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1616_);
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
}
else
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
lean_dec_ref(v_e_1563_);
v_a_1624_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1626_ = v___x_1609_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1609_);
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
else
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1635_; 
lean_dec_ref(v_e_1563_);
v___x_1632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1632_, 0, v_arg_1590_);
lean_ctor_set(v___x_1632_, 1, v_arg_1587_);
v___x_1633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1632_);
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 0, v___x_1633_);
v___x_1635_ = v___x_1606_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1633_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
lean_dec_ref(v_arg_1590_);
lean_dec_ref(v_arg_1587_);
lean_dec_ref(v_e_1563_);
v_a_1638_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1640_ = v___x_1603_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1603_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
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
v___jp_1580_:
{
lean_object* v___x_1581_; lean_object* v___x_1583_; 
v___x_1581_ = lean_box(0);
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 0, v___x_1581_);
v___x_1583_ = v___x_1578_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1581_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
else
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1654_; 
lean_dec_ref(v_e_1563_);
v_a_1647_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1649_ = v___x_1575_;
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v___x_1575_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1652_; 
if (v_isShared_1650_ == 0)
{
v___x_1652_ = v___x_1649_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_a_1647_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
v___jp_1572_:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = lean_box(0);
v___x_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
return v___x_1574_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___boxed(lean_object* v_e_1655_, lean_object* v_report_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_){
_start:
{
uint8_t v_report_boxed_1664_; lean_object* v_res_1665_; 
v_report_boxed_1664_ = lean_unbox(v_report_1656_);
v_res_1665_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_1655_, v_report_boxed_1664_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_);
lean_dec(v_a_1662_);
lean_dec_ref(v_a_1661_);
lean_dec(v_a_1660_);
lean_dec_ref(v_a_1659_);
lean_dec(v_a_1658_);
lean_dec_ref(v_a_1657_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f(lean_object* v_e_1666_, uint8_t v_report_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_1666_, v_report_1667_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___boxed(lean_object* v_e_1680_, lean_object* v_report_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_){
_start:
{
uint8_t v_report_boxed_1693_; lean_object* v_res_1694_; 
v_report_boxed_1693_ = lean_unbox(v_report_1681_);
v_res_1694_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f(v_e_1680_, v_report_boxed_1693_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_);
lean_dec(v_a_1691_);
lean_dec_ref(v_a_1690_);
lean_dec(v_a_1689_);
lean_dec_ref(v_a_1688_);
lean_dec(v_a_1687_);
lean_dec_ref(v_a_1686_);
lean_dec(v_a_1685_);
lean_dec_ref(v_a_1684_);
lean_dec(v_a_1683_);
lean_dec(v_a_1682_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(lean_object* v_e_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_){
_start:
{
uint8_t v___x_1703_; lean_object* v___x_1704_; 
v___x_1703_ = 0;
v___x_1704_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_1695_, v___x_1703_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_);
if (lean_obj_tag(v___x_1704_) == 0)
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1718_; 
v_a_1705_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1707_ = v___x_1704_;
v_isShared_1708_ = v_isSharedCheck_1718_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1704_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1718_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
if (lean_obj_tag(v_a_1705_) == 0)
{
lean_object* v___x_1709_; lean_object* v___x_1711_; 
v___x_1709_ = lean_box(v___x_1703_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 0, v___x_1709_);
v___x_1711_ = v___x_1707_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v___x_1709_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
else
{
uint8_t v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1716_; 
lean_dec_ref(v_a_1705_);
v___x_1713_ = 1;
v___x_1714_ = lean_box(v___x_1713_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 0, v___x_1714_);
v___x_1716_ = v___x_1707_;
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
}
}
else
{
lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1726_; 
v_a_1719_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1721_ = v___x_1704_;
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v___x_1704_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1724_; 
if (v_isShared_1722_ == 0)
{
v___x_1724_ = v___x_1721_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_a_1719_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg___boxed(lean_object* v_e_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(v_e_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_);
lean_dec(v_a_1733_);
lean_dec_ref(v_a_1732_);
lean_dec(v_a_1731_);
lean_dec_ref(v_a_1730_);
lean_dec(v_a_1729_);
lean_dec_ref(v_a_1728_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd(lean_object* v_e_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_){
_start:
{
lean_object* v___x_1748_; 
v___x_1748_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(v_e_1736_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___boxed(lean_object* v_e_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd(v_e_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_);
lean_dec(v_a_1759_);
lean_dec_ref(v_a_1758_);
lean_dec(v_a_1757_);
lean_dec_ref(v_a_1756_);
lean_dec(v_a_1755_);
lean_dec_ref(v_a_1754_);
lean_dec(v_a_1753_);
lean_dec_ref(v_a_1752_);
lean_dec(v_a_1751_);
lean_dec(v_a_1750_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(lean_object* v_e_1762_, uint8_t v_report_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_){
_start:
{
lean_object* v___x_1774_; 
lean_inc_ref(v_e_1762_);
v___x_1774_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1762_, v_a_1767_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v_a_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1866_; 
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1777_ = v___x_1774_;
v_isShared_1778_ = v_isSharedCheck_1866_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_a_1775_);
lean_dec(v___x_1774_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1866_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1784_; uint8_t v___x_1785_; 
v___x_1784_ = l_Lean_Expr_cleanupAnnotations(v_a_1775_);
v___x_1785_ = l_Lean_Expr_isApp(v___x_1784_);
if (v___x_1785_ == 0)
{
lean_dec_ref(v___x_1784_);
lean_dec_ref(v_e_1762_);
goto v___jp_1779_;
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
lean_dec_ref(v_e_1762_);
goto v___jp_1779_;
}
else
{
lean_object* v_arg_1789_; lean_object* v___x_1790_; uint8_t v___x_1791_; 
v_arg_1789_ = lean_ctor_get(v___x_1787_, 1);
lean_inc_ref(v_arg_1789_);
v___x_1790_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1787_);
v___x_1791_ = l_Lean_Expr_isApp(v___x_1790_);
if (v___x_1791_ == 0)
{
lean_dec_ref(v___x_1790_);
lean_dec_ref(v_arg_1789_);
lean_dec_ref(v_arg_1786_);
lean_dec_ref(v_e_1762_);
goto v___jp_1779_;
}
else
{
lean_object* v_arg_1792_; lean_object* v___x_1793_; uint8_t v___x_1794_; 
v_arg_1792_ = lean_ctor_get(v___x_1790_, 1);
lean_inc_ref(v_arg_1792_);
v___x_1793_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1790_);
v___x_1794_ = l_Lean_Expr_isApp(v___x_1793_);
if (v___x_1794_ == 0)
{
lean_dec_ref(v___x_1793_);
lean_dec_ref(v_arg_1792_);
lean_dec_ref(v_arg_1789_);
lean_dec_ref(v_arg_1786_);
lean_dec_ref(v_e_1762_);
goto v___jp_1779_;
}
else
{
lean_object* v___x_1795_; uint8_t v___x_1796_; 
v___x_1795_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1793_);
v___x_1796_ = l_Lean_Expr_isApp(v___x_1795_);
if (v___x_1796_ == 0)
{
lean_dec_ref(v___x_1795_);
lean_dec_ref(v_arg_1792_);
lean_dec_ref(v_arg_1789_);
lean_dec_ref(v_arg_1786_);
lean_dec_ref(v_e_1762_);
goto v___jp_1779_;
}
else
{
lean_object* v___x_1797_; uint8_t v___x_1798_; 
v___x_1797_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1795_);
v___x_1798_ = l_Lean_Expr_isApp(v___x_1797_);
if (v___x_1798_ == 0)
{
lean_dec_ref(v___x_1797_);
lean_dec_ref(v_arg_1792_);
lean_dec_ref(v_arg_1789_);
lean_dec_ref(v_arg_1786_);
lean_dec_ref(v_e_1762_);
goto v___jp_1779_;
}
else
{
lean_object* v___x_1799_; lean_object* v___x_1800_; uint8_t v___x_1801_; 
v___x_1799_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1797_);
v___x_1800_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_isNonlinearTerm___closed__11));
v___x_1801_ = l_Lean_Expr_isConstOf(v___x_1799_, v___x_1800_);
lean_dec_ref(v___x_1799_);
if (v___x_1801_ == 0)
{
lean_dec_ref(v_arg_1792_);
lean_dec_ref(v_arg_1789_);
lean_dec_ref(v_arg_1786_);
lean_dec_ref(v_e_1762_);
goto v___jp_1779_;
}
else
{
lean_object* v___x_1802_; 
lean_del_object(v___x_1777_);
v___x_1802_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_1792_, v_a_1767_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_a_1803_; uint8_t v___x_1804_; 
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
lean_inc(v_a_1803_);
lean_dec_ref(v___x_1802_);
v___x_1804_ = lean_unbox(v_a_1803_);
lean_dec(v_a_1803_);
if (v___x_1804_ == 0)
{
lean_dec_ref(v_arg_1789_);
lean_dec_ref(v_arg_1786_);
if (v_report_1763_ == 0)
{
lean_dec_ref(v_e_1762_);
goto v___jp_1771_;
}
else
{
lean_object* v___x_1805_; 
v___x_1805_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1764_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_a_1806_; uint8_t v___x_1807_; 
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
lean_inc(v_a_1806_);
lean_dec_ref(v___x_1805_);
v___x_1807_ = lean_unbox(v_a_1806_);
lean_dec(v_a_1806_);
if (v___x_1807_ == 0)
{
lean_dec_ref(v_e_1762_);
goto v___jp_1771_;
}
else
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1808_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4);
v___x_1809_ = l_Lean_indentExpr(v_e_1762_);
v___x_1810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1808_);
lean_ctor_set(v___x_1810_, 1, v___x_1809_);
v___x_1811_ = l_Lean_Meta_Sym_reportIssue(v___x_1810_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_dec_ref(v___x_1811_);
goto v___jp_1771_;
}
else
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1819_; 
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1814_ = v___x_1811_;
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1811_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1815_ == 0)
{
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1812_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
}
else
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1827_; 
lean_dec_ref(v_e_1762_);
v_a_1820_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1822_ = v___x_1805_;
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1805_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
if (v_isShared_1823_ == 0)
{
v___x_1825_ = v___x_1822_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1820_);
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
}
else
{
lean_object* v___x_1828_; 
lean_dec_ref(v_e_1762_);
v___x_1828_ = l_Lean_Meta_getIntValue_x3f(v_arg_1789_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1849_; 
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1831_ = v___x_1828_;
v_isShared_1832_ = v_isSharedCheck_1849_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1828_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1849_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
if (lean_obj_tag(v_a_1829_) == 1)
{
lean_object* v_val_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1844_; 
v_val_1833_ = lean_ctor_get(v_a_1829_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v_a_1829_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1835_ = v_a_1829_;
v_isShared_1836_ = v_isSharedCheck_1844_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_val_1833_);
lean_dec(v_a_1829_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1844_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1837_; lean_object* v___x_1839_; 
v___x_1837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1837_, 0, v_val_1833_);
lean_ctor_set(v___x_1837_, 1, v_arg_1786_);
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 0, v___x_1837_);
v___x_1839_ = v___x_1835_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v___x_1837_);
v___x_1839_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
lean_object* v___x_1841_; 
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v___x_1839_);
v___x_1841_ = v___x_1831_;
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
lean_object* v___x_1845_; lean_object* v___x_1847_; 
lean_dec(v_a_1829_);
lean_dec_ref(v_arg_1786_);
v___x_1845_ = lean_box(0);
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v___x_1845_);
v___x_1847_ = v___x_1831_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1845_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
}
else
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1857_; 
lean_dec_ref(v_arg_1786_);
v_a_1850_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1852_ = v___x_1828_;
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1828_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1855_; 
if (v_isShared_1853_ == 0)
{
v___x_1855_ = v___x_1852_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_a_1850_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
}
}
else
{
lean_object* v_a_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1865_; 
lean_dec_ref(v_arg_1789_);
lean_dec_ref(v_arg_1786_);
lean_dec_ref(v_e_1762_);
v_a_1858_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1860_ = v___x_1802_;
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_a_1858_);
lean_dec(v___x_1802_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1863_; 
if (v_isShared_1861_ == 0)
{
v___x_1863_ = v___x_1860_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_a_1858_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
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
v___jp_1779_:
{
lean_object* v___x_1780_; lean_object* v___x_1782_; 
v___x_1780_ = lean_box(0);
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 0, v___x_1780_);
v___x_1782_ = v___x_1777_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v___x_1780_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
}
else
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1874_; 
lean_dec_ref(v_e_1762_);
v_a_1867_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1869_ = v___x_1774_;
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1774_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1872_; 
if (v_isShared_1870_ == 0)
{
v___x_1872_ = v___x_1869_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_a_1867_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
v___jp_1771_:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1772_ = lean_box(0);
v___x_1773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1772_);
return v___x_1773_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg___boxed(lean_object* v_e_1875_, lean_object* v_report_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_){
_start:
{
uint8_t v_report_boxed_1884_; lean_object* v_res_1885_; 
v_report_boxed_1884_ = lean_unbox(v_report_1876_);
v_res_1885_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1875_, v_report_boxed_1884_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_);
lean_dec(v_a_1882_);
lean_dec_ref(v_a_1881_);
lean_dec(v_a_1880_);
lean_dec_ref(v_a_1879_);
lean_dec(v_a_1878_);
lean_dec_ref(v_a_1877_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f(lean_object* v_e_1886_, uint8_t v_report_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_){
_start:
{
lean_object* v___x_1899_; 
v___x_1899_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1886_, v_report_1887_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___boxed(lean_object* v_e_1900_, lean_object* v_report_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_){
_start:
{
uint8_t v_report_boxed_1913_; lean_object* v_res_1914_; 
v_report_boxed_1913_ = lean_unbox(v_report_1901_);
v_res_1914_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f(v_e_1900_, v_report_boxed_1913_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
lean_dec(v_a_1911_);
lean_dec_ref(v_a_1910_);
lean_dec(v_a_1909_);
lean_dec_ref(v_a_1908_);
lean_dec(v_a_1907_);
lean_dec_ref(v_a_1906_);
lean_dec(v_a_1905_);
lean_dec_ref(v_a_1904_);
lean_dec(v_a_1903_);
lean_dec(v_a_1902_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(lean_object* v_e_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_){
_start:
{
uint8_t v___x_1923_; lean_object* v___x_1924_; 
v___x_1923_ = 0;
v___x_1924_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1915_, v___x_1923_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1938_; 
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1927_ = v___x_1924_;
v_isShared_1928_ = v_isSharedCheck_1938_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1924_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1938_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
if (lean_obj_tag(v_a_1925_) == 0)
{
lean_object* v___x_1929_; lean_object* v___x_1931_; 
v___x_1929_ = lean_box(v___x_1923_);
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 0, v___x_1929_);
v___x_1931_ = v___x_1927_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v___x_1929_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
else
{
uint8_t v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1936_; 
lean_dec_ref(v_a_1925_);
v___x_1933_ = 1;
v___x_1934_ = lean_box(v___x_1933_);
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 0, v___x_1934_);
v___x_1936_ = v___x_1927_;
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
}
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
v_a_1939_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1924_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1924_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg___boxed(lean_object* v_e_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(v_e_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
lean_dec(v_a_1953_);
lean_dec_ref(v_a_1952_);
lean_dec(v_a_1951_);
lean_dec_ref(v_a_1950_);
lean_dec(v_a_1949_);
lean_dec_ref(v_a_1948_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul(lean_object* v_e_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_){
_start:
{
lean_object* v___x_1968_; 
v___x_1968_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(v_e_1956_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___boxed(lean_object* v_e_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul(v_e_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_);
lean_dec(v_a_1979_);
lean_dec_ref(v_a_1978_);
lean_dec(v_a_1977_);
lean_dec_ref(v_a_1976_);
lean_dec(v_a_1975_);
lean_dec_ref(v_a_1974_);
lean_dec(v_a_1973_);
lean_dec_ref(v_a_1972_);
lean_dec(v_a_1971_);
lean_dec(v_a_1970_);
return v_res_1981_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0(void){
_start:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1982_ = lean_unsigned_to_nat(1u);
v___x_1983_ = lean_nat_to_int(v___x_1982_);
return v___x_1983_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2(void){
_start:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1985_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__1));
v___x_1986_ = l_Lean_stringToMessageData(v___x_1985_);
return v___x_1986_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4(void){
_start:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1988_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__3));
v___x_1989_ = l_Lean_stringToMessageData(v___x_1988_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(lean_object* v_e_1990_, lean_object* v_p_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_){
_start:
{
lean_object* v___y_2004_; lean_object* v___y_2005_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; uint8_t v___x_2033_; lean_object* v___x_2034_; 
v___x_2033_ = 1;
lean_inc_ref(v_e_1990_);
v___x_2034_ = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(v_e_1990_, v___x_2033_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v_a_2035_; 
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_a_2035_);
lean_dec_ref(v___x_2034_);
if (lean_obj_tag(v_a_2035_) == 1)
{
lean_object* v_val_2036_; lean_object* v_fst_2037_; lean_object* v_snd_2038_; lean_object* v___x_2039_; 
lean_dec_ref(v_e_1990_);
v_val_2036_ = lean_ctor_get(v_a_2035_, 0);
lean_inc(v_val_2036_);
lean_dec_ref(v_a_2035_);
v_fst_2037_ = lean_ctor_get(v_val_2036_, 0);
lean_inc(v_fst_2037_);
v_snd_2038_ = lean_ctor_get(v_val_2036_, 1);
lean_inc(v_snd_2038_);
lean_dec(v_val_2036_);
lean_inc(v_a_2001_);
lean_inc_ref(v_a_2000_);
lean_inc(v_a_1999_);
lean_inc_ref(v_a_1998_);
lean_inc(v_a_1997_);
lean_inc_ref(v_a_1996_);
lean_inc(v_a_1995_);
lean_inc_ref(v_a_1994_);
lean_inc(v_a_1993_);
lean_inc(v_a_1992_);
v___x_2039_ = lean_grind_cutsat_mk_var(v_snd_2038_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2048_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2042_ = v___x_2039_;
v_isShared_2043_ = v_isSharedCheck_2048_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2039_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2048_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2044_; lean_object* v___x_2046_; 
v___x_2044_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2044_, 0, v_fst_2037_);
lean_ctor_set(v___x_2044_, 1, v_a_2040_);
lean_ctor_set(v___x_2044_, 2, v_p_1991_);
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 0, v___x_2044_);
v___x_2046_ = v___x_2042_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2044_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
else
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2056_; 
lean_dec(v_fst_2037_);
lean_dec_ref(v_p_1991_);
v_a_2049_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2051_ = v___x_2039_;
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2039_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2049_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
else
{
lean_object* v___x_2057_; 
lean_dec(v_a_2035_);
lean_inc_ref(v_e_1990_);
v___x_2057_ = l_Lean_Meta_getIntValue_x3f(v_e_1990_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2099_; 
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2060_ = v___x_2057_;
v_isShared_2061_ = v_isSharedCheck_2099_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2057_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2099_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
if (lean_obj_tag(v_a_2058_) == 1)
{
lean_object* v_val_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2098_; 
v_val_2062_ = lean_ctor_get(v_a_2058_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v_a_2058_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2064_ = v_a_2058_;
v_isShared_2065_ = v_isSharedCheck_2098_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_val_2062_);
lean_dec(v_a_2058_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2098_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
uint8_t v___x_2066_; 
v___x_2066_ = l_Int_Linear_Poly_isZero(v_p_1991_);
if (v___x_2066_ == 0)
{
lean_object* v___x_2067_; 
lean_del_object(v___x_2064_);
lean_dec(v_val_2062_);
lean_del_object(v___x_2060_);
v___x_2067_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1996_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v_a_2068_; uint8_t v___x_2069_; 
v_a_2068_ = lean_ctor_get(v___x_2067_, 0);
lean_inc(v_a_2068_);
lean_dec_ref(v___x_2067_);
v___x_2069_ = lean_unbox(v_a_2068_);
lean_dec(v_a_2068_);
if (v___x_2069_ == 0)
{
v___y_2004_ = v_a_1992_;
v___y_2005_ = v_a_1993_;
v___y_2006_ = v_a_1994_;
v___y_2007_ = v_a_1995_;
v___y_2008_ = v_a_1996_;
v___y_2009_ = v_a_1997_;
v___y_2010_ = v_a_1998_;
v___y_2011_ = v_a_1999_;
v___y_2012_ = v_a_2000_;
v___y_2013_ = v_a_2001_;
goto v___jp_2003_;
}
else
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2070_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2, &l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2);
lean_inc_ref(v_e_1990_);
v___x_2071_ = l_Lean_indentExpr(v_e_1990_);
v___x_2072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2070_);
lean_ctor_set(v___x_2072_, 1, v___x_2071_);
v___x_2073_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4, &l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4);
v___x_2074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2072_);
lean_ctor_set(v___x_2074_, 1, v___x_2073_);
v___x_2075_ = l_Lean_Meta_Sym_reportIssue(v___x_2074_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_dec_ref(v___x_2075_);
v___y_2004_ = v_a_1992_;
v___y_2005_ = v_a_1993_;
v___y_2006_ = v_a_1994_;
v___y_2007_ = v_a_1995_;
v___y_2008_ = v_a_1996_;
v___y_2009_ = v_a_1997_;
v___y_2010_ = v_a_1998_;
v___y_2011_ = v_a_1999_;
v___y_2012_ = v_a_2000_;
v___y_2013_ = v_a_2001_;
goto v___jp_2003_;
}
else
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
lean_dec_ref(v_p_1991_);
lean_dec_ref(v_e_1990_);
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2078_ = v___x_2075_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2075_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_a_2076_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
}
}
else
{
lean_object* v_a_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2091_; 
lean_dec_ref(v_p_1991_);
lean_dec_ref(v_e_1990_);
v_a_2084_ = lean_ctor_get(v___x_2067_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2086_ = v___x_2067_;
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_a_2084_);
lean_dec(v___x_2067_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2089_; 
if (v_isShared_2087_ == 0)
{
v___x_2089_ = v___x_2086_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_a_2084_);
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
else
{
lean_object* v___x_2093_; 
lean_dec_ref(v_p_1991_);
lean_dec_ref(v_e_1990_);
if (v_isShared_2065_ == 0)
{
lean_ctor_set_tag(v___x_2064_, 0);
v___x_2093_ = v___x_2064_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_val_2062_);
v___x_2093_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
lean_object* v___x_2095_; 
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 0, v___x_2093_);
v___x_2095_ = v___x_2060_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_2093_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
}
}
else
{
lean_del_object(v___x_2060_);
lean_dec(v_a_2058_);
v___y_2004_ = v_a_1992_;
v___y_2005_ = v_a_1993_;
v___y_2006_ = v_a_1994_;
v___y_2007_ = v_a_1995_;
v___y_2008_ = v_a_1996_;
v___y_2009_ = v_a_1997_;
v___y_2010_ = v_a_1998_;
v___y_2011_ = v_a_1999_;
v___y_2012_ = v_a_2000_;
v___y_2013_ = v_a_2001_;
goto v___jp_2003_;
}
}
}
else
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2107_; 
lean_dec_ref(v_p_1991_);
lean_dec_ref(v_e_1990_);
v_a_2100_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2102_ = v___x_2057_;
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2057_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2105_; 
if (v_isShared_2103_ == 0)
{
v___x_2105_ = v___x_2102_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_a_2100_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
}
}
else
{
lean_object* v_a_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2115_; 
lean_dec_ref(v_p_1991_);
lean_dec_ref(v_e_1990_);
v_a_2108_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2110_ = v___x_2034_;
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_a_2108_);
lean_dec(v___x_2034_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2113_; 
if (v_isShared_2111_ == 0)
{
v___x_2113_ = v___x_2110_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_a_2108_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
v___jp_2003_:
{
lean_object* v___x_2014_; 
lean_inc(v___y_2013_);
lean_inc_ref(v___y_2012_);
lean_inc(v___y_2011_);
lean_inc_ref(v___y_2010_);
lean_inc(v___y_2009_);
lean_inc_ref(v___y_2008_);
lean_inc(v___y_2007_);
lean_inc_ref(v___y_2006_);
lean_inc(v___y_2005_);
lean_inc(v___y_2004_);
v___x_2014_ = lean_grind_cutsat_mk_var(v_e_1990_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2024_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2017_ = v___x_2014_;
v_isShared_2018_ = v_isSharedCheck_2024_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_2014_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2024_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2022_; 
v___x_2019_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0);
v___x_2020_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2019_);
lean_ctor_set(v___x_2020_, 1, v_a_2015_);
lean_ctor_set(v___x_2020_, 2, v_p_1991_);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 0, v___x_2020_);
v___x_2022_ = v___x_2017_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2020_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
else
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2032_; 
lean_dec_ref(v_p_1991_);
v_a_2025_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2027_ = v___x_2014_;
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_2014_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
if (v_isShared_2028_ == 0)
{
v___x_2030_ = v___x_2027_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_a_2025_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___boxed(lean_object* v_e_2116_, lean_object* v_p_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_e_2116_, v_p_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_);
lean_dec(v_a_2127_);
lean_dec_ref(v_a_2126_);
lean_dec(v_a_2125_);
lean_dec_ref(v_a_2124_);
lean_dec(v_a_2123_);
lean_dec_ref(v_a_2122_);
lean_dec(v_a_2121_);
lean_dec_ref(v_a_2120_);
lean_dec(v_a_2119_);
lean_dec(v_a_2118_);
return v_res_2129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go(lean_object* v_e_2130_, lean_object* v_p_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_){
_start:
{
uint8_t v___x_2143_; lean_object* v___x_2144_; 
v___x_2143_ = 1;
lean_inc_ref(v_e_2130_);
v___x_2144_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_2130_, v___x_2143_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref(v___x_2144_);
if (lean_obj_tag(v_a_2145_) == 1)
{
lean_object* v_val_2146_; lean_object* v_fst_2147_; lean_object* v_snd_2148_; lean_object* v___x_2149_; 
lean_dec_ref(v_e_2130_);
v_val_2146_ = lean_ctor_get(v_a_2145_, 0);
lean_inc(v_val_2146_);
lean_dec_ref(v_a_2145_);
v_fst_2147_ = lean_ctor_get(v_val_2146_, 0);
lean_inc(v_fst_2147_);
v_snd_2148_ = lean_ctor_get(v_val_2146_, 1);
lean_inc(v_snd_2148_);
lean_dec(v_val_2146_);
v___x_2149_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_snd_2148_, v_p_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_a_2150_);
lean_dec_ref(v___x_2149_);
v_e_2130_ = v_fst_2147_;
v_p_2131_ = v_a_2150_;
goto _start;
}
else
{
lean_dec(v_fst_2147_);
return v___x_2149_;
}
}
else
{
lean_object* v___x_2152_; 
lean_dec(v_a_2145_);
v___x_2152_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_e_2130_, v_p_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
return v___x_2152_;
}
}
else
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2160_; 
lean_dec_ref(v_p_2131_);
lean_dec_ref(v_e_2130_);
v_a_2153_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2155_ = v___x_2144_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2144_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2153_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go___boxed(lean_object* v_e_2161_, lean_object* v_p_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go(v_e_2161_, v_p_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
lean_dec(v_a_2172_);
lean_dec_ref(v_a_2171_);
lean_dec(v_a_2170_);
lean_dec_ref(v_a_2169_);
lean_dec(v_a_2168_);
lean_dec_ref(v_a_2167_);
lean_dec(v_a_2166_);
lean_dec_ref(v_a_2165_);
lean_dec(v_a_2164_);
lean_dec(v_a_2163_);
return v_res_2174_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0(void){
_start:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2175_ = lean_unsigned_to_nat(0u);
v___x_2176_ = lean_nat_to_int(v___x_2175_);
return v___x_2176_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1(void){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2177_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0);
v___x_2178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2178_, 0, v___x_2177_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly(lean_object* v_e_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_){
_start:
{
uint8_t v___x_2191_; lean_object* v___x_2192_; 
v___x_2191_ = 1;
lean_inc_ref(v_e_2179_);
v___x_2192_ = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(v_e_2179_, v___x_2191_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v_a_2193_; 
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_a_2193_);
lean_dec_ref(v___x_2192_);
if (lean_obj_tag(v_a_2193_) == 1)
{
lean_object* v_val_2194_; lean_object* v_fst_2195_; lean_object* v_snd_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
lean_dec_ref(v_e_2179_);
v_val_2194_ = lean_ctor_get(v_a_2193_, 0);
lean_inc(v_val_2194_);
lean_dec_ref(v_a_2193_);
v_fst_2195_ = lean_ctor_get(v_val_2194_, 0);
lean_inc(v_fst_2195_);
v_snd_2196_ = lean_ctor_get(v_val_2194_, 1);
lean_inc(v_snd_2196_);
lean_dec(v_val_2194_);
v___x_2197_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1);
v___x_2198_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_snd_2196_, v___x_2197_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; lean_object* v___x_2200_; 
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_a_2199_);
lean_dec_ref(v___x_2198_);
v___x_2200_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var_0__Lean_Meta_Grind_Arith_Cutsat_toPoly_go(v_fst_2195_, v_a_2199_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_);
return v___x_2200_;
}
else
{
lean_dec(v_fst_2195_);
return v___x_2198_;
}
}
else
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
lean_dec(v_a_2193_);
v___x_2201_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1);
v___x_2202_ = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(v_e_2179_, v___x_2201_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_, v_a_2189_);
return v___x_2202_;
}
}
else
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2210_; 
lean_dec_ref(v_e_2179_);
v_a_2203_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2205_ = v___x_2192_;
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v___x_2192_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2208_; 
if (v_isShared_2206_ == 0)
{
v___x_2208_ = v___x_2205_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_a_2203_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly___boxed(lean_object* v_e_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_e_2211_, v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_);
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
return v_res_2223_;
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
