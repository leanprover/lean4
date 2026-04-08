// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Arith.Int.Basic
// Imports: public import Init.Data.Int.Linear public import Lean.Util.SortExprs public import Lean.Meta.IntInstTesters public import Lean.Meta.AppBuilder public import Lean.Meta.KExprMap public import Lean.Data.RArray import Lean.Meta.LitValues
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
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DefEq_isInstLEInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_KExprMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_KExprMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DefEq_isInstHAddInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DefEq_isInstHSubInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DefEq_isInstHMulInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DefEq_isInstAddInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DefEq_isInstSubInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DefEq_isInstMulInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DefEq_isInstNegInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DefEq_isInstLTInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkIntAdd(lean_object*, lean_object*);
lean_object* l_Lean_mkIntSub(lean_object*, lean_object*);
lean_object* l_Lean_mkIntNeg(lean_object*);
lean_object* l_Lean_mkIntMul(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DefEq_isInstDvdInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_sortExprs(lean_object*, uint8_t);
lean_object* l_Lean_mkIntLit(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_RArray_toExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RArray_ofArray___redArg(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_applyPerm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_applyPerm___boxed(lean_object*, lean_object*);
static const lean_string_object l_Int_Linear_instReprPoly__lean_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Int.Linear.Poly.num"};
static const lean_object* l_Int_Linear_instReprPoly__lean_repr___closed__0 = (const lean_object*)&l_Int_Linear_instReprPoly__lean_repr___closed__0_value;
static const lean_ctor_object l_Int_Linear_instReprPoly__lean_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Int_Linear_instReprPoly__lean_repr___closed__0_value)}};
static const lean_object* l_Int_Linear_instReprPoly__lean_repr___closed__1 = (const lean_object*)&l_Int_Linear_instReprPoly__lean_repr___closed__1_value;
static const lean_ctor_object l_Int_Linear_instReprPoly__lean_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Int_Linear_instReprPoly__lean_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Int_Linear_instReprPoly__lean_repr___closed__2 = (const lean_object*)&l_Int_Linear_instReprPoly__lean_repr___closed__2_value;
static lean_once_cell_t l_Int_Linear_instReprPoly__lean_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_Linear_instReprPoly__lean_repr___closed__3;
static const lean_string_object l_Int_Linear_instReprPoly__lean_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Int.Linear.Poly.add"};
static const lean_object* l_Int_Linear_instReprPoly__lean_repr___closed__4 = (const lean_object*)&l_Int_Linear_instReprPoly__lean_repr___closed__4_value;
static const lean_ctor_object l_Int_Linear_instReprPoly__lean_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Int_Linear_instReprPoly__lean_repr___closed__4_value)}};
static const lean_object* l_Int_Linear_instReprPoly__lean_repr___closed__5 = (const lean_object*)&l_Int_Linear_instReprPoly__lean_repr___closed__5_value;
static const lean_ctor_object l_Int_Linear_instReprPoly__lean_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Int_Linear_instReprPoly__lean_repr___closed__5_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Int_Linear_instReprPoly__lean_repr___closed__6 = (const lean_object*)&l_Int_Linear_instReprPoly__lean_repr___closed__6_value;
LEAN_EXPORT lean_object* l_Int_Linear_instReprPoly__lean_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_instReprPoly__lean_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Int_Linear_instReprPoly__lean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_Linear_instReprPoly__lean_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int_Linear_instReprPoly__lean___closed__0 = (const lean_object*)&l_Int_Linear_instReprPoly__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Int_Linear_instReprPoly__lean = (const lean_object*)&l_Int_Linear_instReprPoly__lean___closed__0_value;
static const lean_string_object l_Int_Linear_instReprExpr__lean_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Int.Linear.Expr.num"};
static const lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__0 = (const lean_object*)&l_Int_Linear_instReprExpr__lean_repr___closed__0_value;
static const lean_ctor_object l_Int_Linear_instReprExpr__lean_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Int_Linear_instReprExpr__lean_repr___closed__0_value)}};
static const lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__1 = (const lean_object*)&l_Int_Linear_instReprExpr__lean_repr___closed__1_value;
static const lean_ctor_object l_Int_Linear_instReprExpr__lean_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Int_Linear_instReprExpr__lean_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__2 = (const lean_object*)&l_Int_Linear_instReprExpr__lean_repr___closed__2_value;
static const lean_string_object l_Int_Linear_instReprExpr__lean_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Int.Linear.Expr.var"};
static const lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__3 = (const lean_object*)&l_Int_Linear_instReprExpr__lean_repr___closed__3_value;
static const lean_ctor_object l_Int_Linear_instReprExpr__lean_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Int_Linear_instReprExpr__lean_repr___closed__3_value)}};
static const lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__4 = (const lean_object*)&l_Int_Linear_instReprExpr__lean_repr___closed__4_value;
static const lean_ctor_object l_Int_Linear_instReprExpr__lean_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Int_Linear_instReprExpr__lean_repr___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__5 = (const lean_object*)&l_Int_Linear_instReprExpr__lean_repr___closed__5_value;
static const lean_string_object l_Int_Linear_instReprExpr__lean_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Int.Linear.Expr.add"};
static const lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__6 = (const lean_object*)&l_Int_Linear_instReprExpr__lean_repr___closed__6_value;
static const lean_ctor_object l_Int_Linear_instReprExpr__lean_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Int_Linear_instReprExpr__lean_repr___closed__6_value)}};
static const lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__7 = (const lean_object*)&l_Int_Linear_instReprExpr__lean_repr___closed__7_value;
static const lean_ctor_object l_Int_Linear_instReprExpr__lean_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Int_Linear_instReprExpr__lean_repr___closed__7_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__8 = (const lean_object*)&l_Int_Linear_instReprExpr__lean_repr___closed__8_value;
static const lean_string_object l_Int_Linear_instReprExpr__lean_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Int.Linear.Expr.sub"};
static const lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__9 = (const lean_object*)&l_Int_Linear_instReprExpr__lean_repr___closed__9_value;
static const lean_ctor_object l_Int_Linear_instReprExpr__lean_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Int_Linear_instReprExpr__lean_repr___closed__9_value)}};
static const lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__10 = (const lean_object*)&l_Int_Linear_instReprExpr__lean_repr___closed__10_value;
static const lean_ctor_object l_Int_Linear_instReprExpr__lean_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Int_Linear_instReprExpr__lean_repr___closed__10_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__11 = (const lean_object*)&l_Int_Linear_instReprExpr__lean_repr___closed__11_value;
static const lean_string_object l_Int_Linear_instReprExpr__lean_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Int.Linear.Expr.neg"};
static const lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__12 = (const lean_object*)&l_Int_Linear_instReprExpr__lean_repr___closed__12_value;
static const lean_ctor_object l_Int_Linear_instReprExpr__lean_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Int_Linear_instReprExpr__lean_repr___closed__12_value)}};
static const lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__13 = (const lean_object*)&l_Int_Linear_instReprExpr__lean_repr___closed__13_value;
static const lean_ctor_object l_Int_Linear_instReprExpr__lean_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Int_Linear_instReprExpr__lean_repr___closed__13_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__14 = (const lean_object*)&l_Int_Linear_instReprExpr__lean_repr___closed__14_value;
static const lean_string_object l_Int_Linear_instReprExpr__lean_repr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Int.Linear.Expr.mulL"};
static const lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__15 = (const lean_object*)&l_Int_Linear_instReprExpr__lean_repr___closed__15_value;
static const lean_ctor_object l_Int_Linear_instReprExpr__lean_repr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Int_Linear_instReprExpr__lean_repr___closed__15_value)}};
static const lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__16 = (const lean_object*)&l_Int_Linear_instReprExpr__lean_repr___closed__16_value;
static const lean_ctor_object l_Int_Linear_instReprExpr__lean_repr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Int_Linear_instReprExpr__lean_repr___closed__16_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__17 = (const lean_object*)&l_Int_Linear_instReprExpr__lean_repr___closed__17_value;
static const lean_string_object l_Int_Linear_instReprExpr__lean_repr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Int.Linear.Expr.mulR"};
static const lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__18 = (const lean_object*)&l_Int_Linear_instReprExpr__lean_repr___closed__18_value;
static const lean_ctor_object l_Int_Linear_instReprExpr__lean_repr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Int_Linear_instReprExpr__lean_repr___closed__18_value)}};
static const lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__19 = (const lean_object*)&l_Int_Linear_instReprExpr__lean_repr___closed__19_value;
static const lean_ctor_object l_Int_Linear_instReprExpr__lean_repr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Int_Linear_instReprExpr__lean_repr___closed__19_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__20 = (const lean_object*)&l_Int_Linear_instReprExpr__lean_repr___closed__20_value;
LEAN_EXPORT lean_object* l_Int_Linear_instReprExpr__lean_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_instReprExpr__lean_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Int_Linear_instReprExpr__lean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_Linear_instReprExpr__lean_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int_Linear_instReprExpr__lean___closed__0 = (const lean_object*)&l_Int_Linear_instReprExpr__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Int_Linear_instReprExpr__lean = (const lean_object*)&l_Int_Linear_instReprExpr__lean___closed__0_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linear"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Poly"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__2_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__2_value),LEAN_SCALAR_PTR_LITERAL(102, 184, 140, 227, 255, 85, 86, 248)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__3_value),LEAN_SCALAR_PTR_LITERAL(18, 157, 224, 87, 89, 58, 239, 103)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__5;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__6 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__6_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__6_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__7_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__8 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__9;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__10;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instNegInt"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__15_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14_value),LEAN_SCALAR_PTR_LITERAL(217, 109, 233, 1, 211, 122, 77, 88)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__15 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__15_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "add"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__18_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__18_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__2_value),LEAN_SCALAR_PTR_LITERAL(102, 184, 140, 227, 255, 85, 86, 248)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__18_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_value),LEAN_SCALAR_PTR_LITERAL(195, 221, 166, 180, 111, 219, 180, 121)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__18 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__18_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__19;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly(lean_object*);
static const lean_closure_object l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Simp_Arith_Int_ofPoly, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__2_value),LEAN_SCALAR_PTR_LITERAL(102, 184, 140, 227, 255, 85, 86, 248)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__2;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprPoly;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Expr"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 62, 222, 142, 91, 249, 126, 146)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 166, 107, 26, 87, 46, 244, 220)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__2;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "var"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 62, 222, 142, 91, 249, 126, 146)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(91, 96, 149, 78, 42, 27, 109, 180)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__5;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 62, 222, 142, 91, 249, 126, 146)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_value),LEAN_SCALAR_PTR_LITERAL(175, 177, 222, 112, 100, 91, 249, 82)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__7;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sub"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__8 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 62, 222, 142, 91, 249, 126, 146)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__8_value),LEAN_SCALAR_PTR_LITERAL(204, 113, 82, 25, 216, 242, 239, 252)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__10;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 62, 222, 142, 91, 249, 126, 146)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__7_value),LEAN_SCALAR_PTR_LITERAL(109, 233, 73, 173, 185, 81, 227, 211)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__12;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "mulL"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__13 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 62, 222, 142, 91, 249, 126, 146)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__13_value),LEAN_SCALAR_PTR_LITERAL(37, 221, 171, 65, 105, 141, 44, 155)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__15;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "mulR"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__16 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 62, 222, 142, 91, 249, 126, 146)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__16_value),LEAN_SCALAR_PTR_LITERAL(72, 41, 111, 163, 84, 18, 140, 30)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__18;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(lean_object*);
static const lean_closure_object l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Simp_Arith_Int_ofLinearExpr, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 62, 222, 142, 91, 249, 126, 146)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__2;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprExpr;
LEAN_EXPORT lean_object* l_Int_Linear_Expr_denoteExpr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_denoteExpr___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_denoteExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_denoteExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_denoteExpr_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_denoteExpr_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_denoteExpr_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_denoteExpr_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__0_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__7_value),LEAN_SCALAR_PTR_LITERAL(222, 124, 176, 23, 127, 116, 25, 232)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mul"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__1_value),LEAN_SCALAR_PTR_LITERAL(114, 103, 7, 238, 74, 236, 156, 173)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__8_value),LEAN_SCALAR_PTR_LITERAL(191, 36, 220, 237, 68, 229, 44, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_value),LEAN_SCALAR_PTR_LITERAL(28, 250, 199, 101, 180, 239, 175, 219)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__5_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__6_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Mul"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__8_value),LEAN_SCALAR_PTR_LITERAL(155, 25, 183, 66, 31, 85, 84, 65)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__1_value),LEAN_SCALAR_PTR_LITERAL(124, 210, 233, 157, 130, 57, 249, 157)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sub"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__10_value),LEAN_SCALAR_PTR_LITERAL(203, 50, 219, 228, 204, 142, 182, 246)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__8_value),LEAN_SCALAR_PTR_LITERAL(153, 170, 154, 227, 136, 99, 108, 193)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Add"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__12_value),LEAN_SCALAR_PTR_LITERAL(123, 91, 0, 102, 155, 93, 69, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_value),LEAN_SCALAR_PTR_LITERAL(50, 34, 112, 179, 66, 45, 192, 92)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__14_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__15_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__17_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__17_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__18_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__19_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__21_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__20_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__20_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__22_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__21_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__22_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 25, 143, 42, 130, 140, 254, 56)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__1_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(204, 41, 2, 52, 230, 130, 24, 108)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__3_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "GT"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__4_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "gt"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__5 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(240, 16, 15, 58, 66, 186, 138, 31)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(239, 75, 137, 103, 59, 22, 209, 130)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__6 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__6_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "GE"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__7_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ge"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__8 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(74, 169, 4, 72, 62, 21, 91, 24)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(71, 88, 92, 156, 129, 215, 23, 77)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__9 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__9_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__10 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__10_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__11 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__11_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__12 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__13 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__13_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Dvd"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "dvd"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 71, 229, 107, 63, 192, 93, 62)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(233, 16, 181, 127, 123, 63, 3, 18)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__1;
static const lean_array_object l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toLinearExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_adapter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_adapter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Simp_Arith_Int_toContextExpr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__2;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(0u);
v___x_4_ = lean_nat_to_int(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go(lean_object* v_a_5_, lean_object* v_a_6_){
_start:
{
if (lean_obj_tag(v_a_5_) == 0)
{
if (lean_obj_tag(v_a_6_) == 0)
{
lean_object* v_k_7_; lean_object* v___x_9_; uint8_t v_isShared_10_; uint8_t v_isSharedCheck_14_; 
v_k_7_ = lean_ctor_get(v_a_6_, 0);
v_isSharedCheck_14_ = !lean_is_exclusive(v_a_6_);
if (v_isSharedCheck_14_ == 0)
{
v___x_9_ = v_a_6_;
v_isShared_10_ = v_isSharedCheck_14_;
goto v_resetjp_8_;
}
else
{
lean_inc(v_k_7_);
lean_dec(v_a_6_);
v___x_9_ = lean_box(0);
v_isShared_10_ = v_isSharedCheck_14_;
goto v_resetjp_8_;
}
v_resetjp_8_:
{
lean_object* v___x_12_; 
if (v_isShared_10_ == 0)
{
v___x_12_ = v___x_9_;
goto v_reusejp_11_;
}
else
{
lean_object* v_reuseFailAlloc_13_; 
v_reuseFailAlloc_13_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_13_, 0, v_k_7_);
v___x_12_ = v_reuseFailAlloc_13_;
goto v_reusejp_11_;
}
v_reusejp_11_:
{
return v___x_12_;
}
}
}
else
{
lean_object* v_k_15_; lean_object* v_v_16_; lean_object* v_p_17_; lean_object* v___x_18_; uint8_t v___x_19_; 
v_k_15_ = lean_ctor_get(v_a_6_, 0);
lean_inc(v_k_15_);
v_v_16_ = lean_ctor_get(v_a_6_, 1);
lean_inc(v_v_16_);
v_p_17_ = lean_ctor_get(v_a_6_, 2);
lean_inc_ref(v_p_17_);
lean_dec_ref(v_a_6_);
v___x_18_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0);
v___x_19_ = lean_int_dec_eq(v_k_15_, v___x_18_);
if (v___x_19_ == 0)
{
lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_20_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_20_, 0, v_v_16_);
v___x_21_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_21_, 0, v_k_15_);
lean_ctor_set(v___x_21_, 1, v___x_20_);
v___x_22_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_22_, 0, v___x_21_);
v_a_5_ = v___x_22_;
v_a_6_ = v_p_17_;
goto _start;
}
else
{
lean_object* v___x_24_; lean_object* v___x_25_; 
lean_dec(v_k_15_);
v___x_24_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_24_, 0, v_v_16_);
v___x_25_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_25_, 0, v___x_24_);
v_a_5_ = v___x_25_;
v_a_6_ = v_p_17_;
goto _start;
}
}
}
else
{
if (lean_obj_tag(v_a_6_) == 0)
{
lean_object* v_val_27_; lean_object* v_k_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_38_; 
v_val_27_ = lean_ctor_get(v_a_5_, 0);
lean_inc(v_val_27_);
lean_dec_ref(v_a_5_);
v_k_28_ = lean_ctor_get(v_a_6_, 0);
v_isSharedCheck_38_ = !lean_is_exclusive(v_a_6_);
if (v_isSharedCheck_38_ == 0)
{
v___x_30_ = v_a_6_;
v_isShared_31_ = v_isSharedCheck_38_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_k_28_);
lean_dec(v_a_6_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_38_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
lean_object* v___x_32_; uint8_t v___x_33_; 
v___x_32_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1);
v___x_33_ = lean_int_dec_eq(v_k_28_, v___x_32_);
if (v___x_33_ == 0)
{
lean_object* v___x_35_; 
if (v_isShared_31_ == 0)
{
v___x_35_ = v___x_30_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v_k_28_);
v___x_35_ = v_reuseFailAlloc_37_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
lean_object* v___x_36_; 
v___x_36_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_36_, 0, v_val_27_);
lean_ctor_set(v___x_36_, 1, v___x_35_);
return v___x_36_;
}
}
else
{
lean_del_object(v___x_30_);
lean_dec(v_k_28_);
return v_val_27_;
}
}
}
else
{
lean_object* v_val_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_61_; 
v_val_39_ = lean_ctor_get(v_a_5_, 0);
v_isSharedCheck_61_ = !lean_is_exclusive(v_a_5_);
if (v_isSharedCheck_61_ == 0)
{
v___x_41_ = v_a_5_;
v_isShared_42_ = v_isSharedCheck_61_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_val_39_);
lean_dec(v_a_5_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_61_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v_k_43_; lean_object* v_v_44_; lean_object* v_p_45_; lean_object* v___x_46_; uint8_t v___x_47_; 
v_k_43_ = lean_ctor_get(v_a_6_, 0);
lean_inc(v_k_43_);
v_v_44_ = lean_ctor_get(v_a_6_, 1);
lean_inc(v_v_44_);
v_p_45_ = lean_ctor_get(v_a_6_, 2);
lean_inc_ref(v_p_45_);
lean_dec_ref(v_a_6_);
v___x_46_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0);
v___x_47_ = lean_int_dec_eq(v_k_43_, v___x_46_);
if (v___x_47_ == 0)
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_52_; 
v___x_48_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_48_, 0, v_v_44_);
v___x_49_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_49_, 0, v_k_43_);
lean_ctor_set(v___x_49_, 1, v___x_48_);
v___x_50_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_50_, 0, v_val_39_);
lean_ctor_set(v___x_50_, 1, v___x_49_);
if (v_isShared_42_ == 0)
{
lean_ctor_set(v___x_41_, 0, v___x_50_);
v___x_52_ = v___x_41_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v___x_50_);
v___x_52_ = v_reuseFailAlloc_54_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
v_a_5_ = v___x_52_;
v_a_6_ = v_p_45_;
goto _start;
}
}
else
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_58_; 
lean_dec(v_k_43_);
v___x_55_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_55_, 0, v_v_44_);
v___x_56_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_56_, 0, v_val_39_);
lean_ctor_set(v___x_56_, 1, v___x_55_);
if (v_isShared_42_ == 0)
{
lean_ctor_set(v___x_41_, 0, v___x_56_);
v___x_58_ = v___x_41_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v___x_56_);
v___x_58_ = v_reuseFailAlloc_60_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
v_a_5_ = v___x_58_;
v_a_6_ = v_p_45_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_toExpr(lean_object* v_p_62_){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = lean_box(0);
v___x_64_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go(v___x_63_, v_p_62_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(lean_object* v_a_65_, lean_object* v_x_66_){
_start:
{
if (lean_obj_tag(v_x_66_) == 0)
{
lean_object* v___x_67_; 
v___x_67_ = lean_box(0);
return v___x_67_;
}
else
{
lean_object* v_key_68_; lean_object* v_value_69_; lean_object* v_tail_70_; uint8_t v___x_71_; 
v_key_68_ = lean_ctor_get(v_x_66_, 0);
v_value_69_ = lean_ctor_get(v_x_66_, 1);
v_tail_70_ = lean_ctor_get(v_x_66_, 2);
v___x_71_ = lean_nat_dec_eq(v_key_68_, v_a_65_);
if (v___x_71_ == 0)
{
v_x_66_ = v_tail_70_;
goto _start;
}
else
{
lean_object* v___x_73_; 
lean_inc(v_value_69_);
v___x_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_73_, 0, v_value_69_);
return v___x_73_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg___boxed(lean_object* v_a_74_, lean_object* v_x_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(v_a_74_, v_x_75_);
lean_dec(v_x_75_);
lean_dec(v_a_74_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0___redArg(lean_object* v_m_77_, lean_object* v_a_78_){
_start:
{
lean_object* v_buckets_79_; lean_object* v___x_80_; uint64_t v___x_81_; uint64_t v___x_82_; uint64_t v___x_83_; uint64_t v_fold_84_; uint64_t v___x_85_; uint64_t v___x_86_; uint64_t v___x_87_; size_t v___x_88_; size_t v___x_89_; size_t v___x_90_; size_t v___x_91_; size_t v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v_buckets_79_ = lean_ctor_get(v_m_77_, 1);
v___x_80_ = lean_array_get_size(v_buckets_79_);
v___x_81_ = lean_uint64_of_nat(v_a_78_);
v___x_82_ = 32ULL;
v___x_83_ = lean_uint64_shift_right(v___x_81_, v___x_82_);
v_fold_84_ = lean_uint64_xor(v___x_81_, v___x_83_);
v___x_85_ = 16ULL;
v___x_86_ = lean_uint64_shift_right(v_fold_84_, v___x_85_);
v___x_87_ = lean_uint64_xor(v_fold_84_, v___x_86_);
v___x_88_ = lean_uint64_to_usize(v___x_87_);
v___x_89_ = lean_usize_of_nat(v___x_80_);
v___x_90_ = ((size_t)1ULL);
v___x_91_ = lean_usize_sub(v___x_89_, v___x_90_);
v___x_92_ = lean_usize_land(v___x_88_, v___x_91_);
v___x_93_ = lean_array_uget_borrowed(v_buckets_79_, v___x_92_);
v___x_94_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(v_a_78_, v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0___redArg___boxed(lean_object* v_m_95_, lean_object* v_a_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0___redArg(v_m_95_, v_a_96_);
lean_dec(v_a_96_);
lean_dec_ref(v_m_95_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(lean_object* v_perm_98_, lean_object* v_a_99_){
_start:
{
switch(lean_obj_tag(v_a_99_))
{
case 0:
{
return v_a_99_;
}
case 1:
{
lean_object* v_i_100_; lean_object* v___x_101_; 
v_i_100_ = lean_ctor_get(v_a_99_, 0);
v___x_101_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0___redArg(v_perm_98_, v_i_100_);
if (lean_obj_tag(v___x_101_) == 0)
{
return v_a_99_;
}
else
{
lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_109_; 
v_isSharedCheck_109_ = !lean_is_exclusive(v_a_99_);
if (v_isSharedCheck_109_ == 0)
{
lean_object* v_unused_110_; 
v_unused_110_ = lean_ctor_get(v_a_99_, 0);
lean_dec(v_unused_110_);
v___x_103_ = v_a_99_;
v_isShared_104_ = v_isSharedCheck_109_;
goto v_resetjp_102_;
}
else
{
lean_dec(v_a_99_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_109_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v_val_105_; lean_object* v___x_107_; 
v_val_105_ = lean_ctor_get(v___x_101_, 0);
lean_inc(v_val_105_);
lean_dec_ref(v___x_101_);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 0, v_val_105_);
v___x_107_ = v___x_103_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_val_105_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
case 2:
{
lean_object* v_a_111_; lean_object* v_b_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_121_; 
v_a_111_ = lean_ctor_get(v_a_99_, 0);
v_b_112_ = lean_ctor_get(v_a_99_, 1);
v_isSharedCheck_121_ = !lean_is_exclusive(v_a_99_);
if (v_isSharedCheck_121_ == 0)
{
v___x_114_ = v_a_99_;
v_isShared_115_ = v_isSharedCheck_121_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_b_112_);
lean_inc(v_a_111_);
lean_dec(v_a_99_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_121_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_119_; 
v___x_116_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(v_perm_98_, v_a_111_);
v___x_117_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(v_perm_98_, v_b_112_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 1, v___x_117_);
lean_ctor_set(v___x_114_, 0, v___x_116_);
v___x_119_ = v___x_114_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v___x_116_);
lean_ctor_set(v_reuseFailAlloc_120_, 1, v___x_117_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
return v___x_119_;
}
}
}
case 3:
{
lean_object* v_a_122_; lean_object* v_b_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_132_; 
v_a_122_ = lean_ctor_get(v_a_99_, 0);
v_b_123_ = lean_ctor_get(v_a_99_, 1);
v_isSharedCheck_132_ = !lean_is_exclusive(v_a_99_);
if (v_isSharedCheck_132_ == 0)
{
v___x_125_ = v_a_99_;
v_isShared_126_ = v_isSharedCheck_132_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_b_123_);
lean_inc(v_a_122_);
lean_dec(v_a_99_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_132_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_130_; 
v___x_127_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(v_perm_98_, v_a_122_);
v___x_128_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(v_perm_98_, v_b_123_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 1, v___x_128_);
lean_ctor_set(v___x_125_, 0, v___x_127_);
v___x_130_ = v___x_125_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v___x_127_);
lean_ctor_set(v_reuseFailAlloc_131_, 1, v___x_128_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
case 4:
{
lean_object* v_a_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_141_; 
v_a_133_ = lean_ctor_get(v_a_99_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v_a_99_);
if (v_isSharedCheck_141_ == 0)
{
v___x_135_ = v_a_99_;
v_isShared_136_ = v_isSharedCheck_141_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_a_133_);
lean_dec(v_a_99_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_141_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_137_; lean_object* v___x_139_; 
v___x_137_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(v_perm_98_, v_a_133_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 0, v___x_137_);
v___x_139_ = v___x_135_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(4, 1, 0);
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
case 5:
{
lean_object* v_k_142_; lean_object* v_a_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_151_; 
v_k_142_ = lean_ctor_get(v_a_99_, 0);
v_a_143_ = lean_ctor_get(v_a_99_, 1);
v_isSharedCheck_151_ = !lean_is_exclusive(v_a_99_);
if (v_isSharedCheck_151_ == 0)
{
v___x_145_ = v_a_99_;
v_isShared_146_ = v_isSharedCheck_151_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_a_143_);
lean_inc(v_k_142_);
lean_dec(v_a_99_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_151_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_147_; lean_object* v___x_149_; 
v___x_147_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(v_perm_98_, v_a_143_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 1, v___x_147_);
v___x_149_ = v___x_145_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_k_142_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v___x_147_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
default: 
{
lean_object* v_a_152_; lean_object* v_k_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_161_; 
v_a_152_ = lean_ctor_get(v_a_99_, 0);
v_k_153_ = lean_ctor_get(v_a_99_, 1);
v_isSharedCheck_161_ = !lean_is_exclusive(v_a_99_);
if (v_isSharedCheck_161_ == 0)
{
v___x_155_ = v_a_99_;
v_isShared_156_ = v_isSharedCheck_161_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_k_153_);
lean_inc(v_a_152_);
lean_dec(v_a_99_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_161_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_157_; lean_object* v___x_159_; 
v___x_157_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(v_perm_98_, v_a_152_);
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 0, v___x_157_);
v___x_159_ = v___x_155_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_157_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v_k_153_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go___boxed(lean_object* v_perm_162_, lean_object* v_a_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(v_perm_162_, v_a_163_);
lean_dec_ref(v_perm_162_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0(lean_object* v_00_u03b2_165_, lean_object* v_m_166_, lean_object* v_a_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0___redArg(v_m_166_, v_a_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0___boxed(lean_object* v_00_u03b2_169_, lean_object* v_m_170_, lean_object* v_a_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0(v_00_u03b2_169_, v_m_170_, v_a_171_);
lean_dec(v_a_171_);
lean_dec_ref(v_m_170_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0_spec__0(lean_object* v_00_u03b2_173_, lean_object* v_a_174_, lean_object* v_x_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(v_a_174_, v_x_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_177_, lean_object* v_a_178_, lean_object* v_x_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0_spec__0(v_00_u03b2_177_, v_a_178_, v_x_179_);
lean_dec(v_x_179_);
lean_dec(v_a_178_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_applyPerm(lean_object* v_perm_181_, lean_object* v_e_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(v_perm_181_, v_e_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_applyPerm___boxed(lean_object* v_perm_184_, lean_object* v_e_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Int_Linear_Expr_applyPerm(v_perm_184_, v_e_185_);
lean_dec_ref(v_perm_184_);
return v_res_186_;
}
}
static lean_object* _init_l_Int_Linear_instReprPoly__lean_repr___closed__3(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = lean_unsigned_to_nat(2u);
v___x_194_ = lean_nat_to_int(v___x_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_instReprPoly__lean_repr(lean_object* v_x_201_, lean_object* v_prec_202_){
_start:
{
lean_object* v___y_204_; lean_object* v___y_205_; lean_object* v___y_206_; 
if (lean_obj_tag(v_x_201_) == 0)
{
lean_object* v_k_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_235_; 
v_k_212_ = lean_ctor_get(v_x_201_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v_x_201_);
if (v_isSharedCheck_235_ == 0)
{
v___x_214_ = v_x_201_;
v_isShared_215_ = v_isSharedCheck_235_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_k_212_);
lean_dec(v_x_201_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_235_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___y_217_; lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_231_ = lean_unsigned_to_nat(1024u);
v___x_232_ = lean_nat_dec_le(v___x_231_, v_prec_202_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; 
v___x_233_ = lean_obj_once(&l_Int_Linear_instReprPoly__lean_repr___closed__3, &l_Int_Linear_instReprPoly__lean_repr___closed__3_once, _init_l_Int_Linear_instReprPoly__lean_repr___closed__3);
v___y_217_ = v___x_233_;
goto v___jp_216_;
}
else
{
lean_object* v___x_234_; 
v___x_234_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0);
v___y_217_ = v___x_234_;
goto v___jp_216_;
}
v___jp_216_:
{
lean_object* v___x_218_; lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_218_ = ((lean_object*)(l_Int_Linear_instReprPoly__lean_repr___closed__2));
v___x_219_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1);
v___x_220_ = lean_int_dec_lt(v_k_212_, v___x_219_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; lean_object* v___x_223_; 
v___x_221_ = l_Int_repr(v_k_212_);
lean_dec(v_k_212_);
if (v_isShared_215_ == 0)
{
lean_ctor_set_tag(v___x_214_, 3);
lean_ctor_set(v___x_214_, 0, v___x_221_);
v___x_223_ = v___x_214_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_221_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
v___y_204_ = v___x_218_;
v___y_205_ = v___y_217_;
v___y_206_ = v___x_223_;
goto v___jp_203_;
}
}
else
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_225_ = lean_unsigned_to_nat(1024u);
v___x_226_ = l_Int_repr(v_k_212_);
lean_dec(v_k_212_);
if (v_isShared_215_ == 0)
{
lean_ctor_set_tag(v___x_214_, 3);
lean_ctor_set(v___x_214_, 0, v___x_226_);
v___x_228_ = v___x_214_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_226_);
v___x_228_ = v_reuseFailAlloc_230_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
lean_object* v___x_229_; 
v___x_229_ = l_Repr_addAppParen(v___x_228_, v___x_225_);
v___y_204_ = v___x_218_;
v___y_205_ = v___y_217_;
v___y_206_ = v___x_229_;
goto v___jp_203_;
}
}
}
}
}
else
{
lean_object* v_k_236_; lean_object* v_v_237_; lean_object* v_p_238_; lean_object* v___x_239_; lean_object* v___y_241_; lean_object* v___y_242_; lean_object* v___y_243_; lean_object* v___y_244_; lean_object* v___y_258_; uint8_t v___x_268_; 
v_k_236_ = lean_ctor_get(v_x_201_, 0);
lean_inc(v_k_236_);
v_v_237_ = lean_ctor_get(v_x_201_, 1);
lean_inc(v_v_237_);
v_p_238_ = lean_ctor_get(v_x_201_, 2);
lean_inc_ref(v_p_238_);
lean_dec_ref(v_x_201_);
v___x_239_ = lean_unsigned_to_nat(1024u);
v___x_268_ = lean_nat_dec_le(v___x_239_, v_prec_202_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; 
v___x_269_ = lean_obj_once(&l_Int_Linear_instReprPoly__lean_repr___closed__3, &l_Int_Linear_instReprPoly__lean_repr___closed__3_once, _init_l_Int_Linear_instReprPoly__lean_repr___closed__3);
v___y_258_ = v___x_269_;
goto v___jp_257_;
}
else
{
lean_object* v___x_270_; 
v___x_270_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0);
v___y_258_ = v___x_270_;
goto v___jp_257_;
}
v___jp_240_:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
lean_inc(v___y_242_);
v___x_245_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_245_, 0, v___y_242_);
lean_ctor_set(v___x_245_, 1, v___y_244_);
lean_inc_n(v___y_243_, 2);
v___x_246_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
lean_ctor_set(v___x_246_, 1, v___y_243_);
v___x_247_ = l_Nat_reprFast(v_v_237_);
v___x_248_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
v___x_249_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_246_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
v___x_250_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
lean_ctor_set(v___x_250_, 1, v___y_243_);
v___x_251_ = l_Int_Linear_instReprPoly__lean_repr(v_p_238_, v___x_239_);
v___x_252_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_250_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
lean_inc(v___y_241_);
v___x_253_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_253_, 0, v___y_241_);
lean_ctor_set(v___x_253_, 1, v___x_252_);
v___x_254_ = 0;
v___x_255_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_255_, 0, v___x_253_);
lean_ctor_set_uint8(v___x_255_, sizeof(void*)*1, v___x_254_);
v___x_256_ = l_Repr_addAppParen(v___x_255_, v_prec_202_);
return v___x_256_;
}
v___jp_257_:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_259_ = lean_box(1);
v___x_260_ = ((lean_object*)(l_Int_Linear_instReprPoly__lean_repr___closed__6));
v___x_261_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1);
v___x_262_ = lean_int_dec_lt(v_k_236_, v___x_261_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = l_Int_repr(v_k_236_);
lean_dec(v_k_236_);
v___x_264_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
v___y_241_ = v___y_258_;
v___y_242_ = v___x_260_;
v___y_243_ = v___x_259_;
v___y_244_ = v___x_264_;
goto v___jp_240_;
}
else
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_265_ = l_Int_repr(v_k_236_);
lean_dec(v_k_236_);
v___x_266_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
v___x_267_ = l_Repr_addAppParen(v___x_266_, v___x_239_);
v___y_241_ = v___y_258_;
v___y_242_ = v___x_260_;
v___y_243_ = v___x_259_;
v___y_244_ = v___x_267_;
goto v___jp_240_;
}
}
}
v___jp_203_:
{
lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
lean_inc(v___y_204_);
v___x_207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_207_, 0, v___y_204_);
lean_ctor_set(v___x_207_, 1, v___y_206_);
lean_inc(v___y_205_);
v___x_208_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_208_, 0, v___y_205_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
v___x_209_ = 0;
v___x_210_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_210_, 0, v___x_208_);
lean_ctor_set_uint8(v___x_210_, sizeof(void*)*1, v___x_209_);
v___x_211_ = l_Repr_addAppParen(v___x_210_, v_prec_202_);
return v___x_211_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_instReprPoly__lean_repr___boxed(lean_object* v_x_271_, lean_object* v_prec_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Int_Linear_instReprPoly__lean_repr(v_x_271_, v_prec_272_);
lean_dec(v_prec_272_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_instReprExpr__lean_repr(lean_object* v_x_318_, lean_object* v_prec_319_){
_start:
{
lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_330_; lean_object* v___y_331_; lean_object* v___y_332_; 
switch(lean_obj_tag(v_x_318_))
{
case 0:
{
lean_object* v_v_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_361_; 
v_v_338_ = lean_ctor_get(v_x_318_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v_x_318_);
if (v_isSharedCheck_361_ == 0)
{
v___x_340_ = v_x_318_;
v_isShared_341_ = v_isSharedCheck_361_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_v_338_);
lean_dec(v_x_318_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_361_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___y_343_; lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_357_ = lean_unsigned_to_nat(1024u);
v___x_358_ = lean_nat_dec_le(v___x_357_, v_prec_319_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; 
v___x_359_ = lean_obj_once(&l_Int_Linear_instReprPoly__lean_repr___closed__3, &l_Int_Linear_instReprPoly__lean_repr___closed__3_once, _init_l_Int_Linear_instReprPoly__lean_repr___closed__3);
v___y_343_ = v___x_359_;
goto v___jp_342_;
}
else
{
lean_object* v___x_360_; 
v___x_360_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0);
v___y_343_ = v___x_360_;
goto v___jp_342_;
}
v___jp_342_:
{
lean_object* v___x_344_; lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_344_ = ((lean_object*)(l_Int_Linear_instReprExpr__lean_repr___closed__2));
v___x_345_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1);
v___x_346_ = lean_int_dec_lt(v_v_338_, v___x_345_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; lean_object* v___x_349_; 
v___x_347_ = l_Int_repr(v_v_338_);
lean_dec(v_v_338_);
if (v_isShared_341_ == 0)
{
lean_ctor_set_tag(v___x_340_, 3);
lean_ctor_set(v___x_340_, 0, v___x_347_);
v___x_349_ = v___x_340_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_347_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
v___y_330_ = v___x_344_;
v___y_331_ = v___y_343_;
v___y_332_ = v___x_349_;
goto v___jp_329_;
}
}
else
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_351_ = lean_unsigned_to_nat(1024u);
v___x_352_ = l_Int_repr(v_v_338_);
lean_dec(v_v_338_);
if (v_isShared_341_ == 0)
{
lean_ctor_set_tag(v___x_340_, 3);
lean_ctor_set(v___x_340_, 0, v___x_352_);
v___x_354_ = v___x_340_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_352_);
v___x_354_ = v_reuseFailAlloc_356_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
lean_object* v___x_355_; 
v___x_355_ = l_Repr_addAppParen(v___x_354_, v___x_351_);
v___y_330_ = v___x_344_;
v___y_331_ = v___y_343_;
v___y_332_ = v___x_355_;
goto v___jp_329_;
}
}
}
}
}
case 1:
{
lean_object* v_i_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_382_; 
v_i_362_ = lean_ctor_get(v_x_318_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v_x_318_);
if (v_isSharedCheck_382_ == 0)
{
v___x_364_ = v_x_318_;
v_isShared_365_ = v_isSharedCheck_382_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_i_362_);
lean_dec(v_x_318_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_382_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___y_367_; lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_378_ = lean_unsigned_to_nat(1024u);
v___x_379_ = lean_nat_dec_le(v___x_378_, v_prec_319_);
if (v___x_379_ == 0)
{
lean_object* v___x_380_; 
v___x_380_ = lean_obj_once(&l_Int_Linear_instReprPoly__lean_repr___closed__3, &l_Int_Linear_instReprPoly__lean_repr___closed__3_once, _init_l_Int_Linear_instReprPoly__lean_repr___closed__3);
v___y_367_ = v___x_380_;
goto v___jp_366_;
}
else
{
lean_object* v___x_381_; 
v___x_381_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0);
v___y_367_ = v___x_381_;
goto v___jp_366_;
}
v___jp_366_:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_371_; 
v___x_368_ = ((lean_object*)(l_Int_Linear_instReprExpr__lean_repr___closed__5));
v___x_369_ = l_Nat_reprFast(v_i_362_);
if (v_isShared_365_ == 0)
{
lean_ctor_set_tag(v___x_364_, 3);
lean_ctor_set(v___x_364_, 0, v___x_369_);
v___x_371_ = v___x_364_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_369_);
v___x_371_ = v_reuseFailAlloc_377_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
lean_object* v___x_372_; lean_object* v___x_373_; uint8_t v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_372_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_368_);
lean_ctor_set(v___x_372_, 1, v___x_371_);
lean_inc(v___y_367_);
v___x_373_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_373_, 0, v___y_367_);
lean_ctor_set(v___x_373_, 1, v___x_372_);
v___x_374_ = 0;
v___x_375_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_375_, 0, v___x_373_);
lean_ctor_set_uint8(v___x_375_, sizeof(void*)*1, v___x_374_);
v___x_376_ = l_Repr_addAppParen(v___x_375_, v_prec_319_);
return v___x_376_;
}
}
}
}
case 2:
{
lean_object* v_a_383_; lean_object* v_b_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_407_; 
v_a_383_ = lean_ctor_get(v_x_318_, 0);
v_b_384_ = lean_ctor_get(v_x_318_, 1);
v_isSharedCheck_407_ = !lean_is_exclusive(v_x_318_);
if (v_isSharedCheck_407_ == 0)
{
v___x_386_ = v_x_318_;
v_isShared_387_ = v_isSharedCheck_407_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_b_384_);
lean_inc(v_a_383_);
lean_dec(v_x_318_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_407_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_388_; lean_object* v___y_390_; uint8_t v___x_404_; 
v___x_388_ = lean_unsigned_to_nat(1024u);
v___x_404_ = lean_nat_dec_le(v___x_388_, v_prec_319_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; 
v___x_405_ = lean_obj_once(&l_Int_Linear_instReprPoly__lean_repr___closed__3, &l_Int_Linear_instReprPoly__lean_repr___closed__3_once, _init_l_Int_Linear_instReprPoly__lean_repr___closed__3);
v___y_390_ = v___x_405_;
goto v___jp_389_;
}
else
{
lean_object* v___x_406_; 
v___x_406_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0);
v___y_390_ = v___x_406_;
goto v___jp_389_;
}
v___jp_389_:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_395_; 
v___x_391_ = lean_box(1);
v___x_392_ = ((lean_object*)(l_Int_Linear_instReprExpr__lean_repr___closed__8));
v___x_393_ = l_Int_Linear_instReprExpr__lean_repr(v_a_383_, v___x_388_);
if (v_isShared_387_ == 0)
{
lean_ctor_set_tag(v___x_386_, 5);
lean_ctor_set(v___x_386_, 1, v___x_393_);
lean_ctor_set(v___x_386_, 0, v___x_392_);
v___x_395_ = v___x_386_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_392_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v___x_393_);
v___x_395_ = v_reuseFailAlloc_403_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; uint8_t v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_396_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
lean_ctor_set(v___x_396_, 1, v___x_391_);
v___x_397_ = l_Int_Linear_instReprExpr__lean_repr(v_b_384_, v___x_388_);
v___x_398_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_396_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
lean_inc(v___y_390_);
v___x_399_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_399_, 0, v___y_390_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
v___x_400_ = 0;
v___x_401_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_401_, 0, v___x_399_);
lean_ctor_set_uint8(v___x_401_, sizeof(void*)*1, v___x_400_);
v___x_402_ = l_Repr_addAppParen(v___x_401_, v_prec_319_);
return v___x_402_;
}
}
}
}
case 3:
{
lean_object* v_a_408_; lean_object* v_b_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_432_; 
v_a_408_ = lean_ctor_get(v_x_318_, 0);
v_b_409_ = lean_ctor_get(v_x_318_, 1);
v_isSharedCheck_432_ = !lean_is_exclusive(v_x_318_);
if (v_isSharedCheck_432_ == 0)
{
v___x_411_ = v_x_318_;
v_isShared_412_ = v_isSharedCheck_432_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_b_409_);
lean_inc(v_a_408_);
lean_dec(v_x_318_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_432_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_413_; lean_object* v___y_415_; uint8_t v___x_429_; 
v___x_413_ = lean_unsigned_to_nat(1024u);
v___x_429_ = lean_nat_dec_le(v___x_413_, v_prec_319_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; 
v___x_430_ = lean_obj_once(&l_Int_Linear_instReprPoly__lean_repr___closed__3, &l_Int_Linear_instReprPoly__lean_repr___closed__3_once, _init_l_Int_Linear_instReprPoly__lean_repr___closed__3);
v___y_415_ = v___x_430_;
goto v___jp_414_;
}
else
{
lean_object* v___x_431_; 
v___x_431_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0);
v___y_415_ = v___x_431_;
goto v___jp_414_;
}
v___jp_414_:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_420_; 
v___x_416_ = lean_box(1);
v___x_417_ = ((lean_object*)(l_Int_Linear_instReprExpr__lean_repr___closed__11));
v___x_418_ = l_Int_Linear_instReprExpr__lean_repr(v_a_408_, v___x_413_);
if (v_isShared_412_ == 0)
{
lean_ctor_set_tag(v___x_411_, 5);
lean_ctor_set(v___x_411_, 1, v___x_418_);
lean_ctor_set(v___x_411_, 0, v___x_417_);
v___x_420_ = v___x_411_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_417_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v___x_418_);
v___x_420_ = v_reuseFailAlloc_428_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; uint8_t v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_421_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
lean_ctor_set(v___x_421_, 1, v___x_416_);
v___x_422_ = l_Int_Linear_instReprExpr__lean_repr(v_b_409_, v___x_413_);
v___x_423_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_421_);
lean_ctor_set(v___x_423_, 1, v___x_422_);
lean_inc(v___y_415_);
v___x_424_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_424_, 0, v___y_415_);
lean_ctor_set(v___x_424_, 1, v___x_423_);
v___x_425_ = 0;
v___x_426_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_426_, 0, v___x_424_);
lean_ctor_set_uint8(v___x_426_, sizeof(void*)*1, v___x_425_);
v___x_427_ = l_Repr_addAppParen(v___x_426_, v_prec_319_);
return v___x_427_;
}
}
}
}
case 4:
{
lean_object* v_a_433_; lean_object* v___x_434_; lean_object* v___y_436_; uint8_t v___x_444_; 
v_a_433_ = lean_ctor_get(v_x_318_, 0);
lean_inc_ref(v_a_433_);
lean_dec_ref(v_x_318_);
v___x_434_ = lean_unsigned_to_nat(1024u);
v___x_444_ = lean_nat_dec_le(v___x_434_, v_prec_319_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; 
v___x_445_ = lean_obj_once(&l_Int_Linear_instReprPoly__lean_repr___closed__3, &l_Int_Linear_instReprPoly__lean_repr___closed__3_once, _init_l_Int_Linear_instReprPoly__lean_repr___closed__3);
v___y_436_ = v___x_445_;
goto v___jp_435_;
}
else
{
lean_object* v___x_446_; 
v___x_446_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0);
v___y_436_ = v___x_446_;
goto v___jp_435_;
}
v___jp_435_:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_437_ = ((lean_object*)(l_Int_Linear_instReprExpr__lean_repr___closed__14));
v___x_438_ = l_Int_Linear_instReprExpr__lean_repr(v_a_433_, v___x_434_);
v___x_439_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_437_);
lean_ctor_set(v___x_439_, 1, v___x_438_);
lean_inc(v___y_436_);
v___x_440_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_440_, 0, v___y_436_);
lean_ctor_set(v___x_440_, 1, v___x_439_);
v___x_441_ = 0;
v___x_442_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_442_, 0, v___x_440_);
lean_ctor_set_uint8(v___x_442_, sizeof(void*)*1, v___x_441_);
v___x_443_ = l_Repr_addAppParen(v___x_442_, v_prec_319_);
return v___x_443_;
}
}
case 5:
{
lean_object* v_k_447_; lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_482_; 
v_k_447_ = lean_ctor_get(v_x_318_, 0);
v_a_448_ = lean_ctor_get(v_x_318_, 1);
v_isSharedCheck_482_ = !lean_is_exclusive(v_x_318_);
if (v_isSharedCheck_482_ == 0)
{
v___x_450_ = v_x_318_;
v_isShared_451_ = v_isSharedCheck_482_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_inc(v_k_447_);
lean_dec(v_x_318_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_482_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_452_; lean_object* v___y_454_; lean_object* v___y_455_; lean_object* v___y_456_; lean_object* v___y_457_; lean_object* v___y_469_; uint8_t v___x_479_; 
v___x_452_ = lean_unsigned_to_nat(1024u);
v___x_479_ = lean_nat_dec_le(v___x_452_, v_prec_319_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; 
v___x_480_ = lean_obj_once(&l_Int_Linear_instReprPoly__lean_repr___closed__3, &l_Int_Linear_instReprPoly__lean_repr___closed__3_once, _init_l_Int_Linear_instReprPoly__lean_repr___closed__3);
v___y_469_ = v___x_480_;
goto v___jp_468_;
}
else
{
lean_object* v___x_481_; 
v___x_481_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0);
v___y_469_ = v___x_481_;
goto v___jp_468_;
}
v___jp_453_:
{
lean_object* v___x_459_; 
lean_inc(v___y_456_);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 1, v___y_457_);
lean_ctor_set(v___x_450_, 0, v___y_456_);
v___x_459_ = v___x_450_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___y_456_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v___y_457_);
v___x_459_ = v_reuseFailAlloc_467_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; uint8_t v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
lean_inc(v___y_454_);
v___x_460_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
lean_ctor_set(v___x_460_, 1, v___y_454_);
v___x_461_ = l_Int_Linear_instReprExpr__lean_repr(v_a_448_, v___x_452_);
v___x_462_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_462_, 0, v___x_460_);
lean_ctor_set(v___x_462_, 1, v___x_461_);
lean_inc(v___y_455_);
v___x_463_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_463_, 0, v___y_455_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
v___x_464_ = 0;
v___x_465_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_465_, 0, v___x_463_);
lean_ctor_set_uint8(v___x_465_, sizeof(void*)*1, v___x_464_);
v___x_466_ = l_Repr_addAppParen(v___x_465_, v_prec_319_);
return v___x_466_;
}
}
v___jp_468_:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_470_ = lean_box(1);
v___x_471_ = ((lean_object*)(l_Int_Linear_instReprExpr__lean_repr___closed__17));
v___x_472_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1);
v___x_473_ = lean_int_dec_lt(v_k_447_, v___x_472_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_474_ = l_Int_repr(v_k_447_);
lean_dec(v_k_447_);
v___x_475_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
v___y_454_ = v___x_470_;
v___y_455_ = v___y_469_;
v___y_456_ = v___x_471_;
v___y_457_ = v___x_475_;
goto v___jp_453_;
}
else
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_476_ = l_Int_repr(v_k_447_);
lean_dec(v_k_447_);
v___x_477_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
v___x_478_ = l_Repr_addAppParen(v___x_477_, v___x_452_);
v___y_454_ = v___x_470_;
v___y_455_ = v___y_469_;
v___y_456_ = v___x_471_;
v___y_457_ = v___x_478_;
goto v___jp_453_;
}
}
}
}
default: 
{
lean_object* v_a_483_; lean_object* v_k_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_508_; 
v_a_483_ = lean_ctor_get(v_x_318_, 0);
v_k_484_ = lean_ctor_get(v_x_318_, 1);
v_isSharedCheck_508_ = !lean_is_exclusive(v_x_318_);
if (v_isSharedCheck_508_ == 0)
{
v___x_486_ = v_x_318_;
v_isShared_487_ = v_isSharedCheck_508_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_k_484_);
lean_inc(v_a_483_);
lean_dec(v_x_318_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_508_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_488_; lean_object* v___y_490_; uint8_t v___x_505_; 
v___x_488_ = lean_unsigned_to_nat(1024u);
v___x_505_ = lean_nat_dec_le(v___x_488_, v_prec_319_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; 
v___x_506_ = lean_obj_once(&l_Int_Linear_instReprPoly__lean_repr___closed__3, &l_Int_Linear_instReprPoly__lean_repr___closed__3_once, _init_l_Int_Linear_instReprPoly__lean_repr___closed__3);
v___y_490_ = v___x_506_;
goto v___jp_489_;
}
else
{
lean_object* v___x_507_; 
v___x_507_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0);
v___y_490_ = v___x_507_;
goto v___jp_489_;
}
v___jp_489_:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_495_; 
v___x_491_ = lean_box(1);
v___x_492_ = ((lean_object*)(l_Int_Linear_instReprExpr__lean_repr___closed__20));
v___x_493_ = l_Int_Linear_instReprExpr__lean_repr(v_a_483_, v___x_488_);
if (v_isShared_487_ == 0)
{
lean_ctor_set_tag(v___x_486_, 5);
lean_ctor_set(v___x_486_, 1, v___x_493_);
lean_ctor_set(v___x_486_, 0, v___x_492_);
v___x_495_ = v___x_486_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_492_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v___x_493_);
v___x_495_ = v_reuseFailAlloc_504_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
lean_object* v___x_496_; lean_object* v___x_497_; uint8_t v___x_498_; 
v___x_496_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
lean_ctor_set(v___x_496_, 1, v___x_491_);
v___x_497_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1);
v___x_498_ = lean_int_dec_lt(v_k_484_, v___x_497_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = l_Int_repr(v_k_484_);
lean_dec(v_k_484_);
v___x_500_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
v___y_321_ = v___x_496_;
v___y_322_ = v___y_490_;
v___y_323_ = v___x_500_;
goto v___jp_320_;
}
else
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_501_ = l_Int_repr(v_k_484_);
lean_dec(v_k_484_);
v___x_502_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
v___x_503_ = l_Repr_addAppParen(v___x_502_, v___x_488_);
v___y_321_ = v___x_496_;
v___y_322_ = v___y_490_;
v___y_323_ = v___x_503_;
goto v___jp_320_;
}
}
}
}
}
}
v___jp_320_:
{
lean_object* v___x_324_; lean_object* v___x_325_; uint8_t v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_324_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_324_, 0, v___y_321_);
lean_ctor_set(v___x_324_, 1, v___y_323_);
lean_inc(v___y_322_);
v___x_325_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_325_, 0, v___y_322_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
v___x_326_ = 0;
v___x_327_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_327_, 0, v___x_325_);
lean_ctor_set_uint8(v___x_327_, sizeof(void*)*1, v___x_326_);
v___x_328_ = l_Repr_addAppParen(v___x_327_, v_prec_319_);
return v___x_328_;
}
v___jp_329_:
{
lean_object* v___x_333_; lean_object* v___x_334_; uint8_t v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
lean_inc(v___y_330_);
v___x_333_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_333_, 0, v___y_330_);
lean_ctor_set(v___x_333_, 1, v___y_332_);
lean_inc(v___y_331_);
v___x_334_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_334_, 0, v___y_331_);
lean_ctor_set(v___x_334_, 1, v___x_333_);
v___x_335_ = 0;
v___x_336_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_336_, 0, v___x_334_);
lean_ctor_set_uint8(v___x_336_, sizeof(void*)*1, v___x_335_);
v___x_337_ = l_Repr_addAppParen(v___x_336_, v_prec_319_);
return v___x_337_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_instReprExpr__lean_repr___boxed(lean_object* v_x_509_, lean_object* v_prec_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Int_Linear_instReprExpr__lean_repr(v_x_509_, v_prec_510_);
lean_dec(v_prec_510_);
return v_res_511_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__5(void){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_523_ = lean_box(0);
v___x_524_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__4));
v___x_525_ = l_Lean_mkConst(v___x_524_, v___x_523_);
return v___x_525_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__9(void){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = lean_unsigned_to_nat(0u);
v___x_532_ = l_Lean_Level_ofNat(v___x_531_);
return v___x_532_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__10(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_533_ = lean_box(0);
v___x_534_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__9, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__9_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__9);
v___x_535_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
lean_ctor_set(v___x_535_, 1, v___x_533_);
return v___x_535_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11(void){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_536_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__10, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__10_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__10);
v___x_537_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__8));
v___x_538_ = l_Lean_Expr_const___override(v___x_537_, v___x_536_);
return v___x_538_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_541_ = lean_box(0);
v___x_542_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12));
v___x_543_ = l_Lean_Expr_const___override(v___x_542_, v___x_541_);
return v___x_543_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16(void){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_548_ = lean_box(0);
v___x_549_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__15));
v___x_550_ = l_Lean_Expr_const___override(v___x_549_, v___x_548_);
return v___x_550_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__19(void){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_557_ = lean_box(0);
v___x_558_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__18));
v___x_559_ = l_Lean_mkConst(v___x_558_, v___x_557_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly(lean_object* v_p_560_){
_start:
{
if (lean_obj_tag(v_p_560_) == 0)
{
lean_object* v_k_561_; lean_object* v___x_562_; lean_object* v___x_563_; uint8_t v___x_564_; 
v_k_561_ = lean_ctor_get(v_p_560_, 0);
lean_inc(v_k_561_);
lean_dec_ref(v_p_560_);
v___x_562_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__5, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__5);
v___x_563_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1);
v___x_564_ = lean_int_dec_le(v___x_563_, v_k_561_);
if (v___x_564_ == 0)
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_565_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11);
v___x_566_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13);
v___x_567_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16);
v___x_568_ = lean_int_neg(v_k_561_);
lean_dec(v_k_561_);
v___x_569_ = l_Int_toNat(v___x_568_);
lean_dec(v___x_568_);
v___x_570_ = l_Lean_instToExprInt_mkNat(v___x_569_);
v___x_571_ = l_Lean_mkApp3(v___x_565_, v___x_566_, v___x_567_, v___x_570_);
v___x_572_ = l_Lean_Expr_app___override(v___x_562_, v___x_571_);
return v___x_572_;
}
else
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_573_ = l_Int_toNat(v_k_561_);
lean_dec(v_k_561_);
v___x_574_ = l_Lean_instToExprInt_mkNat(v___x_573_);
v___x_575_ = l_Lean_Expr_app___override(v___x_562_, v___x_574_);
return v___x_575_;
}
}
else
{
lean_object* v_k_576_; lean_object* v_v_577_; lean_object* v_p_578_; lean_object* v___x_579_; lean_object* v___y_581_; lean_object* v___x_585_; uint8_t v___x_586_; 
v_k_576_ = lean_ctor_get(v_p_560_, 0);
lean_inc(v_k_576_);
v_v_577_ = lean_ctor_get(v_p_560_, 1);
lean_inc(v_v_577_);
v_p_578_ = lean_ctor_get(v_p_560_, 2);
lean_inc_ref(v_p_578_);
lean_dec_ref(v_p_560_);
v___x_579_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__19, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__19_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__19);
v___x_585_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1);
v___x_586_ = lean_int_dec_le(v___x_585_, v_k_576_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_587_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11);
v___x_588_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13);
v___x_589_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16);
v___x_590_ = lean_int_neg(v_k_576_);
lean_dec(v_k_576_);
v___x_591_ = l_Int_toNat(v___x_590_);
lean_dec(v___x_590_);
v___x_592_ = l_Lean_instToExprInt_mkNat(v___x_591_);
v___x_593_ = l_Lean_mkApp3(v___x_587_, v___x_588_, v___x_589_, v___x_592_);
v___y_581_ = v___x_593_;
goto v___jp_580_;
}
else
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = l_Int_toNat(v_k_576_);
lean_dec(v_k_576_);
v___x_595_ = l_Lean_instToExprInt_mkNat(v___x_594_);
v___y_581_ = v___x_595_;
goto v___jp_580_;
}
v___jp_580_:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_582_ = l_Lean_mkNatLit(v_v_577_);
v___x_583_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v_p_578_);
v___x_584_ = l_Lean_mkApp3(v___x_579_, v___y_581_, v___x_582_, v___x_583_);
return v___x_584_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__2(void){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_601_ = lean_box(0);
v___x_602_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__1));
v___x_603_ = l_Lean_mkConst(v___x_602_, v___x_601_);
return v___x_603_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__3(void){
_start:
{
lean_object* v___x_604_; lean_object* v___f_605_; lean_object* v___x_606_; 
v___x_604_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__2, &l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__2);
v___f_605_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__0));
v___x_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_606_, 0, v___f_605_);
lean_ctor_set(v___x_606_, 1, v___x_604_);
return v___x_606_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_instToExprPoly(void){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__3, &l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__3);
return v___x_607_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__2(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_614_ = lean_box(0);
v___x_615_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1));
v___x_616_ = l_Lean_mkConst(v___x_615_, v___x_614_);
return v___x_616_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__5(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_623_ = lean_box(0);
v___x_624_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4));
v___x_625_ = l_Lean_mkConst(v___x_624_, v___x_623_);
return v___x_625_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__7(void){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_631_ = lean_box(0);
v___x_632_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6));
v___x_633_ = l_Lean_mkConst(v___x_632_, v___x_631_);
return v___x_633_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__10(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_640_ = lean_box(0);
v___x_641_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9));
v___x_642_ = l_Lean_mkConst(v___x_641_, v___x_640_);
return v___x_642_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__12(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_648_ = lean_box(0);
v___x_649_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11));
v___x_650_ = l_Lean_mkConst(v___x_649_, v___x_648_);
return v___x_650_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__15(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_657_ = lean_box(0);
v___x_658_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14));
v___x_659_ = l_Lean_mkConst(v___x_658_, v___x_657_);
return v___x_659_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__18(void){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_666_ = lean_box(0);
v___x_667_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17));
v___x_668_ = l_Lean_mkConst(v___x_667_, v___x_666_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(lean_object* v_e_669_){
_start:
{
switch(lean_obj_tag(v_e_669_))
{
case 0:
{
lean_object* v_v_670_; lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v_v_670_ = lean_ctor_get(v_e_669_, 0);
lean_inc(v_v_670_);
lean_dec_ref(v_e_669_);
v___x_671_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__2, &l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__2);
v___x_672_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1);
v___x_673_ = lean_int_dec_le(v___x_672_, v_v_670_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_674_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11);
v___x_675_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13);
v___x_676_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16);
v___x_677_ = lean_int_neg(v_v_670_);
lean_dec(v_v_670_);
v___x_678_ = l_Int_toNat(v___x_677_);
lean_dec(v___x_677_);
v___x_679_ = l_Lean_instToExprInt_mkNat(v___x_678_);
v___x_680_ = l_Lean_mkApp3(v___x_674_, v___x_675_, v___x_676_, v___x_679_);
v___x_681_ = l_Lean_Expr_app___override(v___x_671_, v___x_680_);
return v___x_681_;
}
else
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_682_ = l_Int_toNat(v_v_670_);
lean_dec(v_v_670_);
v___x_683_ = l_Lean_instToExprInt_mkNat(v___x_682_);
v___x_684_ = l_Lean_Expr_app___override(v___x_671_, v___x_683_);
return v___x_684_;
}
}
case 1:
{
lean_object* v_i_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v_i_685_ = lean_ctor_get(v_e_669_, 0);
lean_inc(v_i_685_);
lean_dec_ref(v_e_669_);
v___x_686_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__5, &l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__5);
v___x_687_ = l_Lean_mkNatLit(v_i_685_);
v___x_688_ = l_Lean_Expr_app___override(v___x_686_, v___x_687_);
return v___x_688_;
}
case 2:
{
lean_object* v_a_689_; lean_object* v_b_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v_a_689_ = lean_ctor_get(v_e_669_, 0);
lean_inc_ref(v_a_689_);
v_b_690_ = lean_ctor_get(v_e_669_, 1);
lean_inc_ref(v_b_690_);
lean_dec_ref(v_e_669_);
v___x_691_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__7, &l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__7_once, _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__7);
v___x_692_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_a_689_);
v___x_693_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_b_690_);
v___x_694_ = l_Lean_mkAppB(v___x_691_, v___x_692_, v___x_693_);
return v___x_694_;
}
case 3:
{
lean_object* v_a_695_; lean_object* v_b_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v_a_695_ = lean_ctor_get(v_e_669_, 0);
lean_inc_ref(v_a_695_);
v_b_696_ = lean_ctor_get(v_e_669_, 1);
lean_inc_ref(v_b_696_);
lean_dec_ref(v_e_669_);
v___x_697_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__10, &l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__10_once, _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__10);
v___x_698_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_a_695_);
v___x_699_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_b_696_);
v___x_700_ = l_Lean_mkAppB(v___x_697_, v___x_698_, v___x_699_);
return v___x_700_;
}
case 4:
{
lean_object* v_a_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v_a_701_ = lean_ctor_get(v_e_669_, 0);
lean_inc_ref(v_a_701_);
lean_dec_ref(v_e_669_);
v___x_702_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__12, &l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__12);
v___x_703_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_a_701_);
v___x_704_ = l_Lean_Expr_app___override(v___x_702_, v___x_703_);
return v___x_704_;
}
case 5:
{
lean_object* v_k_705_; lean_object* v_a_706_; lean_object* v___x_707_; lean_object* v___y_709_; lean_object* v___x_712_; uint8_t v___x_713_; 
v_k_705_ = lean_ctor_get(v_e_669_, 0);
lean_inc(v_k_705_);
v_a_706_ = lean_ctor_get(v_e_669_, 1);
lean_inc_ref(v_a_706_);
lean_dec_ref(v_e_669_);
v___x_707_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__15, &l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__15_once, _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__15);
v___x_712_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1);
v___x_713_ = lean_int_dec_le(v___x_712_, v_k_705_);
if (v___x_713_ == 0)
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_714_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11);
v___x_715_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13);
v___x_716_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16);
v___x_717_ = lean_int_neg(v_k_705_);
lean_dec(v_k_705_);
v___x_718_ = l_Int_toNat(v___x_717_);
lean_dec(v___x_717_);
v___x_719_ = l_Lean_instToExprInt_mkNat(v___x_718_);
v___x_720_ = l_Lean_mkApp3(v___x_714_, v___x_715_, v___x_716_, v___x_719_);
v___y_709_ = v___x_720_;
goto v___jp_708_;
}
else
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = l_Int_toNat(v_k_705_);
lean_dec(v_k_705_);
v___x_722_ = l_Lean_instToExprInt_mkNat(v___x_721_);
v___y_709_ = v___x_722_;
goto v___jp_708_;
}
v___jp_708_:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_a_706_);
v___x_711_ = l_Lean_mkAppB(v___x_707_, v___y_709_, v___x_710_);
return v___x_711_;
}
}
default: 
{
lean_object* v_a_723_; lean_object* v_k_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; uint8_t v___x_728_; 
v_a_723_ = lean_ctor_get(v_e_669_, 0);
lean_inc_ref(v_a_723_);
v_k_724_ = lean_ctor_get(v_e_669_, 1);
lean_inc(v_k_724_);
lean_dec_ref(v_e_669_);
v___x_725_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__18, &l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__18_once, _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__18);
v___x_726_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_a_723_);
v___x_727_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1);
v___x_728_ = lean_int_dec_le(v___x_727_, v_k_724_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_729_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11);
v___x_730_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13);
v___x_731_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16);
v___x_732_ = lean_int_neg(v_k_724_);
lean_dec(v_k_724_);
v___x_733_ = l_Int_toNat(v___x_732_);
lean_dec(v___x_732_);
v___x_734_ = l_Lean_instToExprInt_mkNat(v___x_733_);
v___x_735_ = l_Lean_mkApp3(v___x_729_, v___x_730_, v___x_731_, v___x_734_);
v___x_736_ = l_Lean_mkAppB(v___x_725_, v___x_726_, v___x_735_);
return v___x_736_;
}
else
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_737_ = l_Int_toNat(v_k_724_);
lean_dec(v_k_724_);
v___x_738_ = l_Lean_instToExprInt_mkNat(v___x_737_);
v___x_739_ = l_Lean_mkAppB(v___x_725_, v___x_726_, v___x_738_);
return v___x_739_;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__2(void){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_745_ = lean_box(0);
v___x_746_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__1));
v___x_747_ = l_Lean_mkConst(v___x_746_, v___x_745_);
return v___x_747_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__3(void){
_start:
{
lean_object* v___x_748_; lean_object* v___f_749_; lean_object* v___x_750_; 
v___x_748_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__2, &l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__2);
v___f_749_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__0));
v___x_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_750_, 0, v___f_749_);
lean_ctor_set(v___x_750_, 1, v___x_748_);
return v___x_750_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_instToExprExpr(void){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__3, &l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__3);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_denoteExpr___redArg(lean_object* v_ctx_752_, lean_object* v_e_753_){
_start:
{
switch(lean_obj_tag(v_e_753_))
{
case 0:
{
lean_object* v_v_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_776_; 
lean_dec_ref(v_ctx_752_);
v_v_755_ = lean_ctor_get(v_e_753_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v_e_753_);
if (v_isSharedCheck_776_ == 0)
{
v___x_757_ = v_e_753_;
v_isShared_758_ = v_isSharedCheck_776_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_v_755_);
lean_dec(v_e_753_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_776_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_759_; uint8_t v___x_760_; 
v___x_759_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1);
v___x_760_ = lean_int_dec_le(v___x_759_, v_v_755_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_769_; 
v___x_761_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11);
v___x_762_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13);
v___x_763_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16);
v___x_764_ = lean_int_neg(v_v_755_);
lean_dec(v_v_755_);
v___x_765_ = l_Int_toNat(v___x_764_);
lean_dec(v___x_764_);
v___x_766_ = l_Lean_instToExprInt_mkNat(v___x_765_);
v___x_767_ = l_Lean_mkApp3(v___x_761_, v___x_762_, v___x_763_, v___x_766_);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 0, v___x_767_);
v___x_769_ = v___x_757_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_767_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
else
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_774_; 
v___x_771_ = l_Int_toNat(v_v_755_);
lean_dec(v_v_755_);
v___x_772_ = l_Lean_instToExprInt_mkNat(v___x_771_);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 0, v___x_772_);
v___x_774_ = v___x_757_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_772_);
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
case 1:
{
lean_object* v_i_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_785_; 
v_i_777_ = lean_ctor_get(v_e_753_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v_e_753_);
if (v_isSharedCheck_785_ == 0)
{
v___x_779_ = v_e_753_;
v_isShared_780_ = v_isSharedCheck_785_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_i_777_);
lean_dec(v_e_753_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_785_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_781_; lean_object* v___x_783_; 
v___x_781_ = lean_apply_1(v_ctx_752_, v_i_777_);
if (v_isShared_780_ == 0)
{
lean_ctor_set_tag(v___x_779_, 0);
lean_ctor_set(v___x_779_, 0, v___x_781_);
v___x_783_ = v___x_779_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_781_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
case 2:
{
lean_object* v_a_786_; lean_object* v_b_787_; lean_object* v___x_788_; lean_object* v_a_789_; lean_object* v___x_790_; lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_799_; 
v_a_786_ = lean_ctor_get(v_e_753_, 0);
lean_inc_ref(v_a_786_);
v_b_787_ = lean_ctor_get(v_e_753_, 1);
lean_inc_ref(v_b_787_);
lean_dec_ref(v_e_753_);
lean_inc_ref(v_ctx_752_);
v___x_788_ = l_Int_Linear_Expr_denoteExpr___redArg(v_ctx_752_, v_a_786_);
v_a_789_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_a_789_);
lean_dec_ref(v___x_788_);
v___x_790_ = l_Int_Linear_Expr_denoteExpr___redArg(v_ctx_752_, v_b_787_);
v_a_791_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_799_ == 0)
{
v___x_793_ = v___x_790_;
v_isShared_794_ = v_isSharedCheck_799_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_790_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_799_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_795_; lean_object* v___x_797_; 
v___x_795_ = l_Lean_mkIntAdd(v_a_789_, v_a_791_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 0, v___x_795_);
v___x_797_ = v___x_793_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_795_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
case 3:
{
lean_object* v_a_800_; lean_object* v_b_801_; lean_object* v___x_802_; lean_object* v_a_803_; lean_object* v___x_804_; lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_813_; 
v_a_800_ = lean_ctor_get(v_e_753_, 0);
lean_inc_ref(v_a_800_);
v_b_801_ = lean_ctor_get(v_e_753_, 1);
lean_inc_ref(v_b_801_);
lean_dec_ref(v_e_753_);
lean_inc_ref(v_ctx_752_);
v___x_802_ = l_Int_Linear_Expr_denoteExpr___redArg(v_ctx_752_, v_a_800_);
v_a_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_a_803_);
lean_dec_ref(v___x_802_);
v___x_804_ = l_Int_Linear_Expr_denoteExpr___redArg(v_ctx_752_, v_b_801_);
v_a_805_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_813_ == 0)
{
v___x_807_ = v___x_804_;
v_isShared_808_ = v_isSharedCheck_813_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_804_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_813_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_809_; lean_object* v___x_811_; 
v___x_809_ = l_Lean_mkIntSub(v_a_803_, v_a_805_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 0, v___x_809_);
v___x_811_ = v___x_807_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
case 4:
{
lean_object* v_a_814_; lean_object* v___x_815_; lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_824_; 
v_a_814_ = lean_ctor_get(v_e_753_, 0);
lean_inc_ref(v_a_814_);
lean_dec_ref(v_e_753_);
v___x_815_ = l_Int_Linear_Expr_denoteExpr___redArg(v_ctx_752_, v_a_814_);
v_a_816_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_824_ == 0)
{
v___x_818_ = v___x_815_;
v_isShared_819_ = v_isSharedCheck_824_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_815_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_824_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_820_; lean_object* v___x_822_; 
v___x_820_ = l_Lean_mkIntNeg(v_a_816_);
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 0, v___x_820_);
v___x_822_ = v___x_818_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_820_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
case 5:
{
lean_object* v_k_825_; lean_object* v_a_826_; lean_object* v___x_827_; lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_849_; 
v_k_825_ = lean_ctor_get(v_e_753_, 0);
lean_inc(v_k_825_);
v_a_826_ = lean_ctor_get(v_e_753_, 1);
lean_inc_ref(v_a_826_);
lean_dec_ref(v_e_753_);
v___x_827_ = l_Int_Linear_Expr_denoteExpr___redArg(v_ctx_752_, v_a_826_);
v_a_828_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_849_ == 0)
{
v___x_830_ = v___x_827_;
v_isShared_831_ = v_isSharedCheck_849_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_827_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_849_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___y_833_; lean_object* v___x_838_; uint8_t v___x_839_; 
v___x_838_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1);
v___x_839_ = lean_int_dec_le(v___x_838_, v_k_825_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_840_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11);
v___x_841_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13);
v___x_842_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16);
v___x_843_ = lean_int_neg(v_k_825_);
lean_dec(v_k_825_);
v___x_844_ = l_Int_toNat(v___x_843_);
lean_dec(v___x_843_);
v___x_845_ = l_Lean_instToExprInt_mkNat(v___x_844_);
v___x_846_ = l_Lean_mkApp3(v___x_840_, v___x_841_, v___x_842_, v___x_845_);
v___y_833_ = v___x_846_;
goto v___jp_832_;
}
else
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = l_Int_toNat(v_k_825_);
lean_dec(v_k_825_);
v___x_848_ = l_Lean_instToExprInt_mkNat(v___x_847_);
v___y_833_ = v___x_848_;
goto v___jp_832_;
}
v___jp_832_:
{
lean_object* v___x_834_; lean_object* v___x_836_; 
v___x_834_ = l_Lean_mkIntMul(v___y_833_, v_a_828_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v___x_834_);
v___x_836_ = v___x_830_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_834_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
default: 
{
lean_object* v_a_850_; lean_object* v_k_851_; lean_object* v___x_852_; lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_874_; 
v_a_850_ = lean_ctor_get(v_e_753_, 0);
lean_inc_ref(v_a_850_);
v_k_851_ = lean_ctor_get(v_e_753_, 1);
lean_inc(v_k_851_);
lean_dec_ref(v_e_753_);
v___x_852_ = l_Int_Linear_Expr_denoteExpr___redArg(v_ctx_752_, v_a_850_);
v_a_853_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_874_ == 0)
{
v___x_855_ = v___x_852_;
v_isShared_856_ = v_isSharedCheck_874_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_852_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_874_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___y_858_; lean_object* v___x_863_; uint8_t v___x_864_; 
v___x_863_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1);
v___x_864_ = lean_int_dec_le(v___x_863_, v_k_851_);
if (v___x_864_ == 0)
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_865_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11);
v___x_866_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13);
v___x_867_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16);
v___x_868_ = lean_int_neg(v_k_851_);
lean_dec(v_k_851_);
v___x_869_ = l_Int_toNat(v___x_868_);
lean_dec(v___x_868_);
v___x_870_ = l_Lean_instToExprInt_mkNat(v___x_869_);
v___x_871_ = l_Lean_mkApp3(v___x_865_, v___x_866_, v___x_867_, v___x_870_);
v___y_858_ = v___x_871_;
goto v___jp_857_;
}
else
{
lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_872_ = l_Int_toNat(v_k_851_);
lean_dec(v_k_851_);
v___x_873_ = l_Lean_instToExprInt_mkNat(v___x_872_);
v___y_858_ = v___x_873_;
goto v___jp_857_;
}
v___jp_857_:
{
lean_object* v___x_859_; lean_object* v___x_861_; 
v___x_859_ = l_Lean_mkIntMul(v_a_853_, v___y_858_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v___x_859_);
v___x_861_ = v___x_855_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_859_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_denoteExpr___redArg___boxed(lean_object* v_ctx_875_, lean_object* v_e_876_, lean_object* v_a_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Int_Linear_Expr_denoteExpr___redArg(v_ctx_875_, v_e_876_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_denoteExpr(lean_object* v_ctx_879_, lean_object* v_e_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = l_Int_Linear_Expr_denoteExpr___redArg(v_ctx_879_, v_e_880_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_denoteExpr___boxed(lean_object* v_ctx_887_, lean_object* v_e_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_Int_Linear_Expr_denoteExpr(v_ctx_887_, v_e_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
lean_dec(v_a_892_);
lean_dec_ref(v_a_891_);
lean_dec(v_a_890_);
lean_dec_ref(v_a_889_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_denoteExpr_go___redArg(lean_object* v_ctx_895_, lean_object* v_r_896_, lean_object* v_p_897_){
_start:
{
lean_object* v___y_900_; 
if (lean_obj_tag(v_p_897_) == 0)
{
lean_object* v_k_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_922_; 
lean_dec_ref(v_ctx_895_);
v_k_903_ = lean_ctor_get(v_p_897_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v_p_897_);
if (v_isSharedCheck_922_ == 0)
{
v___x_905_ = v_p_897_;
v_isShared_906_ = v_isSharedCheck_922_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_k_903_);
lean_dec(v_p_897_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_922_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_907_; uint8_t v___x_908_; 
v___x_907_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1);
v___x_908_ = lean_int_dec_eq(v_k_903_, v___x_907_);
if (v___x_908_ == 0)
{
uint8_t v___x_909_; 
lean_del_object(v___x_905_);
v___x_909_ = lean_int_dec_le(v___x_907_, v_k_903_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_910_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11);
v___x_911_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13);
v___x_912_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16);
v___x_913_ = lean_int_neg(v_k_903_);
lean_dec(v_k_903_);
v___x_914_ = l_Int_toNat(v___x_913_);
lean_dec(v___x_913_);
v___x_915_ = l_Lean_instToExprInt_mkNat(v___x_914_);
v___x_916_ = l_Lean_mkApp3(v___x_910_, v___x_911_, v___x_912_, v___x_915_);
v___y_900_ = v___x_916_;
goto v___jp_899_;
}
else
{
lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_917_ = l_Int_toNat(v_k_903_);
lean_dec(v_k_903_);
v___x_918_ = l_Lean_instToExprInt_mkNat(v___x_917_);
v___y_900_ = v___x_918_;
goto v___jp_899_;
}
}
else
{
lean_object* v___x_920_; 
lean_dec(v_k_903_);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 0, v_r_896_);
v___x_920_ = v___x_905_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_r_896_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
else
{
lean_object* v_k_923_; lean_object* v_v_924_; lean_object* v_p_925_; lean_object* v___y_927_; lean_object* v___x_932_; uint8_t v___x_933_; 
v_k_923_ = lean_ctor_get(v_p_897_, 0);
lean_inc(v_k_923_);
v_v_924_ = lean_ctor_get(v_p_897_, 1);
lean_inc(v_v_924_);
v_p_925_ = lean_ctor_get(v_p_897_, 2);
lean_inc_ref(v_p_925_);
lean_dec_ref(v_p_897_);
v___x_932_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0);
v___x_933_ = lean_int_dec_eq(v_k_923_, v___x_932_);
if (v___x_933_ == 0)
{
lean_object* v___x_934_; uint8_t v___x_935_; 
v___x_934_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1);
v___x_935_ = lean_int_dec_le(v___x_934_, v_k_923_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_936_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11);
v___x_937_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13);
v___x_938_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16);
v___x_939_ = lean_int_neg(v_k_923_);
lean_dec(v_k_923_);
v___x_940_ = l_Int_toNat(v___x_939_);
lean_dec(v___x_939_);
v___x_941_ = l_Lean_instToExprInt_mkNat(v___x_940_);
v___x_942_ = l_Lean_mkApp3(v___x_936_, v___x_937_, v___x_938_, v___x_941_);
v___y_927_ = v___x_942_;
goto v___jp_926_;
}
else
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = l_Int_toNat(v_k_923_);
lean_dec(v_k_923_);
v___x_944_ = l_Lean_instToExprInt_mkNat(v___x_943_);
v___y_927_ = v___x_944_;
goto v___jp_926_;
}
}
else
{
lean_object* v___x_945_; lean_object* v___x_946_; 
lean_dec(v_k_923_);
lean_inc_ref(v_ctx_895_);
v___x_945_ = lean_apply_1(v_ctx_895_, v_v_924_);
v___x_946_ = l_Lean_mkIntAdd(v_r_896_, v___x_945_);
v_r_896_ = v___x_946_;
v_p_897_ = v_p_925_;
goto _start;
}
v___jp_926_:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
lean_inc_ref(v_ctx_895_);
v___x_928_ = lean_apply_1(v_ctx_895_, v_v_924_);
v___x_929_ = l_Lean_mkIntMul(v___y_927_, v___x_928_);
v___x_930_ = l_Lean_mkIntAdd(v_r_896_, v___x_929_);
v_r_896_ = v___x_930_;
v_p_897_ = v_p_925_;
goto _start;
}
}
v___jp_899_:
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = l_Lean_mkIntAdd(v_r_896_, v___y_900_);
v___x_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_902_, 0, v___x_901_);
return v___x_902_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_denoteExpr_go___redArg___boxed(lean_object* v_ctx_948_, lean_object* v_r_949_, lean_object* v_p_950_, lean_object* v_a_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_denoteExpr_go___redArg(v_ctx_948_, v_r_949_, v_p_950_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_denoteExpr_go(lean_object* v_ctx_953_, lean_object* v_r_954_, lean_object* v_p_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_denoteExpr_go___redArg(v_ctx_953_, v_r_954_, v_p_955_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_denoteExpr_go___boxed(lean_object* v_ctx_962_, lean_object* v_r_963_, lean_object* v_p_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_denoteExpr_go(v_ctx_962_, v_r_963_, v_p_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_);
lean_dec(v_a_968_);
lean_dec_ref(v_a_967_);
lean_dec(v_a_966_);
lean_dec_ref(v_a_965_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr___redArg(lean_object* v_ctx_971_, lean_object* v_p_972_){
_start:
{
if (lean_obj_tag(v_p_972_) == 0)
{
lean_object* v_k_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_995_; 
lean_dec_ref(v_ctx_971_);
v_k_974_ = lean_ctor_get(v_p_972_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v_p_972_);
if (v_isSharedCheck_995_ == 0)
{
v___x_976_ = v_p_972_;
v_isShared_977_ = v_isSharedCheck_995_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_k_974_);
lean_dec(v_p_972_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_995_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_978_; uint8_t v___x_979_; 
v___x_978_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1);
v___x_979_ = lean_int_dec_le(v___x_978_, v_k_974_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_988_; 
v___x_980_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11);
v___x_981_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13);
v___x_982_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16);
v___x_983_ = lean_int_neg(v_k_974_);
lean_dec(v_k_974_);
v___x_984_ = l_Int_toNat(v___x_983_);
lean_dec(v___x_983_);
v___x_985_ = l_Lean_instToExprInt_mkNat(v___x_984_);
v___x_986_ = l_Lean_mkApp3(v___x_980_, v___x_981_, v___x_982_, v___x_985_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 0, v___x_986_);
v___x_988_ = v___x_976_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_986_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
else
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_993_; 
v___x_990_ = l_Int_toNat(v_k_974_);
lean_dec(v_k_974_);
v___x_991_ = l_Lean_instToExprInt_mkNat(v___x_990_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 0, v___x_991_);
v___x_993_ = v___x_976_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_991_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
else
{
lean_object* v_k_996_; lean_object* v_v_997_; lean_object* v_p_998_; lean_object* v___y_1000_; lean_object* v___x_1004_; uint8_t v___x_1005_; 
v_k_996_ = lean_ctor_get(v_p_972_, 0);
lean_inc(v_k_996_);
v_v_997_ = lean_ctor_get(v_p_972_, 1);
lean_inc(v_v_997_);
v_p_998_ = lean_ctor_get(v_p_972_, 2);
lean_inc_ref(v_p_998_);
lean_dec_ref(v_p_972_);
v___x_1004_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0);
v___x_1005_ = lean_int_dec_eq(v_k_996_, v___x_1004_);
if (v___x_1005_ == 0)
{
lean_object* v___x_1006_; uint8_t v___x_1007_; 
v___x_1006_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1);
v___x_1007_ = lean_int_dec_le(v___x_1006_, v_k_996_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1008_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11);
v___x_1009_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13);
v___x_1010_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16);
v___x_1011_ = lean_int_neg(v_k_996_);
lean_dec(v_k_996_);
v___x_1012_ = l_Int_toNat(v___x_1011_);
lean_dec(v___x_1011_);
v___x_1013_ = l_Lean_instToExprInt_mkNat(v___x_1012_);
v___x_1014_ = l_Lean_mkApp3(v___x_1008_, v___x_1009_, v___x_1010_, v___x_1013_);
v___y_1000_ = v___x_1014_;
goto v___jp_999_;
}
else
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = l_Int_toNat(v_k_996_);
lean_dec(v_k_996_);
v___x_1016_ = l_Lean_instToExprInt_mkNat(v___x_1015_);
v___y_1000_ = v___x_1016_;
goto v___jp_999_;
}
}
else
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
lean_dec(v_k_996_);
lean_inc_ref(v_ctx_971_);
v___x_1017_ = lean_apply_1(v_ctx_971_, v_v_997_);
v___x_1018_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_denoteExpr_go___redArg(v_ctx_971_, v___x_1017_, v_p_998_);
return v___x_1018_;
}
v___jp_999_:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
lean_inc_ref(v_ctx_971_);
v___x_1001_ = lean_apply_1(v_ctx_971_, v_v_997_);
v___x_1002_ = l_Lean_mkIntMul(v___y_1000_, v___x_1001_);
v___x_1003_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_denoteExpr_go___redArg(v_ctx_971_, v___x_1002_, v_p_998_);
return v___x_1003_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr___redArg___boxed(lean_object* v_ctx_1019_, lean_object* v_p_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Int_Linear_Poly_denoteExpr___redArg(v_ctx_1019_, v_p_1020_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr(lean_object* v_ctx_1023_, lean_object* v_p_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Int_Linear_Poly_denoteExpr___redArg(v_ctx_1023_, v_p_1024_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr___boxed(lean_object* v_ctx_1031_, lean_object* v_p_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Int_Linear_Poly_denoteExpr(v_ctx_1031_, v_p_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_);
lean_dec(v_a_1036_);
lean_dec_ref(v_a_1035_);
lean_dec(v_a_1034_);
lean_dec_ref(v_a_1033_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(lean_object* v_e_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_){
_start:
{
lean_object* v___x_1046_; lean_object* v_varMap_1047_; lean_object* v___x_1048_; 
v___x_1046_ = lean_st_ref_get(v_a_1040_);
v_varMap_1047_ = lean_ctor_get(v___x_1046_, 0);
lean_inc_ref(v_varMap_1047_);
lean_dec(v___x_1046_);
lean_inc_ref(v_e_1039_);
v___x_1048_ = l_Lean_Meta_KExprMap_find_x3f___redArg(v_varMap_1047_, v_e_1039_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1097_; 
v_a_1049_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1051_ = v___x_1048_;
v_isShared_1052_ = v_isSharedCheck_1097_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_1048_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1097_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
if (lean_obj_tag(v_a_1049_) == 1)
{
lean_object* v_val_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1063_; 
lean_dec_ref(v_e_1039_);
v_val_1053_ = lean_ctor_get(v_a_1049_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v_a_1049_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1055_ = v_a_1049_;
v_isShared_1056_ = v_isSharedCheck_1063_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_val_1053_);
lean_dec(v_a_1049_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1063_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_val_1053_);
v___x_1058_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
lean_object* v___x_1060_; 
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 0, v___x_1058_);
v___x_1060_ = v___x_1051_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_1058_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
else
{
lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v_vars_1066_; lean_object* v_varMap_1067_; lean_object* v_vars_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1096_; 
lean_del_object(v___x_1051_);
lean_dec(v_a_1049_);
v___x_1064_ = lean_st_ref_get(v_a_1040_);
v___x_1065_ = lean_st_ref_get(v_a_1040_);
v_vars_1066_ = lean_ctor_get(v___x_1064_, 1);
lean_inc_ref(v_vars_1066_);
lean_dec(v___x_1064_);
v_varMap_1067_ = lean_ctor_get(v___x_1065_, 0);
v_vars_1068_ = lean_ctor_get(v___x_1065_, 1);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1065_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1070_ = v___x_1065_;
v_isShared_1071_ = v_isSharedCheck_1096_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_vars_1068_);
lean_inc(v_varMap_1067_);
lean_dec(v___x_1065_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1096_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = lean_array_get_size(v_vars_1066_);
lean_dec_ref(v_vars_1066_);
lean_inc_ref(v_e_1039_);
v___x_1073_ = l_Lean_Meta_KExprMap_insert___redArg(v_varMap_1067_, v_e_1039_, v___x_1072_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1087_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1076_ = v___x_1073_;
v_isShared_1077_ = v_isSharedCheck_1087_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1073_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1087_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1078_; lean_object* v___x_1080_; 
v___x_1078_ = lean_array_push(v_vars_1068_, v_e_1039_);
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 1, v___x_1078_);
lean_ctor_set(v___x_1070_, 0, v_a_1074_);
v___x_1080_ = v___x_1070_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1074_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1084_; 
v___x_1081_ = lean_st_ref_set(v_a_1040_, v___x_1080_);
v___x_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1072_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 0, v___x_1082_);
v___x_1084_ = v___x_1076_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1082_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
lean_del_object(v___x_1070_);
lean_dec_ref(v_vars_1068_);
lean_dec_ref(v_e_1039_);
v_a_1088_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1073_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1073_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
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
}
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
lean_dec_ref(v_e_1039_);
v_a_1098_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1048_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1048_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar___boxed(lean_object* v_e_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_);
lean_dec(v_a_1111_);
lean_dec_ref(v_a_1110_);
lean_dec(v_a_1109_);
lean_dec_ref(v_a_1108_);
lean_dec(v_a_1107_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit(lean_object* v_e_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_){
_start:
{
lean_object* v___x_1166_; 
lean_inc_ref(v_e_1159_);
v___x_1166_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1159_, v_a_1162_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_a_1167_; lean_object* v___x_1168_; uint8_t v___x_1169_; 
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
lean_inc(v_a_1167_);
lean_dec_ref(v___x_1166_);
v___x_1168_ = l_Lean_Expr_cleanupAnnotations(v_a_1167_);
v___x_1169_ = l_Lean_Expr_isApp(v___x_1168_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1170_; 
lean_dec_ref(v___x_1168_);
v___x_1170_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
return v___x_1170_;
}
else
{
lean_object* v_arg_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; uint8_t v___x_1174_; 
v_arg_1171_ = lean_ctor_get(v___x_1168_, 1);
lean_inc_ref(v_arg_1171_);
v___x_1172_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1168_);
v___x_1173_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__0));
v___x_1174_ = l_Lean_Expr_isConstOf(v___x_1172_, v___x_1173_);
if (v___x_1174_ == 0)
{
uint8_t v___x_1175_; 
v___x_1175_ = l_Lean_Expr_isApp(v___x_1172_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; 
lean_dec_ref(v___x_1172_);
lean_dec_ref(v_arg_1171_);
v___x_1176_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
return v___x_1176_;
}
else
{
lean_object* v_arg_1177_; lean_object* v_b_1179_; lean_object* v___y_1180_; lean_object* v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___x_1228_; lean_object* v___x_1229_; uint8_t v___x_1230_; 
v_arg_1177_ = lean_ctor_get(v___x_1172_, 1);
lean_inc_ref(v_arg_1177_);
v___x_1228_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1172_);
v___x_1229_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__2));
v___x_1230_ = l_Lean_Expr_isConstOf(v___x_1228_, v___x_1229_);
if (v___x_1230_ == 0)
{
lean_object* v___x_1231_; uint8_t v___x_1232_; 
v___x_1231_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__3));
v___x_1232_ = l_Lean_Expr_isConstOf(v___x_1228_, v___x_1231_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1233_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__4));
v___x_1234_ = l_Lean_Expr_isConstOf(v___x_1228_, v___x_1233_);
if (v___x_1234_ == 0)
{
uint8_t v___x_1235_; 
v___x_1235_ = l_Lean_Expr_isApp(v___x_1228_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1236_; 
lean_dec_ref(v___x_1228_);
lean_dec_ref(v_arg_1177_);
lean_dec_ref(v_arg_1171_);
v___x_1236_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
return v___x_1236_;
}
else
{
lean_object* v_arg_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; uint8_t v___x_1240_; 
v_arg_1237_ = lean_ctor_get(v___x_1228_, 1);
lean_inc_ref(v_arg_1237_);
v___x_1238_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1228_);
v___x_1239_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__8));
v___x_1240_ = l_Lean_Expr_isConstOf(v___x_1238_, v___x_1239_);
if (v___x_1240_ == 0)
{
lean_object* v___x_1241_; uint8_t v___x_1242_; 
v___x_1241_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__7));
v___x_1242_ = l_Lean_Expr_isConstOf(v___x_1238_, v___x_1241_);
if (v___x_1242_ == 0)
{
uint8_t v___x_1243_; 
v___x_1243_ = l_Lean_Expr_isApp(v___x_1238_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; 
lean_dec_ref(v___x_1238_);
lean_dec_ref(v_arg_1237_);
lean_dec_ref(v_arg_1177_);
lean_dec_ref(v_arg_1171_);
v___x_1244_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
return v___x_1244_;
}
else
{
lean_object* v___x_1245_; lean_object* v___x_1246_; uint8_t v___x_1247_; 
v___x_1245_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1238_);
v___x_1246_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__9));
v___x_1247_ = l_Lean_Expr_isConstOf(v___x_1245_, v___x_1246_);
if (v___x_1247_ == 0)
{
lean_object* v___x_1248_; uint8_t v___x_1249_; 
v___x_1248_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__11));
v___x_1249_ = l_Lean_Expr_isConstOf(v___x_1245_, v___x_1248_);
if (v___x_1249_ == 0)
{
lean_object* v___x_1250_; uint8_t v___x_1251_; 
v___x_1250_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__13));
v___x_1251_ = l_Lean_Expr_isConstOf(v___x_1245_, v___x_1250_);
if (v___x_1251_ == 0)
{
uint8_t v___x_1252_; 
v___x_1252_ = l_Lean_Expr_isApp(v___x_1245_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; 
lean_dec_ref(v___x_1245_);
lean_dec_ref(v_arg_1237_);
lean_dec_ref(v_arg_1177_);
lean_dec_ref(v_arg_1171_);
v___x_1253_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
return v___x_1253_;
}
else
{
lean_object* v___x_1254_; uint8_t v___x_1255_; 
v___x_1254_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1245_);
v___x_1255_ = l_Lean_Expr_isApp(v___x_1254_);
if (v___x_1255_ == 0)
{
lean_object* v___x_1256_; 
lean_dec_ref(v___x_1254_);
lean_dec_ref(v_arg_1237_);
lean_dec_ref(v_arg_1177_);
lean_dec_ref(v_arg_1171_);
v___x_1256_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
return v___x_1256_;
}
else
{
lean_object* v___x_1257_; lean_object* v___x_1258_; uint8_t v___x_1259_; 
v___x_1257_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1254_);
v___x_1258_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__16));
v___x_1259_ = l_Lean_Expr_isConstOf(v___x_1257_, v___x_1258_);
if (v___x_1259_ == 0)
{
lean_object* v___x_1260_; uint8_t v___x_1261_; 
v___x_1260_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__19));
v___x_1261_ = l_Lean_Expr_isConstOf(v___x_1257_, v___x_1260_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1262_; uint8_t v___x_1263_; 
v___x_1262_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__22));
v___x_1263_ = l_Lean_Expr_isConstOf(v___x_1257_, v___x_1262_);
lean_dec_ref(v___x_1257_);
if (v___x_1263_ == 0)
{
lean_object* v___x_1264_; 
lean_dec_ref(v_arg_1237_);
lean_dec_ref(v_arg_1177_);
lean_dec_ref(v_arg_1171_);
v___x_1264_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
return v___x_1264_;
}
else
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Lean_Meta_DefEq_isInstHAddInt(v_arg_1237_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; uint8_t v___x_1267_; 
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_a_1266_);
lean_dec_ref(v___x_1265_);
v___x_1267_ = lean_unbox(v_a_1266_);
lean_dec(v_a_1266_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; 
lean_dec_ref(v_arg_1177_);
lean_dec_ref(v_arg_1171_);
v___x_1268_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
return v___x_1268_;
}
else
{
lean_object* v___x_1269_; 
lean_dec_ref(v_e_1159_);
v___x_1269_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1177_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; lean_object* v___x_1271_; 
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_a_1270_);
lean_dec_ref(v___x_1269_);
v___x_1271_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1171_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1280_; 
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1274_ = v___x_1271_;
v_isShared_1275_ = v_isSharedCheck_1280_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1271_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1280_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1276_; lean_object* v___x_1278_; 
v___x_1276_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1276_, 0, v_a_1270_);
lean_ctor_set(v___x_1276_, 1, v_a_1272_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 0, v___x_1276_);
v___x_1278_ = v___x_1274_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1276_);
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
lean_dec(v_a_1270_);
return v___x_1271_;
}
}
else
{
lean_dec_ref(v_arg_1171_);
return v___x_1269_;
}
}
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
lean_dec_ref(v_arg_1177_);
lean_dec_ref(v_arg_1171_);
lean_dec_ref(v_e_1159_);
v_a_1281_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1265_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1265_);
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
else
{
lean_object* v___x_1289_; 
lean_dec_ref(v___x_1257_);
v___x_1289_ = l_Lean_Meta_DefEq_isInstHSubInt(v_arg_1237_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_object* v_a_1290_; uint8_t v___x_1291_; 
v_a_1290_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_a_1290_);
lean_dec_ref(v___x_1289_);
v___x_1291_ = lean_unbox(v_a_1290_);
lean_dec(v_a_1290_);
if (v___x_1291_ == 0)
{
lean_object* v___x_1292_; 
lean_dec_ref(v_arg_1177_);
lean_dec_ref(v_arg_1171_);
v___x_1292_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
return v___x_1292_;
}
else
{
lean_object* v___x_1293_; 
lean_dec_ref(v_e_1159_);
v___x_1293_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1177_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; lean_object* v___x_1295_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_a_1294_);
lean_dec_ref(v___x_1293_);
v___x_1295_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1171_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1304_; 
v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1298_ = v___x_1295_;
v_isShared_1299_ = v_isSharedCheck_1304_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1295_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1304_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1300_; lean_object* v___x_1302_; 
v___x_1300_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1300_, 0, v_a_1294_);
lean_ctor_set(v___x_1300_, 1, v_a_1296_);
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 0, v___x_1300_);
v___x_1302_ = v___x_1298_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1300_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
else
{
lean_dec(v_a_1294_);
return v___x_1295_;
}
}
else
{
lean_dec_ref(v_arg_1171_);
return v___x_1293_;
}
}
}
else
{
lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1312_; 
lean_dec_ref(v_arg_1177_);
lean_dec_ref(v_arg_1171_);
lean_dec_ref(v_e_1159_);
v_a_1305_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1307_ = v___x_1289_;
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1289_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1310_; 
if (v_isShared_1308_ == 0)
{
v___x_1310_ = v___x_1307_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1305_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
}
}
else
{
lean_object* v___x_1313_; 
lean_dec_ref(v___x_1257_);
v___x_1313_ = l_Lean_Meta_DefEq_isInstHMulInt(v_arg_1237_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v_a_1314_; uint8_t v___x_1315_; 
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_a_1314_);
lean_dec_ref(v___x_1313_);
v___x_1315_ = lean_unbox(v_a_1314_);
lean_dec(v_a_1314_);
if (v___x_1315_ == 0)
{
lean_object* v___x_1316_; 
lean_dec_ref(v_arg_1177_);
lean_dec_ref(v_arg_1171_);
v___x_1316_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
return v___x_1316_;
}
else
{
v_b_1179_ = v_arg_1171_;
v___y_1180_ = v_a_1160_;
v___y_1181_ = v_a_1161_;
v___y_1182_ = v_a_1162_;
v___y_1183_ = v_a_1163_;
v___y_1184_ = v_a_1164_;
goto v___jp_1178_;
}
}
else
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
lean_dec_ref(v_arg_1177_);
lean_dec_ref(v_arg_1171_);
lean_dec_ref(v_e_1159_);
v_a_1317_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1313_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1313_);
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
}
}
}
else
{
lean_object* v___x_1325_; 
lean_dec_ref(v___x_1245_);
v___x_1325_ = l_Lean_Meta_DefEq_isInstAddInt(v_arg_1237_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; uint8_t v___x_1327_; 
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_a_1326_);
lean_dec_ref(v___x_1325_);
v___x_1327_ = lean_unbox(v_a_1326_);
lean_dec(v_a_1326_);
if (v___x_1327_ == 0)
{
lean_object* v___x_1328_; 
lean_dec_ref(v_arg_1177_);
lean_dec_ref(v_arg_1171_);
v___x_1328_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
return v___x_1328_;
}
else
{
lean_object* v___x_1329_; 
lean_dec_ref(v_e_1159_);
v___x_1329_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1177_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v_a_1330_; lean_object* v___x_1331_; 
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
lean_inc(v_a_1330_);
lean_dec_ref(v___x_1329_);
v___x_1331_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1171_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1340_; 
v_a_1332_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1334_ = v___x_1331_;
v_isShared_1335_ = v_isSharedCheck_1340_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1331_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1340_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1336_; lean_object* v___x_1338_; 
v___x_1336_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1336_, 0, v_a_1330_);
lean_ctor_set(v___x_1336_, 1, v_a_1332_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 0, v___x_1336_);
v___x_1338_ = v___x_1334_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1336_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
else
{
lean_dec(v_a_1330_);
return v___x_1331_;
}
}
else
{
lean_dec_ref(v_arg_1171_);
return v___x_1329_;
}
}
}
else
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
lean_dec_ref(v_arg_1177_);
lean_dec_ref(v_arg_1171_);
lean_dec_ref(v_e_1159_);
v_a_1341_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___x_1325_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1325_);
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
else
{
lean_object* v___x_1349_; 
lean_dec_ref(v___x_1245_);
v___x_1349_ = l_Lean_Meta_DefEq_isInstSubInt(v_arg_1237_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; uint8_t v___x_1351_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_a_1350_);
lean_dec_ref(v___x_1349_);
v___x_1351_ = lean_unbox(v_a_1350_);
lean_dec(v_a_1350_);
if (v___x_1351_ == 0)
{
lean_object* v___x_1352_; 
lean_dec_ref(v_arg_1177_);
lean_dec_ref(v_arg_1171_);
v___x_1352_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
return v___x_1352_;
}
else
{
lean_object* v___x_1353_; 
lean_dec_ref(v_e_1159_);
v___x_1353_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1177_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v_a_1354_; lean_object* v___x_1355_; 
v_a_1354_ = lean_ctor_get(v___x_1353_, 0);
lean_inc(v_a_1354_);
lean_dec_ref(v___x_1353_);
v___x_1355_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1171_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1364_; 
v_a_1356_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1358_ = v___x_1355_;
v_isShared_1359_ = v_isSharedCheck_1364_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1355_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1364_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1360_; lean_object* v___x_1362_; 
v___x_1360_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1360_, 0, v_a_1354_);
lean_ctor_set(v___x_1360_, 1, v_a_1356_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 0, v___x_1360_);
v___x_1362_ = v___x_1358_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v___x_1360_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
else
{
lean_dec(v_a_1354_);
return v___x_1355_;
}
}
else
{
lean_dec_ref(v_arg_1171_);
return v___x_1353_;
}
}
}
else
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
lean_dec_ref(v_arg_1177_);
lean_dec_ref(v_arg_1171_);
lean_dec_ref(v_e_1159_);
v_a_1365_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1349_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1349_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
}
else
{
lean_object* v___x_1373_; 
lean_dec_ref(v___x_1245_);
v___x_1373_ = l_Lean_Meta_DefEq_isInstMulInt(v_arg_1237_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v_a_1374_; uint8_t v___x_1375_; 
v_a_1374_ = lean_ctor_get(v___x_1373_, 0);
lean_inc(v_a_1374_);
lean_dec_ref(v___x_1373_);
v___x_1375_ = lean_unbox(v_a_1374_);
lean_dec(v_a_1374_);
if (v___x_1375_ == 0)
{
lean_object* v___x_1376_; 
lean_dec_ref(v_arg_1177_);
lean_dec_ref(v_arg_1171_);
v___x_1376_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
return v___x_1376_;
}
else
{
v_b_1179_ = v_arg_1171_;
v___y_1180_ = v_a_1160_;
v___y_1181_ = v_a_1161_;
v___y_1182_ = v_a_1162_;
v___y_1183_ = v_a_1163_;
v___y_1184_ = v_a_1164_;
goto v___jp_1178_;
}
}
else
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
lean_dec_ref(v_arg_1177_);
lean_dec_ref(v_arg_1171_);
lean_dec_ref(v_e_1159_);
v_a_1377_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1379_ = v___x_1373_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1373_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1377_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
}
}
else
{
lean_object* v___x_1385_; 
lean_dec_ref(v___x_1238_);
lean_dec_ref(v_arg_1237_);
lean_dec_ref(v_arg_1177_);
lean_dec_ref(v_arg_1171_);
lean_inc_ref(v_e_1159_);
v___x_1385_ = l_Lean_Meta_getIntValue_x3f(v_e_1159_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1402_; 
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1388_ = v___x_1385_;
v_isShared_1389_ = v_isSharedCheck_1402_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1385_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1402_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
if (lean_obj_tag(v_a_1386_) == 1)
{
lean_object* v_val_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1400_; 
lean_dec_ref(v_e_1159_);
v_val_1390_ = lean_ctor_get(v_a_1386_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v_a_1386_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1392_ = v_a_1386_;
v_isShared_1393_ = v_isSharedCheck_1400_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_val_1390_);
lean_dec(v_a_1386_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1400_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1395_; 
if (v_isShared_1393_ == 0)
{
lean_ctor_set_tag(v___x_1392_, 0);
v___x_1395_ = v___x_1392_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_val_1390_);
v___x_1395_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
lean_object* v___x_1397_; 
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 0, v___x_1395_);
v___x_1397_ = v___x_1388_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1395_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
}
else
{
lean_object* v___x_1401_; 
lean_del_object(v___x_1388_);
lean_dec(v_a_1386_);
v___x_1401_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
return v___x_1401_;
}
}
}
else
{
lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1410_; 
lean_dec_ref(v_e_1159_);
v_a_1403_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1405_ = v___x_1385_;
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1385_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1408_; 
if (v_isShared_1406_ == 0)
{
v___x_1408_ = v___x_1405_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1403_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
}
}
else
{
lean_object* v___x_1411_; 
lean_dec_ref(v___x_1238_);
lean_dec_ref(v_arg_1237_);
v___x_1411_ = l_Lean_Meta_DefEq_isInstNegInt(v_arg_1177_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_a_1412_; uint8_t v___x_1413_; 
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_a_1412_);
lean_dec_ref(v___x_1411_);
v___x_1413_ = lean_unbox(v_a_1412_);
lean_dec(v_a_1412_);
if (v___x_1413_ == 0)
{
lean_object* v___x_1414_; 
lean_dec_ref(v_arg_1171_);
v___x_1414_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
return v___x_1414_;
}
else
{
lean_object* v___x_1415_; 
lean_dec_ref(v_e_1159_);
v___x_1415_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1171_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1424_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1418_ = v___x_1415_;
v_isShared_1419_ = v_isSharedCheck_1424_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1415_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1424_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1420_; lean_object* v___x_1422_; 
v___x_1420_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1420_, 0, v_a_1416_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v___x_1420_);
v___x_1422_ = v___x_1418_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1420_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
else
{
return v___x_1415_;
}
}
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
lean_dec_ref(v_arg_1171_);
lean_dec_ref(v_e_1159_);
v_a_1425_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1411_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1411_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1430_; 
if (v_isShared_1428_ == 0)
{
v___x_1430_ = v___x_1427_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1425_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
return v___x_1430_;
}
}
}
}
}
}
else
{
lean_object* v___x_1433_; 
lean_dec_ref(v___x_1228_);
lean_dec_ref(v_e_1159_);
v___x_1433_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1177_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; lean_object* v___x_1435_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_a_1434_);
lean_dec_ref(v___x_1433_);
v___x_1435_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1171_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1444_; 
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1438_ = v___x_1435_;
v_isShared_1439_ = v_isSharedCheck_1444_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1435_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1444_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1440_; lean_object* v___x_1442_; 
v___x_1440_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1440_, 0, v_a_1434_);
lean_ctor_set(v___x_1440_, 1, v_a_1436_);
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 0, v___x_1440_);
v___x_1442_ = v___x_1438_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1440_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
else
{
lean_dec(v_a_1434_);
return v___x_1435_;
}
}
else
{
lean_dec_ref(v_arg_1171_);
return v___x_1433_;
}
}
}
else
{
lean_object* v___x_1445_; 
lean_dec_ref(v___x_1228_);
lean_dec_ref(v_e_1159_);
v___x_1445_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1177_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v_a_1446_; lean_object* v___x_1447_; 
v_a_1446_ = lean_ctor_get(v___x_1445_, 0);
lean_inc(v_a_1446_);
lean_dec_ref(v___x_1445_);
v___x_1447_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1171_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1456_; 
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1450_ = v___x_1447_;
v_isShared_1451_ = v_isSharedCheck_1456_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1447_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1456_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1452_; lean_object* v___x_1454_; 
v___x_1452_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1452_, 0, v_a_1446_);
lean_ctor_set(v___x_1452_, 1, v_a_1448_);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 0, v___x_1452_);
v___x_1454_ = v___x_1450_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1452_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
else
{
lean_dec(v_a_1446_);
return v___x_1447_;
}
}
else
{
lean_dec_ref(v_arg_1171_);
return v___x_1445_;
}
}
}
else
{
lean_dec_ref(v___x_1228_);
v_b_1179_ = v_arg_1171_;
v___y_1180_ = v_a_1160_;
v___y_1181_ = v_a_1161_;
v___y_1182_ = v_a_1162_;
v___y_1183_ = v_a_1163_;
v___y_1184_ = v_a_1164_;
goto v___jp_1178_;
}
v___jp_1178_:
{
lean_object* v___x_1185_; 
lean_inc_ref(v_arg_1177_);
v___x_1185_ = l_Lean_Meta_getIntValue_x3f(v_arg_1177_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1186_; 
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
lean_inc(v_a_1186_);
lean_dec_ref(v___x_1185_);
if (lean_obj_tag(v_a_1186_) == 0)
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Lean_Meta_getIntValue_x3f(v_b_1179_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v_a_1188_; 
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_a_1188_);
lean_dec_ref(v___x_1187_);
if (lean_obj_tag(v_a_1188_) == 0)
{
lean_object* v___x_1189_; 
lean_dec_ref(v_arg_1177_);
v___x_1189_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1159_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
return v___x_1189_;
}
else
{
lean_object* v_val_1190_; lean_object* v___x_1191_; 
lean_dec_ref(v_e_1159_);
v_val_1190_ = lean_ctor_get(v_a_1188_, 0);
lean_inc(v_val_1190_);
lean_dec_ref(v_a_1188_);
v___x_1191_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1177_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1200_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1194_ = v___x_1191_;
v_isShared_1195_ = v_isSharedCheck_1200_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1191_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1200_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1196_; lean_object* v___x_1198_; 
v___x_1196_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1196_, 0, v_a_1192_);
lean_ctor_set(v___x_1196_, 1, v_val_1190_);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 0, v___x_1196_);
v___x_1198_ = v___x_1194_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
else
{
lean_dec(v_val_1190_);
return v___x_1191_;
}
}
}
else
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1208_; 
lean_dec_ref(v_arg_1177_);
lean_dec_ref(v_e_1159_);
v_a_1201_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1203_ = v___x_1187_;
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1187_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1206_; 
if (v_isShared_1204_ == 0)
{
v___x_1206_ = v___x_1203_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_a_1201_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
else
{
lean_object* v_val_1209_; lean_object* v___x_1210_; 
lean_dec_ref(v_arg_1177_);
lean_dec_ref(v_e_1159_);
v_val_1209_ = lean_ctor_get(v_a_1186_, 0);
lean_inc(v_val_1209_);
lean_dec_ref(v_a_1186_);
v___x_1210_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_b_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1219_; 
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1213_ = v___x_1210_;
v_isShared_1214_ = v_isSharedCheck_1219_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1210_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1219_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1215_; lean_object* v___x_1217_; 
v___x_1215_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1215_, 0, v_val_1209_);
lean_ctor_set(v___x_1215_, 1, v_a_1211_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v___x_1215_);
v___x_1217_ = v___x_1213_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1215_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
else
{
lean_dec(v_val_1209_);
return v___x_1210_;
}
}
}
else
{
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
lean_dec_ref(v_b_1179_);
lean_dec_ref(v_arg_1177_);
lean_dec_ref(v_e_1159_);
v_a_1220_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___x_1185_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1185_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
}
}
else
{
lean_object* v___x_1457_; 
lean_dec_ref(v___x_1172_);
lean_dec_ref(v_e_1159_);
v___x_1457_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1171_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1466_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1460_ = v___x_1457_;
v_isShared_1461_ = v_isSharedCheck_1466_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1457_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1466_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1462_; lean_object* v___x_1464_; 
v___x_1462_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1462_, 0, v_a_1458_);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 0, v___x_1462_);
v___x_1464_ = v___x_1460_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1462_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
else
{
return v___x_1457_;
}
}
}
}
else
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1474_; 
lean_dec_ref(v_e_1159_);
v_a_1467_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1469_ = v___x_1166_;
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1166_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1467_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(lean_object* v_e_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_){
_start:
{
switch(lean_obj_tag(v_e_1475_))
{
case 10:
{
lean_object* v_expr_1482_; 
v_expr_1482_ = lean_ctor_get(v_e_1475_, 1);
lean_inc_ref(v_expr_1482_);
lean_dec_ref(v_e_1475_);
v_e_1475_ = v_expr_1482_;
goto _start;
}
case 5:
{
lean_object* v___x_1484_; 
v___x_1484_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit(v_e_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_);
return v___x_1484_;
}
case 2:
{
lean_object* v___x_1485_; 
v___x_1485_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit(v_e_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_);
return v___x_1485_;
}
default: 
{
lean_object* v___x_1486_; 
v___x_1486_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_);
return v___x_1486_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr___boxed(lean_object* v_e_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_e_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_);
lean_dec(v_a_1492_);
lean_dec_ref(v_a_1491_);
lean_dec(v_a_1490_);
lean_dec_ref(v_a_1489_);
lean_dec(v_a_1488_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___boxed(lean_object* v_e_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit(v_e_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_);
lean_dec(v_a_1500_);
lean_dec_ref(v_a_1499_);
lean_dec(v_a_1498_);
lean_dec_ref(v_a_1497_);
lean_dec(v_a_1496_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f(lean_object* v_e_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1506_, v_a_1509_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1602_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1516_ = v___x_1513_;
v_isShared_1517_ = v_isSharedCheck_1602_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1513_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1602_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1523_; uint8_t v___x_1524_; 
v___x_1523_ = l_Lean_Expr_cleanupAnnotations(v_a_1514_);
v___x_1524_ = l_Lean_Expr_isApp(v___x_1523_);
if (v___x_1524_ == 0)
{
lean_dec_ref(v___x_1523_);
goto v___jp_1518_;
}
else
{
lean_object* v_arg_1525_; lean_object* v___x_1526_; uint8_t v___x_1527_; 
v_arg_1525_ = lean_ctor_get(v___x_1523_, 1);
lean_inc_ref(v_arg_1525_);
v___x_1526_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1523_);
v___x_1527_ = l_Lean_Expr_isApp(v___x_1526_);
if (v___x_1527_ == 0)
{
lean_dec_ref(v___x_1526_);
lean_dec_ref(v_arg_1525_);
goto v___jp_1518_;
}
else
{
lean_object* v_arg_1528_; lean_object* v___x_1529_; uint8_t v___x_1530_; 
v_arg_1528_ = lean_ctor_get(v___x_1526_, 1);
lean_inc_ref(v_arg_1528_);
v___x_1529_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1526_);
v___x_1530_ = l_Lean_Expr_isApp(v___x_1529_);
if (v___x_1530_ == 0)
{
lean_dec_ref(v___x_1529_);
lean_dec_ref(v_arg_1528_);
lean_dec_ref(v_arg_1525_);
goto v___jp_1518_;
}
else
{
lean_object* v_arg_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; uint8_t v___x_1534_; 
v_arg_1531_ = lean_ctor_get(v___x_1529_, 1);
lean_inc_ref(v_arg_1531_);
v___x_1532_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1529_);
v___x_1533_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___closed__1));
v___x_1534_ = l_Lean_Expr_isConstOf(v___x_1532_, v___x_1533_);
lean_dec_ref(v___x_1532_);
if (v___x_1534_ == 0)
{
lean_dec_ref(v_arg_1531_);
lean_dec_ref(v_arg_1528_);
lean_dec_ref(v_arg_1525_);
goto v___jp_1518_;
}
else
{
lean_object* v___x_1535_; 
lean_del_object(v___x_1516_);
v___x_1535_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1531_, v_a_1509_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1593_; 
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1538_ = v___x_1535_;
v_isShared_1539_ = v_isSharedCheck_1593_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1535_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1593_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; uint8_t v___x_1542_; 
v___x_1540_ = l_Lean_Expr_cleanupAnnotations(v_a_1536_);
v___x_1541_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12));
v___x_1542_ = l_Lean_Expr_isConstOf(v___x_1540_, v___x_1541_);
lean_dec_ref(v___x_1540_);
if (v___x_1542_ == 0)
{
lean_object* v___x_1543_; lean_object* v___x_1545_; 
lean_dec_ref(v_arg_1528_);
lean_dec_ref(v_arg_1525_);
v___x_1543_ = lean_box(0);
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 0, v___x_1543_);
v___x_1545_ = v___x_1538_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1543_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
else
{
lean_object* v___x_1547_; 
lean_del_object(v___x_1538_);
v___x_1547_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1528_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1584_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1550_ = v___x_1547_;
v_isShared_1551_ = v_isSharedCheck_1584_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1547_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1584_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1552_; 
v___x_1552_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1525_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1575_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1555_ = v___x_1552_;
v_isShared_1556_ = v_isSharedCheck_1575_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1552_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1575_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
switch(lean_obj_tag(v_a_1548_))
{
case 1:
{
switch(lean_obj_tag(v_a_1553_))
{
case 1:
{
lean_object* v___x_1563_; lean_object* v___x_1565_; 
lean_dec_ref(v_a_1553_);
lean_dec_ref(v_a_1548_);
lean_del_object(v___x_1555_);
v___x_1563_ = lean_box(0);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 0, v___x_1563_);
v___x_1565_ = v___x_1550_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1563_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
case 0:
{
lean_object* v___x_1567_; lean_object* v___x_1569_; 
lean_dec_ref(v_a_1553_);
lean_dec_ref(v_a_1548_);
lean_del_object(v___x_1555_);
v___x_1567_ = lean_box(0);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 0, v___x_1567_);
v___x_1569_ = v___x_1550_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1567_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
default: 
{
lean_del_object(v___x_1550_);
goto v___jp_1557_;
}
}
}
case 0:
{
if (lean_obj_tag(v_a_1553_) == 1)
{
lean_object* v___x_1571_; lean_object* v___x_1573_; 
lean_dec_ref(v_a_1553_);
lean_dec_ref(v_a_1548_);
lean_del_object(v___x_1555_);
v___x_1571_ = lean_box(0);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 0, v___x_1571_);
v___x_1573_ = v___x_1550_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1571_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
else
{
lean_del_object(v___x_1550_);
goto v___jp_1557_;
}
}
default: 
{
lean_del_object(v___x_1550_);
goto v___jp_1557_;
}
}
v___jp_1557_:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1561_; 
v___x_1558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1558_, 0, v_a_1548_);
lean_ctor_set(v___x_1558_, 1, v_a_1553_);
v___x_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1558_);
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v___x_1559_);
v___x_1561_ = v___x_1555_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1559_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
else
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
lean_del_object(v___x_1550_);
lean_dec(v_a_1548_);
v_a_1576_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1578_ = v___x_1552_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1552_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1576_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
}
else
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
lean_dec_ref(v_arg_1525_);
v_a_1585_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v___x_1547_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1547_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1585_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
}
}
else
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
lean_dec_ref(v_arg_1528_);
lean_dec_ref(v_arg_1525_);
v_a_1594_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1596_ = v___x_1535_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1535_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1594_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
}
}
}
v___jp_1518_:
{
lean_object* v___x_1519_; lean_object* v___x_1521_; 
v___x_1519_ = lean_box(0);
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 0, v___x_1519_);
v___x_1521_ = v___x_1516_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1519_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
}
else
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
v_a_1603_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1513_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1513_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___boxed(lean_object* v_e_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f(v_e_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_);
lean_dec(v_a_1616_);
lean_dec_ref(v_a_1615_);
lean_dec(v_a_1614_);
lean_dec_ref(v_a_1613_);
lean_dec(v_a_1612_);
return v_res_1618_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14(void){
_start:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1645_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0);
v___x_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1645_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f(lean_object* v_e_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1647_, v_a_1650_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v_a_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1944_; 
v_a_1655_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1657_ = v___x_1654_;
v_isShared_1658_ = v_isSharedCheck_1944_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_dec(v___x_1654_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1944_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1664_; uint8_t v___x_1665_; 
v___x_1664_ = l_Lean_Expr_cleanupAnnotations(v_a_1655_);
v___x_1665_ = l_Lean_Expr_isApp(v___x_1664_);
if (v___x_1665_ == 0)
{
lean_dec_ref(v___x_1664_);
goto v___jp_1659_;
}
else
{
lean_object* v_arg_1666_; lean_object* v___x_1667_; uint8_t v___x_1668_; 
v_arg_1666_ = lean_ctor_get(v___x_1664_, 1);
lean_inc_ref(v_arg_1666_);
v___x_1667_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1664_);
v___x_1668_ = l_Lean_Expr_isApp(v___x_1667_);
if (v___x_1668_ == 0)
{
lean_dec_ref(v___x_1667_);
lean_dec_ref(v_arg_1666_);
goto v___jp_1659_;
}
else
{
lean_object* v_arg_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; uint8_t v___x_1672_; 
v_arg_1669_ = lean_ctor_get(v___x_1667_, 1);
lean_inc_ref(v_arg_1669_);
v___x_1670_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1667_);
v___x_1671_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__1));
v___x_1672_ = l_Lean_Expr_isConstOf(v___x_1670_, v___x_1671_);
if (v___x_1672_ == 0)
{
lean_object* v___x_1673_; uint8_t v___x_1674_; 
v___x_1673_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__3));
v___x_1674_ = l_Lean_Expr_isConstOf(v___x_1670_, v___x_1673_);
if (v___x_1674_ == 0)
{
uint8_t v___x_1675_; 
v___x_1675_ = l_Lean_Expr_isApp(v___x_1670_);
if (v___x_1675_ == 0)
{
lean_dec_ref(v___x_1670_);
lean_dec_ref(v_arg_1669_);
lean_dec_ref(v_arg_1666_);
goto v___jp_1659_;
}
else
{
lean_object* v_arg_1676_; lean_object* v___x_1677_; uint8_t v___x_1678_; 
v_arg_1676_ = lean_ctor_get(v___x_1670_, 1);
lean_inc_ref(v_arg_1676_);
v___x_1677_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1670_);
v___x_1678_ = l_Lean_Expr_isApp(v___x_1677_);
if (v___x_1678_ == 0)
{
lean_dec_ref(v___x_1677_);
lean_dec_ref(v_arg_1676_);
lean_dec_ref(v_arg_1669_);
lean_dec_ref(v_arg_1666_);
goto v___jp_1659_;
}
else
{
lean_object* v___x_1679_; lean_object* v___x_1680_; uint8_t v___x_1681_; 
v___x_1679_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1677_);
v___x_1680_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__6));
v___x_1681_ = l_Lean_Expr_isConstOf(v___x_1679_, v___x_1680_);
if (v___x_1681_ == 0)
{
lean_object* v___x_1682_; uint8_t v___x_1683_; 
v___x_1682_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__9));
v___x_1683_ = l_Lean_Expr_isConstOf(v___x_1679_, v___x_1682_);
if (v___x_1683_ == 0)
{
lean_object* v___x_1684_; uint8_t v___x_1685_; 
v___x_1684_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__11));
v___x_1685_ = l_Lean_Expr_isConstOf(v___x_1679_, v___x_1684_);
if (v___x_1685_ == 0)
{
lean_object* v___x_1686_; uint8_t v___x_1687_; 
v___x_1686_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__13));
v___x_1687_ = l_Lean_Expr_isConstOf(v___x_1679_, v___x_1686_);
lean_dec_ref(v___x_1679_);
if (v___x_1687_ == 0)
{
lean_dec_ref(v_arg_1676_);
lean_dec_ref(v_arg_1669_);
lean_dec_ref(v_arg_1666_);
goto v___jp_1659_;
}
else
{
lean_object* v___x_1688_; 
lean_del_object(v___x_1657_);
v___x_1688_ = l_Lean_Meta_DefEq_isInstLEInt(v_arg_1676_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1727_; 
v_a_1689_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1691_ = v___x_1688_;
v_isShared_1692_ = v_isSharedCheck_1727_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1688_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1727_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
uint8_t v___x_1693_; 
v___x_1693_ = lean_unbox(v_a_1689_);
lean_dec(v_a_1689_);
if (v___x_1693_ == 0)
{
lean_object* v___x_1694_; lean_object* v___x_1696_; 
lean_dec_ref(v_arg_1669_);
lean_dec_ref(v_arg_1666_);
v___x_1694_ = lean_box(0);
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 0, v___x_1694_);
v___x_1696_ = v___x_1691_;
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
lean_object* v___x_1698_; 
lean_del_object(v___x_1691_);
v___x_1698_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1669_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1699_; lean_object* v___x_1700_; 
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
lean_inc(v_a_1699_);
lean_dec_ref(v___x_1698_);
v___x_1700_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1666_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1710_; 
v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1703_ = v___x_1700_;
v_isShared_1704_ = v_isSharedCheck_1710_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1700_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1710_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1708_; 
v___x_1705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1705_, 0, v_a_1699_);
lean_ctor_set(v___x_1705_, 1, v_a_1701_);
v___x_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1705_);
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 0, v___x_1706_);
v___x_1708_ = v___x_1703_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1706_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
else
{
lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1718_; 
lean_dec(v_a_1699_);
v_a_1711_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1713_ = v___x_1700_;
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1700_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1716_; 
if (v_isShared_1714_ == 0)
{
v___x_1716_ = v___x_1713_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_a_1711_);
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
lean_dec_ref(v_arg_1666_);
v_a_1719_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1721_ = v___x_1698_;
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v___x_1698_);
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
}
else
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1735_; 
lean_dec_ref(v_arg_1669_);
lean_dec_ref(v_arg_1666_);
v_a_1728_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1730_ = v___x_1688_;
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1688_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1733_; 
if (v_isShared_1731_ == 0)
{
v___x_1733_ = v___x_1730_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1728_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
}
}
else
{
lean_object* v___x_1736_; 
lean_dec_ref(v___x_1679_);
lean_del_object(v___x_1657_);
v___x_1736_ = l_Lean_Meta_DefEq_isInstLTInt(v_arg_1676_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_object* v_a_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1777_; 
v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1739_ = v___x_1736_;
v_isShared_1740_ = v_isSharedCheck_1777_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_a_1737_);
lean_dec(v___x_1736_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1777_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
uint8_t v___x_1741_; 
v___x_1741_ = lean_unbox(v_a_1737_);
lean_dec(v_a_1737_);
if (v___x_1741_ == 0)
{
lean_object* v___x_1742_; lean_object* v___x_1744_; 
lean_dec_ref(v_arg_1669_);
lean_dec_ref(v_arg_1666_);
v___x_1742_ = lean_box(0);
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 0, v___x_1742_);
v___x_1744_ = v___x_1739_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1742_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
else
{
lean_object* v___x_1746_; 
lean_del_object(v___x_1739_);
v___x_1746_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1669_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; lean_object* v___x_1748_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_a_1747_);
lean_dec_ref(v___x_1746_);
v___x_1748_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1666_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1760_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1751_ = v___x_1748_;
v_isShared_1752_ = v_isSharedCheck_1760_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___x_1748_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1760_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1758_; 
v___x_1753_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14, &l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14);
v___x_1754_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1754_, 0, v_a_1747_);
lean_ctor_set(v___x_1754_, 1, v___x_1753_);
v___x_1755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1754_);
lean_ctor_set(v___x_1755_, 1, v_a_1749_);
v___x_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 0, v___x_1756_);
v___x_1758_ = v___x_1751_;
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
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
lean_dec(v_a_1747_);
v_a_1761_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1748_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1748_);
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
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
lean_dec_ref(v_arg_1666_);
v_a_1769_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1746_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1746_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
}
}
else
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
lean_dec_ref(v_arg_1669_);
lean_dec_ref(v_arg_1666_);
v_a_1778_ = lean_ctor_get(v___x_1736_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1780_ = v___x_1736_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1736_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_a_1778_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
}
}
else
{
lean_object* v___x_1786_; 
lean_dec_ref(v___x_1679_);
lean_del_object(v___x_1657_);
v___x_1786_ = l_Lean_Meta_DefEq_isInstLEInt(v_arg_1676_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1825_; 
v_a_1787_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1789_ = v___x_1786_;
v_isShared_1790_ = v_isSharedCheck_1825_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1786_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1825_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
uint8_t v___x_1791_; 
v___x_1791_ = lean_unbox(v_a_1787_);
lean_dec(v_a_1787_);
if (v___x_1791_ == 0)
{
lean_object* v___x_1792_; lean_object* v___x_1794_; 
lean_dec_ref(v_arg_1669_);
lean_dec_ref(v_arg_1666_);
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
else
{
lean_object* v___x_1796_; 
lean_del_object(v___x_1789_);
v___x_1796_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1666_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_a_1797_; lean_object* v___x_1798_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_a_1797_);
lean_dec_ref(v___x_1796_);
v___x_1798_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1669_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1808_; 
v_a_1799_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1801_ = v___x_1798_;
v_isShared_1802_ = v_isSharedCheck_1808_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1798_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1808_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1806_; 
v___x_1803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1803_, 0, v_a_1797_);
lean_ctor_set(v___x_1803_, 1, v_a_1799_);
v___x_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1803_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 0, v___x_1804_);
v___x_1806_ = v___x_1801_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v___x_1804_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
else
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1816_; 
lean_dec(v_a_1797_);
v_a_1809_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1811_ = v___x_1798_;
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1798_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v_a_1809_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
else
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1824_; 
lean_dec_ref(v_arg_1669_);
v_a_1817_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1819_ = v___x_1796_;
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1796_);
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
}
else
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1833_; 
lean_dec_ref(v_arg_1669_);
lean_dec_ref(v_arg_1666_);
v_a_1826_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1828_ = v___x_1786_;
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1786_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_a_1826_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
}
else
{
lean_object* v___x_1834_; 
lean_dec_ref(v___x_1679_);
lean_del_object(v___x_1657_);
v___x_1834_ = l_Lean_Meta_DefEq_isInstLTInt(v_arg_1676_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1875_; 
v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1837_ = v___x_1834_;
v_isShared_1838_ = v_isSharedCheck_1875_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1834_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1875_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
uint8_t v___x_1839_; 
v___x_1839_ = lean_unbox(v_a_1835_);
lean_dec(v_a_1835_);
if (v___x_1839_ == 0)
{
lean_object* v___x_1840_; lean_object* v___x_1842_; 
lean_dec_ref(v_arg_1669_);
lean_dec_ref(v_arg_1666_);
v___x_1840_ = lean_box(0);
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 0, v___x_1840_);
v___x_1842_ = v___x_1837_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v___x_1840_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
else
{
lean_object* v___x_1844_; 
lean_del_object(v___x_1837_);
v___x_1844_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1666_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v_a_1845_; lean_object* v___x_1846_; 
v_a_1845_ = lean_ctor_get(v___x_1844_, 0);
lean_inc(v_a_1845_);
lean_dec_ref(v___x_1844_);
v___x_1846_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1669_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1858_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1849_ = v___x_1846_;
v_isShared_1850_ = v_isSharedCheck_1858_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1846_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1858_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1856_; 
v___x_1851_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14, &l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14);
v___x_1852_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1852_, 0, v_a_1845_);
lean_ctor_set(v___x_1852_, 1, v___x_1851_);
v___x_1853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1852_);
lean_ctor_set(v___x_1853_, 1, v_a_1847_);
v___x_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1853_);
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 0, v___x_1854_);
v___x_1856_ = v___x_1849_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1854_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
lean_dec(v_a_1845_);
v_a_1859_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1846_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1846_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1859_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
}
else
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1874_; 
lean_dec_ref(v_arg_1669_);
v_a_1867_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1869_ = v___x_1844_;
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1844_);
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
}
}
}
else
{
lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1883_; 
lean_dec_ref(v_arg_1669_);
lean_dec_ref(v_arg_1666_);
v_a_1876_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1878_ = v___x_1834_;
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1834_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1879_ == 0)
{
v___x_1881_ = v___x_1878_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_a_1876_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1884_; 
lean_dec_ref(v___x_1670_);
lean_del_object(v___x_1657_);
v___x_1884_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1669_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_a_1885_; lean_object* v___x_1886_; 
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
lean_inc(v_a_1885_);
lean_dec_ref(v___x_1884_);
v___x_1886_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1666_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1896_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1889_ = v___x_1886_;
v_isShared_1890_ = v_isSharedCheck_1896_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_dec(v___x_1886_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1896_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1894_; 
v___x_1891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1891_, 0, v_a_1885_);
lean_ctor_set(v___x_1891_, 1, v_a_1887_);
v___x_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1891_);
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 0, v___x_1892_);
v___x_1894_ = v___x_1889_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1892_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
else
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1904_; 
lean_dec(v_a_1885_);
v_a_1897_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1899_ = v___x_1886_;
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1886_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1902_; 
if (v_isShared_1900_ == 0)
{
v___x_1902_ = v___x_1899_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_a_1897_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
}
else
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1912_; 
lean_dec_ref(v_arg_1666_);
v_a_1905_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1907_ = v___x_1884_;
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1884_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1910_; 
if (v_isShared_1908_ == 0)
{
v___x_1910_ = v___x_1907_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_a_1905_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
}
else
{
lean_object* v___x_1913_; 
lean_dec_ref(v___x_1670_);
lean_del_object(v___x_1657_);
v___x_1913_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1669_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; lean_object* v___x_1915_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_a_1914_);
lean_dec_ref(v___x_1913_);
v___x_1915_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1666_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1927_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1918_ = v___x_1915_;
v_isShared_1919_ = v_isSharedCheck_1927_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1915_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1927_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1925_; 
v___x_1920_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14, &l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14);
v___x_1921_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1921_, 0, v_a_1914_);
lean_ctor_set(v___x_1921_, 1, v___x_1920_);
v___x_1922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1921_);
lean_ctor_set(v___x_1922_, 1, v_a_1916_);
v___x_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1922_);
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 0, v___x_1923_);
v___x_1925_ = v___x_1918_;
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
}
else
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
lean_dec(v_a_1914_);
v_a_1928_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1930_ = v___x_1915_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1915_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_a_1928_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
else
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1943_; 
lean_dec_ref(v_arg_1666_);
v_a_1936_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1938_ = v___x_1913_;
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1913_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1939_ == 0)
{
v___x_1941_ = v___x_1938_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_a_1936_);
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
}
}
v___jp_1659_:
{
lean_object* v___x_1660_; lean_object* v___x_1662_; 
v___x_1660_ = lean_box(0);
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 0, v___x_1660_);
v___x_1662_ = v___x_1657_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v___x_1660_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
v_a_1945_ = lean_ctor_get(v___x_1654_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1654_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1654_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1654_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___boxed(lean_object* v_e_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f(v_e_1953_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_);
lean_dec(v_a_1958_);
lean_dec_ref(v_a_1957_);
lean_dec(v_a_1956_);
lean_dec_ref(v_a_1955_);
lean_dec(v_a_1954_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f(lean_object* v_e_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_){
_start:
{
lean_object* v___x_1973_; 
v___x_1973_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1966_, v_a_1969_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_a_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_2060_; 
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_1976_ = v___x_1973_;
v_isShared_1977_ = v_isSharedCheck_2060_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_a_1974_);
lean_dec(v___x_1973_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_2060_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1983_; uint8_t v___x_1984_; 
v___x_1983_ = l_Lean_Expr_cleanupAnnotations(v_a_1974_);
v___x_1984_ = l_Lean_Expr_isApp(v___x_1983_);
if (v___x_1984_ == 0)
{
lean_dec_ref(v___x_1983_);
goto v___jp_1978_;
}
else
{
lean_object* v_arg_1985_; lean_object* v___x_1986_; uint8_t v___x_1987_; 
v_arg_1985_ = lean_ctor_get(v___x_1983_, 1);
lean_inc_ref(v_arg_1985_);
v___x_1986_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1983_);
v___x_1987_ = l_Lean_Expr_isApp(v___x_1986_);
if (v___x_1987_ == 0)
{
lean_dec_ref(v___x_1986_);
lean_dec_ref(v_arg_1985_);
goto v___jp_1978_;
}
else
{
lean_object* v_arg_1988_; lean_object* v___x_1989_; uint8_t v___x_1990_; 
v_arg_1988_ = lean_ctor_get(v___x_1986_, 1);
lean_inc_ref(v_arg_1988_);
v___x_1989_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1986_);
v___x_1990_ = l_Lean_Expr_isApp(v___x_1989_);
if (v___x_1990_ == 0)
{
lean_dec_ref(v___x_1989_);
lean_dec_ref(v_arg_1988_);
lean_dec_ref(v_arg_1985_);
goto v___jp_1978_;
}
else
{
lean_object* v_arg_1991_; lean_object* v___x_1992_; uint8_t v___x_1993_; 
v_arg_1991_ = lean_ctor_get(v___x_1989_, 1);
lean_inc_ref(v_arg_1991_);
v___x_1992_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1989_);
v___x_1993_ = l_Lean_Expr_isApp(v___x_1992_);
if (v___x_1993_ == 0)
{
lean_dec_ref(v___x_1992_);
lean_dec_ref(v_arg_1991_);
lean_dec_ref(v_arg_1988_);
lean_dec_ref(v_arg_1985_);
goto v___jp_1978_;
}
else
{
lean_object* v___x_1994_; lean_object* v___x_1995_; uint8_t v___x_1996_; 
v___x_1994_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1992_);
v___x_1995_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__2));
v___x_1996_ = l_Lean_Expr_isConstOf(v___x_1994_, v___x_1995_);
lean_dec_ref(v___x_1994_);
if (v___x_1996_ == 0)
{
lean_dec_ref(v_arg_1991_);
lean_dec_ref(v_arg_1988_);
lean_dec_ref(v_arg_1985_);
goto v___jp_1978_;
}
else
{
lean_object* v___x_1997_; 
lean_del_object(v___x_1976_);
v___x_1997_ = l_Lean_Meta_DefEq_isInstDvdInt(v_arg_1991_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v_a_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2051_; 
v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2000_ = v___x_1997_;
v_isShared_2001_ = v_isSharedCheck_2051_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_a_1998_);
lean_dec(v___x_1997_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2051_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
uint8_t v___x_2002_; 
v___x_2002_ = lean_unbox(v_a_1998_);
lean_dec(v_a_1998_);
if (v___x_2002_ == 0)
{
lean_object* v___x_2003_; lean_object* v___x_2005_; 
lean_dec_ref(v_arg_1988_);
lean_dec_ref(v_arg_1985_);
v___x_2003_ = lean_box(0);
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 0, v___x_2003_);
v___x_2005_ = v___x_2000_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_2003_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
else
{
lean_object* v___x_2007_; 
lean_del_object(v___x_2000_);
v___x_2007_ = l_Lean_Meta_getIntValue_x3f(v_arg_1988_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2042_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2010_ = v___x_2007_;
v_isShared_2011_ = v_isSharedCheck_2042_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_2007_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2042_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
if (lean_obj_tag(v_a_2008_) == 1)
{
lean_object* v_val_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2037_; 
lean_del_object(v___x_2010_);
v_val_2012_ = lean_ctor_get(v_a_2008_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v_a_2008_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2014_ = v_a_2008_;
v_isShared_2015_ = v_isSharedCheck_2037_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_val_2012_);
lean_dec(v_a_2008_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2037_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2016_; 
v___x_2016_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1985_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2028_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2019_ = v___x_2016_;
v_isShared_2020_ = v_isSharedCheck_2028_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2016_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2028_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2021_; lean_object* v___x_2023_; 
v___x_2021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2021_, 0, v_val_2012_);
lean_ctor_set(v___x_2021_, 1, v_a_2017_);
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 0, v___x_2021_);
v___x_2023_ = v___x_2014_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2021_);
v___x_2023_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
lean_object* v___x_2025_; 
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 0, v___x_2023_);
v___x_2025_ = v___x_2019_;
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
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
lean_del_object(v___x_2014_);
lean_dec(v_val_2012_);
v_a_2029_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_2016_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2016_);
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
}
else
{
lean_object* v___x_2038_; lean_object* v___x_2040_; 
lean_dec(v_a_2008_);
lean_dec_ref(v_arg_1985_);
v___x_2038_ = lean_box(0);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v___x_2038_);
v___x_2040_ = v___x_2010_;
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
}
else
{
lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2050_; 
lean_dec_ref(v_arg_1985_);
v_a_2043_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2045_ = v___x_2007_;
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_2007_);
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
}
}
else
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2059_; 
lean_dec_ref(v_arg_1988_);
lean_dec_ref(v_arg_1985_);
v_a_2052_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2054_ = v___x_1997_;
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_1997_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2057_; 
if (v_isShared_2055_ == 0)
{
v___x_2057_ = v___x_2054_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_a_2052_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
}
}
}
}
}
v___jp_1978_:
{
lean_object* v___x_1979_; lean_object* v___x_1981_; 
v___x_1979_ = lean_box(0);
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 0, v___x_1979_);
v___x_1981_ = v___x_1976_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v___x_1979_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
}
}
else
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
v_a_2061_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_1973_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_1973_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___boxed(lean_object* v_e_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f(v_e_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_);
lean_dec(v_a_2074_);
lean_dec_ref(v_a_2073_);
lean_dec(v_a_2072_);
lean_dec_ref(v_a_2071_);
lean_dec(v_a_2070_);
return v_res_2076_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_2077_; 
v___x_2077_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2077_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2078_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__0, &l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__0_once, _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__0);
v___x_2079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2078_);
return v___x_2079_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__3(void){
_start:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2082_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__2));
v___x_2083_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__1, &l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__1_once, _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__1);
v___x_2084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
lean_ctor_set(v___x_2084_, 1, v___x_2082_);
return v___x_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(lean_object* v_x_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_){
_start:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2091_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__3, &l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__3);
v___x_2092_ = lean_st_mk_ref(v___x_2091_);
lean_inc(v_a_2089_);
lean_inc_ref(v_a_2088_);
lean_inc(v_a_2087_);
lean_inc_ref(v_a_2086_);
lean_inc(v___x_2092_);
v___x_2093_ = lean_apply_6(v_x_2085_, v___x_2092_, v_a_2086_, v_a_2087_, v_a_2088_, v_a_2089_, lean_box(0));
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v_a_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2111_; 
v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2096_ = v___x_2093_;
v_isShared_2097_ = v_isSharedCheck_2111_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_a_2094_);
lean_dec(v___x_2093_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2111_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2098_; lean_object* v_vars_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2109_; 
v___x_2098_ = lean_st_ref_get(v___x_2092_);
lean_dec(v___x_2092_);
v_vars_2099_ = lean_ctor_get(v___x_2098_, 1);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2109_ == 0)
{
lean_object* v_unused_2110_; 
v_unused_2110_ = lean_ctor_get(v___x_2098_, 0);
lean_dec(v_unused_2110_);
v___x_2101_ = v___x_2098_;
v_isShared_2102_ = v_isSharedCheck_2109_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_vars_2099_);
lean_dec(v___x_2098_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2109_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 0, v_a_2094_);
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_a_2094_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v_vars_2099_);
v___x_2104_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
lean_object* v___x_2106_; 
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 0, v___x_2104_);
v___x_2106_ = v___x_2096_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2104_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
}
}
else
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
lean_dec(v___x_2092_);
v_a_2112_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2093_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2093_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___boxed(lean_object* v_x_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_){
_start:
{
lean_object* v_res_2126_; 
v_res_2126_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(v_x_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_);
lean_dec(v_a_2124_);
lean_dec_ref(v_a_2123_);
lean_dec(v_a_2122_);
lean_dec_ref(v_a_2121_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run(lean_object* v_00_u03b1_2127_, lean_object* v_x_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_){
_start:
{
lean_object* v___x_2134_; 
v___x_2134_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(v_x_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run___boxed(lean_object* v_00_u03b1_2135_, lean_object* v_x_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_){
_start:
{
lean_object* v_res_2142_; 
v_res_2142_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run(v_00_u03b1_2135_, v_x_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_);
lean_dec(v_a_2140_);
lean_dec_ref(v_a_2139_);
lean_dec(v_a_2138_);
lean_dec_ref(v_a_2137_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toLinearExpr(lean_object* v_e_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_){
_start:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2149_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr___boxed), 7, 1);
lean_closure_set(v___x_2149_, 0, v_e_2143_);
v___x_2150_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(v___x_2149_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v_a_2151_; lean_object* v_fst_2152_; lean_object* v_snd_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; uint8_t v___x_2156_; 
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
lean_inc(v_a_2151_);
v_fst_2152_ = lean_ctor_get(v_a_2151_, 0);
lean_inc(v_fst_2152_);
v_snd_2153_ = lean_ctor_get(v_a_2151_, 1);
lean_inc(v_snd_2153_);
lean_dec(v_a_2151_);
v___x_2154_ = lean_array_get_size(v_snd_2153_);
v___x_2155_ = lean_unsigned_to_nat(1u);
v___x_2156_ = lean_nat_dec_eq(v___x_2154_, v___x_2155_);
if (v___x_2156_ == 0)
{
lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2174_; 
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2174_ == 0)
{
lean_object* v_unused_2175_; 
v_unused_2175_ = lean_ctor_get(v___x_2150_, 0);
lean_dec(v_unused_2175_);
v___x_2158_ = v___x_2150_;
v_isShared_2159_ = v_isSharedCheck_2174_;
goto v_resetjp_2157_;
}
else
{
lean_dec(v___x_2150_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2174_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2160_; lean_object* v_fst_2161_; lean_object* v_snd_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2173_; 
v___x_2160_ = l_Lean_sortExprs(v_snd_2153_, v___x_2156_);
lean_dec(v_snd_2153_);
v_fst_2161_ = lean_ctor_get(v___x_2160_, 0);
v_snd_2162_ = lean_ctor_get(v___x_2160_, 1);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2164_ = v___x_2160_;
v_isShared_2165_ = v_isSharedCheck_2173_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_snd_2162_);
lean_inc(v_fst_2161_);
lean_dec(v___x_2160_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2173_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2166_; lean_object* v___x_2168_; 
v___x_2166_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(v_snd_2162_, v_fst_2152_);
lean_dec(v_snd_2162_);
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 1, v_fst_2161_);
lean_ctor_set(v___x_2164_, 0, v___x_2166_);
v___x_2168_ = v___x_2164_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2166_);
lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_fst_2161_);
v___x_2168_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
lean_object* v___x_2170_; 
if (v_isShared_2159_ == 0)
{
lean_ctor_set(v___x_2158_, 0, v___x_2168_);
v___x_2170_ = v___x_2158_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2168_);
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
else
{
lean_dec(v_snd_2153_);
lean_dec(v_fst_2152_);
return v___x_2150_;
}
}
else
{
return v___x_2150_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toLinearExpr___boxed(lean_object* v_e_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l_Lean_Meta_Simp_Arith_Int_toLinearExpr(v_e_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_);
lean_dec(v_a_2180_);
lean_dec_ref(v_a_2179_);
lean_dec(v_a_2178_);
lean_dec_ref(v_a_2177_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_adapter(lean_object* v_e_2183_, lean_object* v_k_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2190_ = lean_apply_1(v_k_2184_, v_e_2183_);
v___x_2191_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(v___x_2190_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_);
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2254_; 
v_a_2192_ = lean_ctor_get(v___x_2191_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2194_ = v___x_2191_;
v_isShared_2195_ = v_isSharedCheck_2254_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2191_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2254_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v_fst_2196_; 
v_fst_2196_ = lean_ctor_get(v_a_2192_, 0);
lean_inc(v_fst_2196_);
if (lean_obj_tag(v_fst_2196_) == 1)
{
lean_object* v_val_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2249_; 
v_val_2197_ = lean_ctor_get(v_fst_2196_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v_fst_2196_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2199_ = v_fst_2196_;
v_isShared_2200_ = v_isSharedCheck_2249_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_val_2197_);
lean_dec(v_fst_2196_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2249_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v_snd_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2247_; 
v_snd_2201_ = lean_ctor_get(v_a_2192_, 1);
v_isSharedCheck_2247_ = !lean_is_exclusive(v_a_2192_);
if (v_isSharedCheck_2247_ == 0)
{
lean_object* v_unused_2248_; 
v_unused_2248_ = lean_ctor_get(v_a_2192_, 0);
lean_dec(v_unused_2248_);
v___x_2203_ = v_a_2192_;
v_isShared_2204_ = v_isSharedCheck_2247_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_snd_2201_);
lean_dec(v_a_2192_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2247_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v_fst_2205_; lean_object* v_snd_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2246_; 
v_fst_2205_ = lean_ctor_get(v_val_2197_, 0);
v_snd_2206_ = lean_ctor_get(v_val_2197_, 1);
v_isSharedCheck_2246_ = !lean_is_exclusive(v_val_2197_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2208_ = v_val_2197_;
v_isShared_2209_ = v_isSharedCheck_2246_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_snd_2206_);
lean_inc(v_fst_2205_);
lean_dec(v_val_2197_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2246_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; uint8_t v___x_2212_; 
v___x_2210_ = lean_array_get_size(v_snd_2201_);
v___x_2211_ = lean_unsigned_to_nat(1u);
v___x_2212_ = lean_nat_dec_le(v___x_2210_, v___x_2211_);
if (v___x_2212_ == 0)
{
lean_object* v___x_2213_; lean_object* v_fst_2214_; lean_object* v_snd_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2233_; 
lean_del_object(v___x_2203_);
v___x_2213_ = l_Lean_sortExprs(v_snd_2201_, v___x_2212_);
lean_dec(v_snd_2201_);
v_fst_2214_ = lean_ctor_get(v___x_2213_, 0);
v_snd_2215_ = lean_ctor_get(v___x_2213_, 1);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2217_ = v___x_2213_;
v_isShared_2218_ = v_isSharedCheck_2233_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_snd_2215_);
lean_inc(v_fst_2214_);
lean_dec(v___x_2213_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2233_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2222_; 
v___x_2219_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(v_snd_2215_, v_fst_2205_);
v___x_2220_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(v_snd_2215_, v_snd_2206_);
lean_dec(v_snd_2215_);
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 1, v_fst_2214_);
lean_ctor_set(v___x_2217_, 0, v___x_2220_);
v___x_2222_ = v___x_2217_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v___x_2220_);
lean_ctor_set(v_reuseFailAlloc_2232_, 1, v_fst_2214_);
v___x_2222_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
lean_object* v___x_2224_; 
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 1, v___x_2222_);
lean_ctor_set(v___x_2208_, 0, v___x_2219_);
v___x_2224_ = v___x_2208_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v___x_2219_);
lean_ctor_set(v_reuseFailAlloc_2231_, 1, v___x_2222_);
v___x_2224_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
lean_object* v___x_2226_; 
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 0, v___x_2224_);
v___x_2226_ = v___x_2199_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v___x_2224_);
v___x_2226_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
lean_object* v___x_2228_; 
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 0, v___x_2226_);
v___x_2228_ = v___x_2194_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2226_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
}
}
else
{
lean_object* v___x_2235_; 
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 1, v_snd_2201_);
lean_ctor_set(v___x_2208_, 0, v_snd_2206_);
v___x_2235_ = v___x_2208_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_snd_2206_);
lean_ctor_set(v_reuseFailAlloc_2245_, 1, v_snd_2201_);
v___x_2235_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
lean_object* v___x_2237_; 
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 1, v___x_2235_);
lean_ctor_set(v___x_2203_, 0, v_fst_2205_);
v___x_2237_ = v___x_2203_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_fst_2205_);
lean_ctor_set(v_reuseFailAlloc_2244_, 1, v___x_2235_);
v___x_2237_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
lean_object* v___x_2239_; 
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 0, v___x_2237_);
v___x_2239_ = v___x_2199_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2237_);
v___x_2239_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
lean_object* v___x_2241_; 
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 0, v___x_2239_);
v___x_2241_ = v___x_2194_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v___x_2239_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
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
lean_object* v___x_2250_; lean_object* v___x_2252_; 
lean_dec(v_fst_2196_);
lean_dec(v_a_2192_);
v___x_2250_ = lean_box(0);
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 0, v___x_2250_);
v___x_2252_ = v___x_2194_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v___x_2250_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
else
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2262_; 
v_a_2255_ = lean_ctor_get(v___x_2191_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2257_ = v___x_2191_;
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2191_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2260_; 
if (v_isShared_2258_ == 0)
{
v___x_2260_ = v___x_2257_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_a_2255_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_adapter___boxed(lean_object* v_e_2263_, lean_object* v_k_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_){
_start:
{
lean_object* v_res_2270_; 
v_res_2270_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_adapter(v_e_2263_, v_k_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_);
lean_dec(v_a_2268_);
lean_dec_ref(v_a_2267_);
lean_dec(v_a_2266_);
lean_dec_ref(v_a_2265_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(lean_object* v_e_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_){
_start:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2277_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___boxed), 7, 1);
lean_closure_set(v___x_2277_, 0, v_e_2271_);
v___x_2278_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(v___x_2277_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2341_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2281_ = v___x_2278_;
v_isShared_2282_ = v_isSharedCheck_2341_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_a_2279_);
lean_dec(v___x_2278_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2341_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v_fst_2283_; 
v_fst_2283_ = lean_ctor_get(v_a_2279_, 0);
lean_inc(v_fst_2283_);
if (lean_obj_tag(v_fst_2283_) == 1)
{
lean_object* v_val_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2336_; 
v_val_2284_ = lean_ctor_get(v_fst_2283_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v_fst_2283_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2286_ = v_fst_2283_;
v_isShared_2287_ = v_isSharedCheck_2336_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_val_2284_);
lean_dec(v_fst_2283_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2336_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v_snd_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2334_; 
v_snd_2288_ = lean_ctor_get(v_a_2279_, 1);
v_isSharedCheck_2334_ = !lean_is_exclusive(v_a_2279_);
if (v_isSharedCheck_2334_ == 0)
{
lean_object* v_unused_2335_; 
v_unused_2335_ = lean_ctor_get(v_a_2279_, 0);
lean_dec(v_unused_2335_);
v___x_2290_ = v_a_2279_;
v_isShared_2291_ = v_isSharedCheck_2334_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_snd_2288_);
lean_dec(v_a_2279_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2334_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v_fst_2292_; lean_object* v_snd_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2333_; 
v_fst_2292_ = lean_ctor_get(v_val_2284_, 0);
v_snd_2293_ = lean_ctor_get(v_val_2284_, 1);
v_isSharedCheck_2333_ = !lean_is_exclusive(v_val_2284_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2295_ = v_val_2284_;
v_isShared_2296_ = v_isSharedCheck_2333_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_snd_2293_);
lean_inc(v_fst_2292_);
lean_dec(v_val_2284_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2333_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; uint8_t v___x_2299_; 
v___x_2297_ = lean_array_get_size(v_snd_2288_);
v___x_2298_ = lean_unsigned_to_nat(1u);
v___x_2299_ = lean_nat_dec_le(v___x_2297_, v___x_2298_);
if (v___x_2299_ == 0)
{
lean_object* v___x_2300_; lean_object* v_fst_2301_; lean_object* v_snd_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2320_; 
lean_del_object(v___x_2290_);
v___x_2300_ = l_Lean_sortExprs(v_snd_2288_, v___x_2299_);
lean_dec(v_snd_2288_);
v_fst_2301_ = lean_ctor_get(v___x_2300_, 0);
v_snd_2302_ = lean_ctor_get(v___x_2300_, 1);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2304_ = v___x_2300_;
v_isShared_2305_ = v_isSharedCheck_2320_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_snd_2302_);
lean_inc(v_fst_2301_);
lean_dec(v___x_2300_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2320_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2309_; 
v___x_2306_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(v_snd_2302_, v_fst_2292_);
v___x_2307_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(v_snd_2302_, v_snd_2293_);
lean_dec(v_snd_2302_);
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 1, v_fst_2301_);
lean_ctor_set(v___x_2304_, 0, v___x_2307_);
v___x_2309_ = v___x_2304_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2307_);
lean_ctor_set(v_reuseFailAlloc_2319_, 1, v_fst_2301_);
v___x_2309_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
lean_object* v___x_2311_; 
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 1, v___x_2309_);
lean_ctor_set(v___x_2295_, 0, v___x_2306_);
v___x_2311_ = v___x_2295_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v___x_2306_);
lean_ctor_set(v_reuseFailAlloc_2318_, 1, v___x_2309_);
v___x_2311_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
lean_object* v___x_2313_; 
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 0, v___x_2311_);
v___x_2313_ = v___x_2286_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v___x_2311_);
v___x_2313_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
lean_object* v___x_2315_; 
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 0, v___x_2313_);
v___x_2315_ = v___x_2281_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v___x_2313_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
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
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 1, v_snd_2288_);
lean_ctor_set(v___x_2295_, 0, v_snd_2293_);
v___x_2322_ = v___x_2295_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_snd_2293_);
lean_ctor_set(v_reuseFailAlloc_2332_, 1, v_snd_2288_);
v___x_2322_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
lean_object* v___x_2324_; 
if (v_isShared_2291_ == 0)
{
lean_ctor_set(v___x_2290_, 1, v___x_2322_);
lean_ctor_set(v___x_2290_, 0, v_fst_2292_);
v___x_2324_ = v___x_2290_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_fst_2292_);
lean_ctor_set(v_reuseFailAlloc_2331_, 1, v___x_2322_);
v___x_2324_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
lean_object* v___x_2326_; 
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 0, v___x_2324_);
v___x_2326_ = v___x_2286_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2324_);
v___x_2326_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
lean_object* v___x_2328_; 
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 0, v___x_2326_);
v___x_2328_ = v___x_2281_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2326_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
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
lean_object* v___x_2337_; lean_object* v___x_2339_; 
lean_dec(v_fst_2283_);
lean_dec(v_a_2279_);
v___x_2337_ = lean_box(0);
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 0, v___x_2337_);
v___x_2339_ = v___x_2281_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v___x_2337_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
else
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2349_; 
v_a_2342_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2344_ = v___x_2278_;
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___x_2278_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2347_; 
if (v_isShared_2345_ == 0)
{
v___x_2347_ = v___x_2344_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_a_2342_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f___boxed(lean_object* v_e_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_){
_start:
{
lean_object* v_res_2356_; 
v_res_2356_ = l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(v_e_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_);
lean_dec(v_a_2354_);
lean_dec_ref(v_a_2353_);
lean_dec(v_a_2352_);
lean_dec_ref(v_a_2351_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(lean_object* v_e_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_){
_start:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; 
v___x_2363_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___boxed), 7, 1);
lean_closure_set(v___x_2363_, 0, v_e_2357_);
v___x_2364_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(v___x_2363_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_);
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2427_; 
v_a_2365_ = lean_ctor_get(v___x_2364_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2367_ = v___x_2364_;
v_isShared_2368_ = v_isSharedCheck_2427_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2364_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2427_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v_fst_2369_; 
v_fst_2369_ = lean_ctor_get(v_a_2365_, 0);
lean_inc(v_fst_2369_);
if (lean_obj_tag(v_fst_2369_) == 1)
{
lean_object* v_val_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2422_; 
v_val_2370_ = lean_ctor_get(v_fst_2369_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v_fst_2369_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2372_ = v_fst_2369_;
v_isShared_2373_ = v_isSharedCheck_2422_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_val_2370_);
lean_dec(v_fst_2369_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2422_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v_snd_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2420_; 
v_snd_2374_ = lean_ctor_get(v_a_2365_, 1);
v_isSharedCheck_2420_ = !lean_is_exclusive(v_a_2365_);
if (v_isSharedCheck_2420_ == 0)
{
lean_object* v_unused_2421_; 
v_unused_2421_ = lean_ctor_get(v_a_2365_, 0);
lean_dec(v_unused_2421_);
v___x_2376_ = v_a_2365_;
v_isShared_2377_ = v_isSharedCheck_2420_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_snd_2374_);
lean_dec(v_a_2365_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2420_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v_fst_2378_; lean_object* v_snd_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2419_; 
v_fst_2378_ = lean_ctor_get(v_val_2370_, 0);
v_snd_2379_ = lean_ctor_get(v_val_2370_, 1);
v_isSharedCheck_2419_ = !lean_is_exclusive(v_val_2370_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2381_ = v_val_2370_;
v_isShared_2382_ = v_isSharedCheck_2419_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_snd_2379_);
lean_inc(v_fst_2378_);
lean_dec(v_val_2370_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2419_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; uint8_t v___x_2385_; 
v___x_2383_ = lean_array_get_size(v_snd_2374_);
v___x_2384_ = lean_unsigned_to_nat(1u);
v___x_2385_ = lean_nat_dec_le(v___x_2383_, v___x_2384_);
if (v___x_2385_ == 0)
{
lean_object* v___x_2386_; lean_object* v_fst_2387_; lean_object* v_snd_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2406_; 
lean_del_object(v___x_2376_);
v___x_2386_ = l_Lean_sortExprs(v_snd_2374_, v___x_2385_);
lean_dec(v_snd_2374_);
v_fst_2387_ = lean_ctor_get(v___x_2386_, 0);
v_snd_2388_ = lean_ctor_get(v___x_2386_, 1);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2390_ = v___x_2386_;
v_isShared_2391_ = v_isSharedCheck_2406_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_snd_2388_);
lean_inc(v_fst_2387_);
lean_dec(v___x_2386_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2406_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2395_; 
v___x_2392_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(v_snd_2388_, v_fst_2378_);
v___x_2393_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(v_snd_2388_, v_snd_2379_);
lean_dec(v_snd_2388_);
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 1, v_fst_2387_);
lean_ctor_set(v___x_2390_, 0, v___x_2393_);
v___x_2395_ = v___x_2390_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v___x_2393_);
lean_ctor_set(v_reuseFailAlloc_2405_, 1, v_fst_2387_);
v___x_2395_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
lean_object* v___x_2397_; 
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 1, v___x_2395_);
lean_ctor_set(v___x_2381_, 0, v___x_2392_);
v___x_2397_ = v___x_2381_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v___x_2392_);
lean_ctor_set(v_reuseFailAlloc_2404_, 1, v___x_2395_);
v___x_2397_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
lean_object* v___x_2399_; 
if (v_isShared_2373_ == 0)
{
lean_ctor_set(v___x_2372_, 0, v___x_2397_);
v___x_2399_ = v___x_2372_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v___x_2397_);
v___x_2399_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
lean_object* v___x_2401_; 
if (v_isShared_2368_ == 0)
{
lean_ctor_set(v___x_2367_, 0, v___x_2399_);
v___x_2401_ = v___x_2367_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v___x_2399_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
}
}
}
else
{
lean_object* v___x_2408_; 
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 1, v_snd_2374_);
lean_ctor_set(v___x_2381_, 0, v_snd_2379_);
v___x_2408_ = v___x_2381_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_snd_2379_);
lean_ctor_set(v_reuseFailAlloc_2418_, 1, v_snd_2374_);
v___x_2408_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
lean_object* v___x_2410_; 
if (v_isShared_2377_ == 0)
{
lean_ctor_set(v___x_2376_, 1, v___x_2408_);
lean_ctor_set(v___x_2376_, 0, v_fst_2378_);
v___x_2410_ = v___x_2376_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_fst_2378_);
lean_ctor_set(v_reuseFailAlloc_2417_, 1, v___x_2408_);
v___x_2410_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
lean_object* v___x_2412_; 
if (v_isShared_2373_ == 0)
{
lean_ctor_set(v___x_2372_, 0, v___x_2410_);
v___x_2412_ = v___x_2372_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v___x_2410_);
v___x_2412_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
lean_object* v___x_2414_; 
if (v_isShared_2368_ == 0)
{
lean_ctor_set(v___x_2367_, 0, v___x_2412_);
v___x_2414_ = v___x_2367_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v___x_2412_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
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
lean_object* v___x_2423_; lean_object* v___x_2425_; 
lean_dec(v_fst_2369_);
lean_dec(v_a_2365_);
v___x_2423_ = lean_box(0);
if (v_isShared_2368_ == 0)
{
lean_ctor_set(v___x_2367_, 0, v___x_2423_);
v___x_2425_ = v___x_2367_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2423_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
return v___x_2425_;
}
}
}
}
else
{
lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2435_; 
v_a_2428_ = lean_ctor_get(v___x_2364_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2430_ = v___x_2364_;
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___x_2364_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2433_; 
if (v_isShared_2431_ == 0)
{
v___x_2433_ = v___x_2430_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_a_2428_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f___boxed(lean_object* v_e_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(v_e_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_);
lean_dec(v_a_2440_);
lean_dec_ref(v_a_2439_);
lean_dec(v_a_2438_);
lean_dec_ref(v_a_2437_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(lean_object* v_e_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_){
_start:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2449_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___boxed), 7, 1);
lean_closure_set(v___x_2449_, 0, v_e_2443_);
v___x_2450_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(v___x_2449_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2512_; 
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2453_ = v___x_2450_;
v_isShared_2454_ = v_isSharedCheck_2512_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2450_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2512_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v_fst_2455_; 
v_fst_2455_ = lean_ctor_get(v_a_2451_, 0);
lean_inc(v_fst_2455_);
if (lean_obj_tag(v_fst_2455_) == 1)
{
lean_object* v_val_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2507_; 
v_val_2456_ = lean_ctor_get(v_fst_2455_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v_fst_2455_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2458_ = v_fst_2455_;
v_isShared_2459_ = v_isSharedCheck_2507_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_val_2456_);
lean_dec(v_fst_2455_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2507_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v_snd_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2505_; 
v_snd_2460_ = lean_ctor_get(v_a_2451_, 1);
v_isSharedCheck_2505_ = !lean_is_exclusive(v_a_2451_);
if (v_isSharedCheck_2505_ == 0)
{
lean_object* v_unused_2506_; 
v_unused_2506_ = lean_ctor_get(v_a_2451_, 0);
lean_dec(v_unused_2506_);
v___x_2462_ = v_a_2451_;
v_isShared_2463_ = v_isSharedCheck_2505_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_snd_2460_);
lean_dec(v_a_2451_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2505_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v_fst_2464_; lean_object* v_snd_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2504_; 
v_fst_2464_ = lean_ctor_get(v_val_2456_, 0);
v_snd_2465_ = lean_ctor_get(v_val_2456_, 1);
v_isSharedCheck_2504_ = !lean_is_exclusive(v_val_2456_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2467_ = v_val_2456_;
v_isShared_2468_ = v_isSharedCheck_2504_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_snd_2465_);
lean_inc(v_fst_2464_);
lean_dec(v_val_2456_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2504_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; uint8_t v___x_2471_; 
v___x_2469_ = lean_array_get_size(v_snd_2460_);
v___x_2470_ = lean_unsigned_to_nat(1u);
v___x_2471_ = lean_nat_dec_le(v___x_2469_, v___x_2470_);
if (v___x_2471_ == 0)
{
lean_object* v___x_2472_; lean_object* v_fst_2473_; lean_object* v_snd_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2491_; 
lean_del_object(v___x_2462_);
v___x_2472_ = l_Lean_sortExprs(v_snd_2460_, v___x_2471_);
lean_dec(v_snd_2460_);
v_fst_2473_ = lean_ctor_get(v___x_2472_, 0);
v_snd_2474_ = lean_ctor_get(v___x_2472_, 1);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2476_ = v___x_2472_;
v_isShared_2477_ = v_isSharedCheck_2491_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_snd_2474_);
lean_inc(v_fst_2473_);
lean_dec(v___x_2472_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2491_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2478_; lean_object* v___x_2480_; 
v___x_2478_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(v_snd_2474_, v_snd_2465_);
lean_dec(v_snd_2474_);
if (v_isShared_2477_ == 0)
{
lean_ctor_set(v___x_2476_, 1, v_fst_2473_);
lean_ctor_set(v___x_2476_, 0, v___x_2478_);
v___x_2480_ = v___x_2476_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v___x_2478_);
lean_ctor_set(v_reuseFailAlloc_2490_, 1, v_fst_2473_);
v___x_2480_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
lean_object* v___x_2482_; 
if (v_isShared_2468_ == 0)
{
lean_ctor_set(v___x_2467_, 1, v___x_2480_);
v___x_2482_ = v___x_2467_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_fst_2464_);
lean_ctor_set(v_reuseFailAlloc_2489_, 1, v___x_2480_);
v___x_2482_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
lean_object* v___x_2484_; 
if (v_isShared_2459_ == 0)
{
lean_ctor_set(v___x_2458_, 0, v___x_2482_);
v___x_2484_ = v___x_2458_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v___x_2482_);
v___x_2484_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
lean_object* v___x_2486_; 
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 0, v___x_2484_);
v___x_2486_ = v___x_2453_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v___x_2484_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
}
}
}
else
{
lean_object* v___x_2493_; 
if (v_isShared_2468_ == 0)
{
lean_ctor_set(v___x_2467_, 1, v_snd_2460_);
lean_ctor_set(v___x_2467_, 0, v_snd_2465_);
v___x_2493_ = v___x_2467_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_snd_2465_);
lean_ctor_set(v_reuseFailAlloc_2503_, 1, v_snd_2460_);
v___x_2493_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
lean_object* v___x_2495_; 
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 1, v___x_2493_);
lean_ctor_set(v___x_2462_, 0, v_fst_2464_);
v___x_2495_ = v___x_2462_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_fst_2464_);
lean_ctor_set(v_reuseFailAlloc_2502_, 1, v___x_2493_);
v___x_2495_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
lean_object* v___x_2497_; 
if (v_isShared_2459_ == 0)
{
lean_ctor_set(v___x_2458_, 0, v___x_2495_);
v___x_2497_ = v___x_2458_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v___x_2495_);
v___x_2497_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
lean_object* v___x_2499_; 
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 0, v___x_2497_);
v___x_2499_ = v___x_2453_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v___x_2497_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
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
lean_object* v___x_2508_; lean_object* v___x_2510_; 
lean_dec(v_fst_2455_);
lean_dec(v_a_2451_);
v___x_2508_ = lean_box(0);
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 0, v___x_2508_);
v___x_2510_ = v___x_2453_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v___x_2508_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
else
{
lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2520_; 
v_a_2513_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2515_ = v___x_2450_;
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v___x_2450_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2518_; 
if (v_isShared_2516_ == 0)
{
v___x_2518_ = v___x_2515_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_a_2513_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f___boxed(lean_object* v_e_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(v_e_2521_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_);
lean_dec(v_a_2525_);
lean_dec_ref(v_a_2524_);
lean_dec(v_a_2523_);
lean_dec_ref(v_a_2522_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr___lam__0(lean_object* v___y_2528_){
_start:
{
lean_inc_ref(v___y_2528_);
return v___y_2528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr___lam__0___boxed(lean_object* v___y_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr___lam__0(v___y_2529_);
lean_dec_ref(v___y_2529_);
return v_res_2530_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1(void){
_start:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2532_ = lean_box(0);
v___x_2533_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12));
v___x_2534_ = l_Lean_mkConst(v___x_2533_, v___x_2532_);
return v___x_2534_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__2(void){
_start:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2535_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1);
v___x_2536_ = l_Lean_mkIntLit(v___x_2535_);
return v___x_2536_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__3(void){
_start:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2537_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__2, &l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__2);
v___x_2538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2538_, 0, v___x_2537_);
return v___x_2538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr(lean_object* v_ctx_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_){
_start:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; uint8_t v___x_2547_; 
v___x_2545_ = lean_unsigned_to_nat(0u);
v___x_2546_ = lean_array_get_size(v_ctx_2539_);
v___x_2547_ = lean_nat_dec_lt(v___x_2545_, v___x_2546_);
if (v___x_2547_ == 0)
{
lean_object* v___f_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
lean_dec_ref(v_ctx_2539_);
v___f_2548_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__0));
v___x_2549_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1, &l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1_once, _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1);
v___x_2550_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__3, &l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__3);
v___x_2551_ = l_Lean_RArray_toExpr___redArg(v___x_2549_, v___f_2548_, v___x_2550_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_);
return v___x_2551_;
}
else
{
lean_object* v___f_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___f_2552_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__0));
v___x_2553_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1, &l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1_once, _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1);
v___x_2554_ = l_Lean_RArray_ofArray___redArg(v_ctx_2539_);
v___x_2555_ = l_Lean_RArray_toExpr___redArg(v___x_2553_, v___f_2552_, v___x_2554_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_);
return v___x_2555_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr___boxed(lean_object* v_ctx_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_){
_start:
{
lean_object* v_res_2562_; 
v_res_2562_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_ctx_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_);
lean_dec(v_a_2560_);
lean_dec_ref(v_a_2559_);
lean_dec(v_a_2558_);
lean_dec_ref(v_a_2557_);
return v_res_2562_;
}
}
lean_object* runtime_initialize_Init_Data_Int_Linear(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_SortExprs(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_IntInstTesters(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_KExprMap(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_RArray(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_LitValues(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Int_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_SortExprs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_IntInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_KExprMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_RArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Simp_Arith_Int_instToExprPoly = _init_l_Lean_Meta_Simp_Arith_Int_instToExprPoly();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_instToExprPoly);
l_Lean_Meta_Simp_Arith_Int_instToExprExpr = _init_l_Lean_Meta_Simp_Arith_Int_instToExprExpr();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_instToExprExpr);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Int_Linear(uint8_t builtin);
lean_object* initialize_Lean_Util_SortExprs(uint8_t builtin);
lean_object* initialize_Lean_Meta_IntInstTesters(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_KExprMap(uint8_t builtin);
lean_object* initialize_Lean_Data_RArray(uint8_t builtin);
lean_object* initialize_Lean_Meta_LitValues(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Int_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_SortExprs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_IntInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_KExprMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_RArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
