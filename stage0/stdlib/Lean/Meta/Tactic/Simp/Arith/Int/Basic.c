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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DefEq_isInstLEInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_KExprMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_KExprMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DefEq_isInstHAddInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DefEq_isInstHSubInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DefEq_isInstHMulInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DefEq_isInstAddInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DefEq_isInstSubInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DefEq_isInstMulInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DefEq_isInstNegInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DefEq_isInstLTInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_mkIntMul(lean_object*, lean_object*);
lean_object* l_Lean_mkIntAdd(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DefEq_isInstDvdInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_mkIntSub(lean_object*, lean_object*);
lean_object* l_Lean_mkIntNeg(lean_object*);
lean_object* l_Lean_sortExprs(lean_object*, uint8_t);
lean_object* l_Lean_mkIntLit(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_RArray_toExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RArray_ofArray___redArg(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_applyPerm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_applyPerm___boxed(lean_object*, lean_object*);
static const lean_string_object l_Int_Internal_Linear_instReprPoly__lean_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Int.Internal.Linear.Poly.num"};
static const lean_object* l_Int_Internal_Linear_instReprPoly__lean_repr___closed__0 = (const lean_object*)&l_Int_Internal_Linear_instReprPoly__lean_repr___closed__0_value;
static const lean_ctor_object l_Int_Internal_Linear_instReprPoly__lean_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Int_Internal_Linear_instReprPoly__lean_repr___closed__0_value)}};
static const lean_object* l_Int_Internal_Linear_instReprPoly__lean_repr___closed__1 = (const lean_object*)&l_Int_Internal_Linear_instReprPoly__lean_repr___closed__1_value;
static const lean_ctor_object l_Int_Internal_Linear_instReprPoly__lean_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Int_Internal_Linear_instReprPoly__lean_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Int_Internal_Linear_instReprPoly__lean_repr___closed__2 = (const lean_object*)&l_Int_Internal_Linear_instReprPoly__lean_repr___closed__2_value;
static lean_once_cell_t l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3;
static const lean_string_object l_Int_Internal_Linear_instReprPoly__lean_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Int.Internal.Linear.Poly.add"};
static const lean_object* l_Int_Internal_Linear_instReprPoly__lean_repr___closed__4 = (const lean_object*)&l_Int_Internal_Linear_instReprPoly__lean_repr___closed__4_value;
static const lean_ctor_object l_Int_Internal_Linear_instReprPoly__lean_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Int_Internal_Linear_instReprPoly__lean_repr___closed__4_value)}};
static const lean_object* l_Int_Internal_Linear_instReprPoly__lean_repr___closed__5 = (const lean_object*)&l_Int_Internal_Linear_instReprPoly__lean_repr___closed__5_value;
static const lean_ctor_object l_Int_Internal_Linear_instReprPoly__lean_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Int_Internal_Linear_instReprPoly__lean_repr___closed__5_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Int_Internal_Linear_instReprPoly__lean_repr___closed__6 = (const lean_object*)&l_Int_Internal_Linear_instReprPoly__lean_repr___closed__6_value;
LEAN_EXPORT lean_object* l_Int_Internal_Linear_instReprPoly__lean_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_instReprPoly__lean_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Int_Internal_Linear_instReprPoly__lean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_Internal_Linear_instReprPoly__lean_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int_Internal_Linear_instReprPoly__lean___closed__0 = (const lean_object*)&l_Int_Internal_Linear_instReprPoly__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Int_Internal_Linear_instReprPoly__lean = (const lean_object*)&l_Int_Internal_Linear_instReprPoly__lean___closed__0_value;
static const lean_string_object l_Int_Internal_Linear_instReprExpr__lean_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Int.Internal.Linear.Expr.num"};
static const lean_object* l_Int_Internal_Linear_instReprExpr__lean_repr___closed__0 = (const lean_object*)&l_Int_Internal_Linear_instReprExpr__lean_repr___closed__0_value;
static const lean_ctor_object l_Int_Internal_Linear_instReprExpr__lean_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Int_Internal_Linear_instReprExpr__lean_repr___closed__0_value)}};
static const lean_object* l_Int_Internal_Linear_instReprExpr__lean_repr___closed__1 = (const lean_object*)&l_Int_Internal_Linear_instReprExpr__lean_repr___closed__1_value;
static const lean_ctor_object l_Int_Internal_Linear_instReprExpr__lean_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Int_Internal_Linear_instReprExpr__lean_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Int_Internal_Linear_instReprExpr__lean_repr___closed__2 = (const lean_object*)&l_Int_Internal_Linear_instReprExpr__lean_repr___closed__2_value;
static const lean_string_object l_Int_Internal_Linear_instReprExpr__lean_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Int.Internal.Linear.Expr.var"};
static const lean_object* l_Int_Internal_Linear_instReprExpr__lean_repr___closed__3 = (const lean_object*)&l_Int_Internal_Linear_instReprExpr__lean_repr___closed__3_value;
static const lean_ctor_object l_Int_Internal_Linear_instReprExpr__lean_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Int_Internal_Linear_instReprExpr__lean_repr___closed__3_value)}};
static const lean_object* l_Int_Internal_Linear_instReprExpr__lean_repr___closed__4 = (const lean_object*)&l_Int_Internal_Linear_instReprExpr__lean_repr___closed__4_value;
static const lean_ctor_object l_Int_Internal_Linear_instReprExpr__lean_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Int_Internal_Linear_instReprExpr__lean_repr___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Int_Internal_Linear_instReprExpr__lean_repr___closed__5 = (const lean_object*)&l_Int_Internal_Linear_instReprExpr__lean_repr___closed__5_value;
static const lean_string_object l_Int_Internal_Linear_instReprExpr__lean_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Int.Internal.Linear.Expr.add"};
static const lean_object* l_Int_Internal_Linear_instReprExpr__lean_repr___closed__6 = (const lean_object*)&l_Int_Internal_Linear_instReprExpr__lean_repr___closed__6_value;
static const lean_ctor_object l_Int_Internal_Linear_instReprExpr__lean_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Int_Internal_Linear_instReprExpr__lean_repr___closed__6_value)}};
static const lean_object* l_Int_Internal_Linear_instReprExpr__lean_repr___closed__7 = (const lean_object*)&l_Int_Internal_Linear_instReprExpr__lean_repr___closed__7_value;
static const lean_ctor_object l_Int_Internal_Linear_instReprExpr__lean_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Int_Internal_Linear_instReprExpr__lean_repr___closed__7_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Int_Internal_Linear_instReprExpr__lean_repr___closed__8 = (const lean_object*)&l_Int_Internal_Linear_instReprExpr__lean_repr___closed__8_value;
static const lean_string_object l_Int_Internal_Linear_instReprExpr__lean_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Int.Internal.Linear.Expr.sub"};
static const lean_object* l_Int_Internal_Linear_instReprExpr__lean_repr___closed__9 = (const lean_object*)&l_Int_Internal_Linear_instReprExpr__lean_repr___closed__9_value;
static const lean_ctor_object l_Int_Internal_Linear_instReprExpr__lean_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Int_Internal_Linear_instReprExpr__lean_repr___closed__9_value)}};
static const lean_object* l_Int_Internal_Linear_instReprExpr__lean_repr___closed__10 = (const lean_object*)&l_Int_Internal_Linear_instReprExpr__lean_repr___closed__10_value;
static const lean_ctor_object l_Int_Internal_Linear_instReprExpr__lean_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Int_Internal_Linear_instReprExpr__lean_repr___closed__10_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Int_Internal_Linear_instReprExpr__lean_repr___closed__11 = (const lean_object*)&l_Int_Internal_Linear_instReprExpr__lean_repr___closed__11_value;
static const lean_string_object l_Int_Internal_Linear_instReprExpr__lean_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Int.Internal.Linear.Expr.neg"};
static const lean_object* l_Int_Internal_Linear_instReprExpr__lean_repr___closed__12 = (const lean_object*)&l_Int_Internal_Linear_instReprExpr__lean_repr___closed__12_value;
static const lean_ctor_object l_Int_Internal_Linear_instReprExpr__lean_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Int_Internal_Linear_instReprExpr__lean_repr___closed__12_value)}};
static const lean_object* l_Int_Internal_Linear_instReprExpr__lean_repr___closed__13 = (const lean_object*)&l_Int_Internal_Linear_instReprExpr__lean_repr___closed__13_value;
static const lean_ctor_object l_Int_Internal_Linear_instReprExpr__lean_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Int_Internal_Linear_instReprExpr__lean_repr___closed__13_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Int_Internal_Linear_instReprExpr__lean_repr___closed__14 = (const lean_object*)&l_Int_Internal_Linear_instReprExpr__lean_repr___closed__14_value;
static const lean_string_object l_Int_Internal_Linear_instReprExpr__lean_repr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Int.Internal.Linear.Expr.mulL"};
static const lean_object* l_Int_Internal_Linear_instReprExpr__lean_repr___closed__15 = (const lean_object*)&l_Int_Internal_Linear_instReprExpr__lean_repr___closed__15_value;
static const lean_ctor_object l_Int_Internal_Linear_instReprExpr__lean_repr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Int_Internal_Linear_instReprExpr__lean_repr___closed__15_value)}};
static const lean_object* l_Int_Internal_Linear_instReprExpr__lean_repr___closed__16 = (const lean_object*)&l_Int_Internal_Linear_instReprExpr__lean_repr___closed__16_value;
static const lean_ctor_object l_Int_Internal_Linear_instReprExpr__lean_repr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Int_Internal_Linear_instReprExpr__lean_repr___closed__16_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Int_Internal_Linear_instReprExpr__lean_repr___closed__17 = (const lean_object*)&l_Int_Internal_Linear_instReprExpr__lean_repr___closed__17_value;
static const lean_string_object l_Int_Internal_Linear_instReprExpr__lean_repr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Int.Internal.Linear.Expr.mulR"};
static const lean_object* l_Int_Internal_Linear_instReprExpr__lean_repr___closed__18 = (const lean_object*)&l_Int_Internal_Linear_instReprExpr__lean_repr___closed__18_value;
static const lean_ctor_object l_Int_Internal_Linear_instReprExpr__lean_repr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Int_Internal_Linear_instReprExpr__lean_repr___closed__18_value)}};
static const lean_object* l_Int_Internal_Linear_instReprExpr__lean_repr___closed__19 = (const lean_object*)&l_Int_Internal_Linear_instReprExpr__lean_repr___closed__19_value;
static const lean_ctor_object l_Int_Internal_Linear_instReprExpr__lean_repr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Int_Internal_Linear_instReprExpr__lean_repr___closed__19_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Int_Internal_Linear_instReprExpr__lean_repr___closed__20 = (const lean_object*)&l_Int_Internal_Linear_instReprExpr__lean_repr___closed__20_value;
LEAN_EXPORT lean_object* l_Int_Internal_Linear_instReprExpr__lean_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_instReprExpr__lean_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Int_Internal_Linear_instReprExpr__lean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_Internal_Linear_instReprExpr__lean_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Int_Internal_Linear_instReprExpr__lean___closed__0 = (const lean_object*)&l_Int_Internal_Linear_instReprExpr__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Int_Internal_Linear_instReprExpr__lean = (const lean_object*)&l_Int_Internal_Linear_instReprExpr__lean___closed__0_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linear"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__2_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Poly"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__3_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__3_value),LEAN_SCALAR_PTR_LITERAL(219, 243, 223, 72, 81, 124, 247, 238)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__5_value_aux_3),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__4_value),LEAN_SCALAR_PTR_LITERAL(195, 205, 63, 213, 229, 248, 205, 52)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__5 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__6;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__7_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__8 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__7_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__8_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__9 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__10;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instNegInt"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__15 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__15_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__15_value),LEAN_SCALAR_PTR_LITERAL(217, 109, 233, 1, 211, 122, 77, 88)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "add"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__18 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__18_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__19_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__19_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__19_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__19_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__3_value),LEAN_SCALAR_PTR_LITERAL(219, 243, 223, 72, 81, 124, 247, 238)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__19_value_aux_3),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__18_value),LEAN_SCALAR_PTR_LITERAL(18, 173, 113, 116, 0, 135, 212, 71)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__19 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__19_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__20;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly(lean_object*);
static const lean_closure_object l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Simp_Arith_Int_ofPoly, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__3_value),LEAN_SCALAR_PTR_LITERAL(219, 243, 223, 72, 81, 124, 247, 238)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__2;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprPoly;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Expr"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 251, 136, 155, 162, 62, 241, 107)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1_value_aux_3),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__4_value),LEAN_SCALAR_PTR_LITERAL(215, 182, 254, 77, 89, 153, 240, 232)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__2;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "var"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 251, 136, 155, 162, 62, 241, 107)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4_value_aux_3),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(34, 56, 10, 96, 249, 72, 101, 215)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__5;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 251, 136, 155, 162, 62, 241, 107)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6_value_aux_3),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__18_value),LEAN_SCALAR_PTR_LITERAL(126, 249, 59, 98, 228, 81, 124, 140)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__7;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sub"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__8 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 251, 136, 155, 162, 62, 241, 107)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9_value_aux_3),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__8_value),LEAN_SCALAR_PTR_LITERAL(93, 165, 45, 209, 153, 175, 80, 68)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__10;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 251, 136, 155, 162, 62, 241, 107)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11_value_aux_3),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__8_value),LEAN_SCALAR_PTR_LITERAL(60, 3, 94, 207, 254, 165, 57, 208)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__12;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "mulL"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__13 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 251, 136, 155, 162, 62, 241, 107)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14_value_aux_3),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__13_value),LEAN_SCALAR_PTR_LITERAL(52, 50, 91, 255, 202, 128, 171, 140)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__15;
static const lean_string_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "mulR"};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__16 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 251, 136, 155, 162, 62, 241, 107)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17_value_aux_3),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__16_value),LEAN_SCALAR_PTR_LITERAL(225, 200, 2, 207, 201, 186, 168, 184)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__18;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(lean_object*);
static const lean_closure_object l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Simp_Arith_Int_ofLinearExpr, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__2_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 251, 136, 155, 162, 62, 241, 107)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__2;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprExpr;
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_denoteExpr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_denoteExpr___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_denoteExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_denoteExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_denoteExpr_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_denoteExpr_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_denoteExpr_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_denoteExpr_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__0_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__8_value),LEAN_SCALAR_PTR_LITERAL(222, 124, 176, 23, 127, 116, 25, 232)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__18_value),LEAN_SCALAR_PTR_LITERAL(28, 250, 199, 101, 180, 239, 175, 219)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__18_value),LEAN_SCALAR_PTR_LITERAL(50, 34, 112, 179, 66, 45, 192, 92)}};
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(0u);
v___x_4_ = lean_nat_to_int(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go(lean_object* v_a_5_, lean_object* v_a_6_){
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
lean_dec_ref_known(v_a_6_, 3);
v___x_18_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0);
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
lean_dec_ref_known(v_a_5_, 1);
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
v___x_32_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
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
lean_dec_ref_known(v_a_6_, 3);
v___x_46_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0);
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
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_toExpr(lean_object* v_p_62_){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = lean_box(0);
v___x_64_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go(v___x_63_, v_p_62_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(lean_object* v_a_65_, lean_object* v_x_66_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg___boxed(lean_object* v_a_74_, lean_object* v_x_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(v_a_74_, v_x_75_);
lean_dec(v_x_75_);
lean_dec(v_a_74_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0___redArg(lean_object* v_m_77_, lean_object* v_a_78_){
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
v___x_94_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(v_a_78_, v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0___redArg___boxed(lean_object* v_m_95_, lean_object* v_a_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0___redArg(v_m_95_, v_a_96_);
lean_dec(v_a_96_);
lean_dec_ref(v_m_95_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(lean_object* v_perm_98_, lean_object* v_a_99_){
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
v___x_101_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0___redArg(v_perm_98_, v_i_100_);
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
lean_dec_ref_known(v___x_101_, 1);
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
v___x_116_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_perm_98_, v_a_111_);
v___x_117_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_perm_98_, v_b_112_);
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
v___x_127_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_perm_98_, v_a_122_);
v___x_128_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_perm_98_, v_b_123_);
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
v___x_137_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_perm_98_, v_a_133_);
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
v___x_147_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_perm_98_, v_a_143_);
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
v___x_157_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_perm_98_, v_a_152_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go___boxed(lean_object* v_perm_162_, lean_object* v_a_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_perm_162_, v_a_163_);
lean_dec_ref(v_perm_162_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0(lean_object* v_00_u03b2_165_, lean_object* v_m_166_, lean_object* v_a_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0___redArg(v_m_166_, v_a_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0___boxed(lean_object* v_00_u03b2_169_, lean_object* v_m_170_, lean_object* v_a_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0(v_00_u03b2_169_, v_m_170_, v_a_171_);
lean_dec(v_a_171_);
lean_dec_ref(v_m_170_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0(lean_object* v_00_u03b2_173_, lean_object* v_a_174_, lean_object* v_x_175_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(v_a_174_, v_x_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_177_, lean_object* v_a_178_, lean_object* v_x_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0(v_00_u03b2_177_, v_a_178_, v_x_179_);
lean_dec(v_x_179_);
lean_dec(v_a_178_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_applyPerm(lean_object* v_perm_181_, lean_object* v_e_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_perm_181_, v_e_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_applyPerm___boxed(lean_object* v_perm_184_, lean_object* v_e_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Int_Internal_Linear_Expr_applyPerm(v_perm_184_, v_e_185_);
lean_dec_ref(v_perm_184_);
return v_res_186_;
}
}
static lean_object* _init_l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = lean_unsigned_to_nat(2u);
v___x_194_ = lean_nat_to_int(v___x_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_instReprPoly__lean_repr(lean_object* v_x_201_, lean_object* v_prec_202_){
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
v___x_233_ = lean_obj_once(&l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3, &l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3_once, _init_l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3);
v___y_217_ = v___x_233_;
goto v___jp_216_;
}
else
{
lean_object* v___x_234_; 
v___x_234_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0);
v___y_217_ = v___x_234_;
goto v___jp_216_;
}
v___jp_216_:
{
lean_object* v___x_218_; lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_218_ = ((lean_object*)(l_Int_Internal_Linear_instReprPoly__lean_repr___closed__2));
v___x_219_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
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
lean_dec_ref_known(v_x_201_, 3);
v___x_239_ = lean_unsigned_to_nat(1024u);
v___x_268_ = lean_nat_dec_le(v___x_239_, v_prec_202_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; 
v___x_269_ = lean_obj_once(&l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3, &l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3_once, _init_l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3);
v___y_258_ = v___x_269_;
goto v___jp_257_;
}
else
{
lean_object* v___x_270_; 
v___x_270_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0);
v___y_258_ = v___x_270_;
goto v___jp_257_;
}
v___jp_240_:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
lean_inc(v___y_241_);
v___x_245_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_245_, 0, v___y_241_);
lean_ctor_set(v___x_245_, 1, v___y_244_);
lean_inc_n(v___y_242_, 2);
v___x_246_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
lean_ctor_set(v___x_246_, 1, v___y_242_);
v___x_247_ = l_Nat_reprFast(v_v_237_);
v___x_248_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
v___x_249_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_246_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
v___x_250_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
lean_ctor_set(v___x_250_, 1, v___y_242_);
v___x_251_ = l_Int_Internal_Linear_instReprPoly__lean_repr(v_p_238_, v___x_239_);
v___x_252_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_250_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
lean_inc(v___y_243_);
v___x_253_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_253_, 0, v___y_243_);
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
v___x_260_ = ((lean_object*)(l_Int_Internal_Linear_instReprPoly__lean_repr___closed__6));
v___x_261_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
v___x_262_ = lean_int_dec_lt(v_k_236_, v___x_261_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = l_Int_repr(v_k_236_);
lean_dec(v_k_236_);
v___x_264_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
v___y_241_ = v___x_260_;
v___y_242_ = v___x_259_;
v___y_243_ = v___y_258_;
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
v___y_241_ = v___x_260_;
v___y_242_ = v___x_259_;
v___y_243_ = v___y_258_;
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
LEAN_EXPORT lean_object* l_Int_Internal_Linear_instReprPoly__lean_repr___boxed(lean_object* v_x_271_, lean_object* v_prec_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Int_Internal_Linear_instReprPoly__lean_repr(v_x_271_, v_prec_272_);
lean_dec(v_prec_272_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_instReprExpr__lean_repr(lean_object* v_x_318_, lean_object* v_prec_319_){
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
v___x_359_ = lean_obj_once(&l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3, &l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3_once, _init_l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3);
v___y_343_ = v___x_359_;
goto v___jp_342_;
}
else
{
lean_object* v___x_360_; 
v___x_360_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0);
v___y_343_ = v___x_360_;
goto v___jp_342_;
}
v___jp_342_:
{
lean_object* v___x_344_; lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_344_ = ((lean_object*)(l_Int_Internal_Linear_instReprExpr__lean_repr___closed__2));
v___x_345_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
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
v___x_380_ = lean_obj_once(&l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3, &l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3_once, _init_l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3);
v___y_367_ = v___x_380_;
goto v___jp_366_;
}
else
{
lean_object* v___x_381_; 
v___x_381_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0);
v___y_367_ = v___x_381_;
goto v___jp_366_;
}
v___jp_366_:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_371_; 
v___x_368_ = ((lean_object*)(l_Int_Internal_Linear_instReprExpr__lean_repr___closed__5));
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
v___x_405_ = lean_obj_once(&l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3, &l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3_once, _init_l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3);
v___y_390_ = v___x_405_;
goto v___jp_389_;
}
else
{
lean_object* v___x_406_; 
v___x_406_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0);
v___y_390_ = v___x_406_;
goto v___jp_389_;
}
v___jp_389_:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_395_; 
v___x_391_ = lean_box(1);
v___x_392_ = ((lean_object*)(l_Int_Internal_Linear_instReprExpr__lean_repr___closed__8));
v___x_393_ = l_Int_Internal_Linear_instReprExpr__lean_repr(v_a_383_, v___x_388_);
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
v___x_397_ = l_Int_Internal_Linear_instReprExpr__lean_repr(v_b_384_, v___x_388_);
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
v___x_430_ = lean_obj_once(&l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3, &l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3_once, _init_l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3);
v___y_415_ = v___x_430_;
goto v___jp_414_;
}
else
{
lean_object* v___x_431_; 
v___x_431_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0);
v___y_415_ = v___x_431_;
goto v___jp_414_;
}
v___jp_414_:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_420_; 
v___x_416_ = lean_box(1);
v___x_417_ = ((lean_object*)(l_Int_Internal_Linear_instReprExpr__lean_repr___closed__11));
v___x_418_ = l_Int_Internal_Linear_instReprExpr__lean_repr(v_a_408_, v___x_413_);
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
v___x_422_ = l_Int_Internal_Linear_instReprExpr__lean_repr(v_b_409_, v___x_413_);
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
lean_dec_ref_known(v_x_318_, 1);
v___x_434_ = lean_unsigned_to_nat(1024u);
v___x_444_ = lean_nat_dec_le(v___x_434_, v_prec_319_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; 
v___x_445_ = lean_obj_once(&l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3, &l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3_once, _init_l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3);
v___y_436_ = v___x_445_;
goto v___jp_435_;
}
else
{
lean_object* v___x_446_; 
v___x_446_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0);
v___y_436_ = v___x_446_;
goto v___jp_435_;
}
v___jp_435_:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_437_ = ((lean_object*)(l_Int_Internal_Linear_instReprExpr__lean_repr___closed__14));
v___x_438_ = l_Int_Internal_Linear_instReprExpr__lean_repr(v_a_433_, v___x_434_);
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
v___x_480_ = lean_obj_once(&l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3, &l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3_once, _init_l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3);
v___y_469_ = v___x_480_;
goto v___jp_468_;
}
else
{
lean_object* v___x_481_; 
v___x_481_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0);
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
lean_inc(v___y_455_);
v___x_460_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
lean_ctor_set(v___x_460_, 1, v___y_455_);
v___x_461_ = l_Int_Internal_Linear_instReprExpr__lean_repr(v_a_448_, v___x_452_);
v___x_462_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_462_, 0, v___x_460_);
lean_ctor_set(v___x_462_, 1, v___x_461_);
lean_inc(v___y_454_);
v___x_463_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_463_, 0, v___y_454_);
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
v___x_471_ = ((lean_object*)(l_Int_Internal_Linear_instReprExpr__lean_repr___closed__17));
v___x_472_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
v___x_473_ = lean_int_dec_lt(v_k_447_, v___x_472_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_474_ = l_Int_repr(v_k_447_);
lean_dec(v_k_447_);
v___x_475_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
v___y_454_ = v___y_469_;
v___y_455_ = v___x_470_;
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
v___y_454_ = v___y_469_;
v___y_455_ = v___x_470_;
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
v___x_506_ = lean_obj_once(&l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3, &l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3_once, _init_l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3);
v___y_490_ = v___x_506_;
goto v___jp_489_;
}
else
{
lean_object* v___x_507_; 
v___x_507_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0);
v___y_490_ = v___x_507_;
goto v___jp_489_;
}
v___jp_489_:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_495_; 
v___x_491_ = lean_box(1);
v___x_492_ = ((lean_object*)(l_Int_Internal_Linear_instReprExpr__lean_repr___closed__20));
v___x_493_ = l_Int_Internal_Linear_instReprExpr__lean_repr(v_a_483_, v___x_488_);
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
v___x_497_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
v___x_498_ = lean_int_dec_lt(v_k_484_, v___x_497_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = l_Int_repr(v_k_484_);
lean_dec(v_k_484_);
v___x_500_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
v___y_321_ = v___y_490_;
v___y_322_ = v___x_496_;
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
v___y_321_ = v___y_490_;
v___y_322_ = v___x_496_;
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
lean_ctor_set(v___x_324_, 0, v___y_322_);
lean_ctor_set(v___x_324_, 1, v___y_323_);
lean_inc(v___y_321_);
v___x_325_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_325_, 0, v___y_321_);
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
LEAN_EXPORT lean_object* l_Int_Internal_Linear_instReprExpr__lean_repr___boxed(lean_object* v_x_509_, lean_object* v_prec_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Int_Internal_Linear_instReprExpr__lean_repr(v_x_509_, v_prec_510_);
lean_dec(v_prec_510_);
return v_res_511_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__6(void){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_525_ = lean_box(0);
v___x_526_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__5));
v___x_527_ = l_Lean_mkConst(v___x_526_, v___x_525_);
return v___x_527_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__10(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = lean_unsigned_to_nat(0u);
v___x_534_ = l_Lean_Level_ofNat(v___x_533_);
return v___x_534_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_535_ = lean_box(0);
v___x_536_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__10, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__10_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__10);
v___x_537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
lean_ctor_set(v___x_537_, 1, v___x_535_);
return v___x_537_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_538_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11);
v___x_539_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__9));
v___x_540_ = l_Lean_Expr_const___override(v___x_539_, v___x_538_);
return v___x_540_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14(void){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_543_ = lean_box(0);
v___x_544_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13));
v___x_545_ = l_Lean_Expr_const___override(v___x_544_, v___x_543_);
return v___x_545_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17(void){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_550_ = lean_box(0);
v___x_551_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16));
v___x_552_ = l_Lean_Expr_const___override(v___x_551_, v___x_550_);
return v___x_552_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__20(void){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_560_ = lean_box(0);
v___x_561_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__19));
v___x_562_ = l_Lean_mkConst(v___x_561_, v___x_560_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly(lean_object* v_p_563_){
_start:
{
if (lean_obj_tag(v_p_563_) == 0)
{
lean_object* v_k_564_; lean_object* v___x_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
v_k_564_ = lean_ctor_get(v_p_563_, 0);
lean_inc(v_k_564_);
lean_dec_ref_known(v_p_563_, 1);
v___x_565_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__6, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__6_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__6);
v___x_566_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
v___x_567_ = lean_int_dec_le(v___x_566_, v_k_564_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_568_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12);
v___x_569_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14);
v___x_570_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17);
v___x_571_ = lean_int_neg(v_k_564_);
lean_dec(v_k_564_);
v___x_572_ = l_Int_toNat(v___x_571_);
lean_dec(v___x_571_);
v___x_573_ = l_Lean_instToExprInt_mkNat(v___x_572_);
v___x_574_ = l_Lean_mkApp3(v___x_568_, v___x_569_, v___x_570_, v___x_573_);
v___x_575_ = l_Lean_Expr_app___override(v___x_565_, v___x_574_);
return v___x_575_;
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_576_ = l_Int_toNat(v_k_564_);
lean_dec(v_k_564_);
v___x_577_ = l_Lean_instToExprInt_mkNat(v___x_576_);
v___x_578_ = l_Lean_Expr_app___override(v___x_565_, v___x_577_);
return v___x_578_;
}
}
else
{
lean_object* v_k_579_; lean_object* v_v_580_; lean_object* v_p_581_; lean_object* v___x_582_; lean_object* v___y_584_; lean_object* v___x_588_; uint8_t v___x_589_; 
v_k_579_ = lean_ctor_get(v_p_563_, 0);
lean_inc(v_k_579_);
v_v_580_ = lean_ctor_get(v_p_563_, 1);
lean_inc(v_v_580_);
v_p_581_ = lean_ctor_get(v_p_563_, 2);
lean_inc_ref(v_p_581_);
lean_dec_ref_known(v_p_563_, 3);
v___x_582_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__20, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__20_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__20);
v___x_588_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
v___x_589_ = lean_int_dec_le(v___x_588_, v_k_579_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_590_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12);
v___x_591_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14);
v___x_592_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17);
v___x_593_ = lean_int_neg(v_k_579_);
lean_dec(v_k_579_);
v___x_594_ = l_Int_toNat(v___x_593_);
lean_dec(v___x_593_);
v___x_595_ = l_Lean_instToExprInt_mkNat(v___x_594_);
v___x_596_ = l_Lean_mkApp3(v___x_590_, v___x_591_, v___x_592_, v___x_595_);
v___y_584_ = v___x_596_;
goto v___jp_583_;
}
else
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = l_Int_toNat(v_k_579_);
lean_dec(v_k_579_);
v___x_598_ = l_Lean_instToExprInt_mkNat(v___x_597_);
v___y_584_ = v___x_598_;
goto v___jp_583_;
}
v___jp_583_:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_585_ = l_Lean_mkNatLit(v_v_580_);
v___x_586_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v_p_581_);
v___x_587_ = l_Lean_mkApp3(v___x_582_, v___y_584_, v___x_585_, v___x_586_);
return v___x_587_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__2(void){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_605_ = lean_box(0);
v___x_606_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__1));
v___x_607_ = l_Lean_mkConst(v___x_606_, v___x_605_);
return v___x_607_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__3(void){
_start:
{
lean_object* v___x_608_; lean_object* v___f_609_; lean_object* v___x_610_; 
v___x_608_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__2, &l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__2);
v___f_609_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__0));
v___x_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_610_, 0, v___f_609_);
lean_ctor_set(v___x_610_, 1, v___x_608_);
return v___x_610_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_instToExprPoly(void){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__3, &l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__3);
return v___x_611_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__2(void){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_619_ = lean_box(0);
v___x_620_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1));
v___x_621_ = l_Lean_mkConst(v___x_620_, v___x_619_);
return v___x_621_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__5(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_629_ = lean_box(0);
v___x_630_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4));
v___x_631_ = l_Lean_mkConst(v___x_630_, v___x_629_);
return v___x_631_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__7(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_638_ = lean_box(0);
v___x_639_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6));
v___x_640_ = l_Lean_mkConst(v___x_639_, v___x_638_);
return v___x_640_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__10(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_648_ = lean_box(0);
v___x_649_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9));
v___x_650_ = l_Lean_mkConst(v___x_649_, v___x_648_);
return v___x_650_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__12(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_657_ = lean_box(0);
v___x_658_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11));
v___x_659_ = l_Lean_mkConst(v___x_658_, v___x_657_);
return v___x_659_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__15(void){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_667_ = lean_box(0);
v___x_668_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14));
v___x_669_ = l_Lean_mkConst(v___x_668_, v___x_667_);
return v___x_669_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__18(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_677_ = lean_box(0);
v___x_678_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17));
v___x_679_ = l_Lean_mkConst(v___x_678_, v___x_677_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(lean_object* v_e_680_){
_start:
{
switch(lean_obj_tag(v_e_680_))
{
case 0:
{
lean_object* v_v_681_; lean_object* v___x_682_; lean_object* v___x_683_; uint8_t v___x_684_; 
v_v_681_ = lean_ctor_get(v_e_680_, 0);
lean_inc(v_v_681_);
lean_dec_ref_known(v_e_680_, 1);
v___x_682_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__2, &l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__2);
v___x_683_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
v___x_684_ = lean_int_dec_le(v___x_683_, v_v_681_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_685_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12);
v___x_686_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14);
v___x_687_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17);
v___x_688_ = lean_int_neg(v_v_681_);
lean_dec(v_v_681_);
v___x_689_ = l_Int_toNat(v___x_688_);
lean_dec(v___x_688_);
v___x_690_ = l_Lean_instToExprInt_mkNat(v___x_689_);
v___x_691_ = l_Lean_mkApp3(v___x_685_, v___x_686_, v___x_687_, v___x_690_);
v___x_692_ = l_Lean_Expr_app___override(v___x_682_, v___x_691_);
return v___x_692_;
}
else
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_693_ = l_Int_toNat(v_v_681_);
lean_dec(v_v_681_);
v___x_694_ = l_Lean_instToExprInt_mkNat(v___x_693_);
v___x_695_ = l_Lean_Expr_app___override(v___x_682_, v___x_694_);
return v___x_695_;
}
}
case 1:
{
lean_object* v_i_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v_i_696_ = lean_ctor_get(v_e_680_, 0);
lean_inc(v_i_696_);
lean_dec_ref_known(v_e_680_, 1);
v___x_697_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__5, &l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__5);
v___x_698_ = l_Lean_mkNatLit(v_i_696_);
v___x_699_ = l_Lean_Expr_app___override(v___x_697_, v___x_698_);
return v___x_699_;
}
case 2:
{
lean_object* v_a_700_; lean_object* v_b_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v_a_700_ = lean_ctor_get(v_e_680_, 0);
lean_inc_ref(v_a_700_);
v_b_701_ = lean_ctor_get(v_e_680_, 1);
lean_inc_ref(v_b_701_);
lean_dec_ref_known(v_e_680_, 2);
v___x_702_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__7, &l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__7_once, _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__7);
v___x_703_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_a_700_);
v___x_704_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_b_701_);
v___x_705_ = l_Lean_mkAppB(v___x_702_, v___x_703_, v___x_704_);
return v___x_705_;
}
case 3:
{
lean_object* v_a_706_; lean_object* v_b_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v_a_706_ = lean_ctor_get(v_e_680_, 0);
lean_inc_ref(v_a_706_);
v_b_707_ = lean_ctor_get(v_e_680_, 1);
lean_inc_ref(v_b_707_);
lean_dec_ref_known(v_e_680_, 2);
v___x_708_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__10, &l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__10_once, _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__10);
v___x_709_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_a_706_);
v___x_710_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_b_707_);
v___x_711_ = l_Lean_mkAppB(v___x_708_, v___x_709_, v___x_710_);
return v___x_711_;
}
case 4:
{
lean_object* v_a_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v_a_712_ = lean_ctor_get(v_e_680_, 0);
lean_inc_ref(v_a_712_);
lean_dec_ref_known(v_e_680_, 1);
v___x_713_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__12, &l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__12);
v___x_714_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_a_712_);
v___x_715_ = l_Lean_Expr_app___override(v___x_713_, v___x_714_);
return v___x_715_;
}
case 5:
{
lean_object* v_k_716_; lean_object* v_a_717_; lean_object* v___x_718_; lean_object* v___y_720_; lean_object* v___x_723_; uint8_t v___x_724_; 
v_k_716_ = lean_ctor_get(v_e_680_, 0);
lean_inc(v_k_716_);
v_a_717_ = lean_ctor_get(v_e_680_, 1);
lean_inc_ref(v_a_717_);
lean_dec_ref_known(v_e_680_, 2);
v___x_718_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__15, &l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__15_once, _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__15);
v___x_723_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
v___x_724_ = lean_int_dec_le(v___x_723_, v_k_716_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_725_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12);
v___x_726_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14);
v___x_727_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17);
v___x_728_ = lean_int_neg(v_k_716_);
lean_dec(v_k_716_);
v___x_729_ = l_Int_toNat(v___x_728_);
lean_dec(v___x_728_);
v___x_730_ = l_Lean_instToExprInt_mkNat(v___x_729_);
v___x_731_ = l_Lean_mkApp3(v___x_725_, v___x_726_, v___x_727_, v___x_730_);
v___y_720_ = v___x_731_;
goto v___jp_719_;
}
else
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = l_Int_toNat(v_k_716_);
lean_dec(v_k_716_);
v___x_733_ = l_Lean_instToExprInt_mkNat(v___x_732_);
v___y_720_ = v___x_733_;
goto v___jp_719_;
}
v___jp_719_:
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_a_717_);
v___x_722_ = l_Lean_mkAppB(v___x_718_, v___y_720_, v___x_721_);
return v___x_722_;
}
}
default: 
{
lean_object* v_a_734_; lean_object* v_k_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v_a_734_ = lean_ctor_get(v_e_680_, 0);
lean_inc_ref(v_a_734_);
v_k_735_ = lean_ctor_get(v_e_680_, 1);
lean_inc(v_k_735_);
lean_dec_ref_known(v_e_680_, 2);
v___x_736_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__18, &l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__18_once, _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__18);
v___x_737_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_a_734_);
v___x_738_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
v___x_739_ = lean_int_dec_le(v___x_738_, v_k_735_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_740_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12);
v___x_741_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14);
v___x_742_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17);
v___x_743_ = lean_int_neg(v_k_735_);
lean_dec(v_k_735_);
v___x_744_ = l_Int_toNat(v___x_743_);
lean_dec(v___x_743_);
v___x_745_ = l_Lean_instToExprInt_mkNat(v___x_744_);
v___x_746_ = l_Lean_mkApp3(v___x_740_, v___x_741_, v___x_742_, v___x_745_);
v___x_747_ = l_Lean_mkAppB(v___x_736_, v___x_737_, v___x_746_);
return v___x_747_;
}
else
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_748_ = l_Int_toNat(v_k_735_);
lean_dec(v_k_735_);
v___x_749_ = l_Lean_instToExprInt_mkNat(v___x_748_);
v___x_750_ = l_Lean_mkAppB(v___x_736_, v___x_737_, v___x_749_);
return v___x_750_;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__2(void){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_757_ = lean_box(0);
v___x_758_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__1));
v___x_759_ = l_Lean_mkConst(v___x_758_, v___x_757_);
return v___x_759_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__3(void){
_start:
{
lean_object* v___x_760_; lean_object* v___f_761_; lean_object* v___x_762_; 
v___x_760_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__2, &l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__2);
v___f_761_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__0));
v___x_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_762_, 0, v___f_761_);
lean_ctor_set(v___x_762_, 1, v___x_760_);
return v___x_762_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_instToExprExpr(void){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__3, &l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__3);
return v___x_763_;
}
}
lean_object* l_Int_Internal_Linear_Expr_denoteExpr___redArg(lean_object* v_ctx_764_, lean_object* v_e_765_){
_start:
{
switch(lean_obj_tag(v_e_765_))
{
case 0:
{
lean_object* v_v_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_788_; 
lean_dec_ref(v_ctx_764_);
v_v_767_ = lean_ctor_get(v_e_765_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v_e_765_);
if (v_isSharedCheck_788_ == 0)
{
v___x_769_ = v_e_765_;
v_isShared_770_ = v_isSharedCheck_788_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_v_767_);
lean_dec(v_e_765_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_788_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_771_; uint8_t v___x_772_; 
v___x_771_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
v___x_772_ = lean_int_dec_le(v___x_771_, v_v_767_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_781_; 
v___x_773_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12);
v___x_774_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14);
v___x_775_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17);
v___x_776_ = lean_int_neg(v_v_767_);
lean_dec(v_v_767_);
v___x_777_ = l_Int_toNat(v___x_776_);
lean_dec(v___x_776_);
v___x_778_ = l_Lean_instToExprInt_mkNat(v___x_777_);
v___x_779_ = l_Lean_mkApp3(v___x_773_, v___x_774_, v___x_775_, v___x_778_);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 0, v___x_779_);
v___x_781_ = v___x_769_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_779_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
else
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_786_; 
v___x_783_ = l_Int_toNat(v_v_767_);
lean_dec(v_v_767_);
v___x_784_ = l_Lean_instToExprInt_mkNat(v___x_783_);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 0, v___x_784_);
v___x_786_ = v___x_769_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_784_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
case 1:
{
lean_object* v_i_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_797_; 
v_i_789_ = lean_ctor_get(v_e_765_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v_e_765_);
if (v_isSharedCheck_797_ == 0)
{
v___x_791_ = v_e_765_;
v_isShared_792_ = v_isSharedCheck_797_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_i_789_);
lean_dec(v_e_765_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_797_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; lean_object* v___x_795_; 
v___x_793_ = lean_apply_1(v_ctx_764_, v_i_789_);
if (v_isShared_792_ == 0)
{
lean_ctor_set_tag(v___x_791_, 0);
lean_ctor_set(v___x_791_, 0, v___x_793_);
v___x_795_ = v___x_791_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
case 2:
{
lean_object* v_a_798_; lean_object* v_b_799_; lean_object* v___x_800_; lean_object* v_a_801_; lean_object* v___x_802_; lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_811_; 
v_a_798_ = lean_ctor_get(v_e_765_, 0);
lean_inc_ref(v_a_798_);
v_b_799_ = lean_ctor_get(v_e_765_, 1);
lean_inc_ref(v_b_799_);
lean_dec_ref_known(v_e_765_, 2);
lean_inc_ref(v_ctx_764_);
v___x_800_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v_ctx_764_, v_a_798_);
v_a_801_ = lean_ctor_get(v___x_800_, 0);
lean_inc(v_a_801_);
lean_dec_ref(v___x_800_);
v___x_802_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v_ctx_764_, v_b_799_);
v_a_803_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_811_ == 0)
{
v___x_805_ = v___x_802_;
v_isShared_806_ = v_isSharedCheck_811_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_802_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_811_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_807_; lean_object* v___x_809_; 
v___x_807_ = l_Lean_mkIntAdd(v_a_801_, v_a_803_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v___x_807_);
v___x_809_ = v___x_805_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_807_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
case 3:
{
lean_object* v_a_812_; lean_object* v_b_813_; lean_object* v___x_814_; lean_object* v_a_815_; lean_object* v___x_816_; lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_825_; 
v_a_812_ = lean_ctor_get(v_e_765_, 0);
lean_inc_ref(v_a_812_);
v_b_813_ = lean_ctor_get(v_e_765_, 1);
lean_inc_ref(v_b_813_);
lean_dec_ref_known(v_e_765_, 2);
lean_inc_ref(v_ctx_764_);
v___x_814_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v_ctx_764_, v_a_812_);
v_a_815_ = lean_ctor_get(v___x_814_, 0);
lean_inc(v_a_815_);
lean_dec_ref(v___x_814_);
v___x_816_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v_ctx_764_, v_b_813_);
v_a_817_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_825_ == 0)
{
v___x_819_ = v___x_816_;
v_isShared_820_ = v_isSharedCheck_825_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_816_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_825_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_821_; lean_object* v___x_823_; 
v___x_821_ = l_Lean_mkIntSub(v_a_815_, v_a_817_);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 0, v___x_821_);
v___x_823_ = v___x_819_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_821_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
case 4:
{
lean_object* v_a_826_; lean_object* v___x_827_; lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_836_; 
v_a_826_ = lean_ctor_get(v_e_765_, 0);
lean_inc_ref(v_a_826_);
lean_dec_ref_known(v_e_765_, 1);
v___x_827_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v_ctx_764_, v_a_826_);
v_a_828_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_836_ == 0)
{
v___x_830_ = v___x_827_;
v_isShared_831_ = v_isSharedCheck_836_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_827_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_836_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_832_; lean_object* v___x_834_; 
v___x_832_ = l_Lean_mkIntNeg(v_a_828_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v___x_832_);
v___x_834_ = v___x_830_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_832_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
case 5:
{
lean_object* v_k_837_; lean_object* v_a_838_; lean_object* v___x_839_; lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_861_; 
v_k_837_ = lean_ctor_get(v_e_765_, 0);
lean_inc(v_k_837_);
v_a_838_ = lean_ctor_get(v_e_765_, 1);
lean_inc_ref(v_a_838_);
lean_dec_ref_known(v_e_765_, 2);
v___x_839_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v_ctx_764_, v_a_838_);
v_a_840_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_861_ == 0)
{
v___x_842_ = v___x_839_;
v_isShared_843_ = v_isSharedCheck_861_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_839_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_861_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___y_845_; lean_object* v___x_850_; uint8_t v___x_851_; 
v___x_850_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
v___x_851_ = lean_int_dec_le(v___x_850_, v_k_837_);
if (v___x_851_ == 0)
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_852_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12);
v___x_853_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14);
v___x_854_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17);
v___x_855_ = lean_int_neg(v_k_837_);
lean_dec(v_k_837_);
v___x_856_ = l_Int_toNat(v___x_855_);
lean_dec(v___x_855_);
v___x_857_ = l_Lean_instToExprInt_mkNat(v___x_856_);
v___x_858_ = l_Lean_mkApp3(v___x_852_, v___x_853_, v___x_854_, v___x_857_);
v___y_845_ = v___x_858_;
goto v___jp_844_;
}
else
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = l_Int_toNat(v_k_837_);
lean_dec(v_k_837_);
v___x_860_ = l_Lean_instToExprInt_mkNat(v___x_859_);
v___y_845_ = v___x_860_;
goto v___jp_844_;
}
v___jp_844_:
{
lean_object* v___x_846_; lean_object* v___x_848_; 
v___x_846_ = l_Lean_mkIntMul(v___y_845_, v_a_840_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v___x_846_);
v___x_848_ = v___x_842_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_846_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
default: 
{
lean_object* v_a_862_; lean_object* v_k_863_; lean_object* v___x_864_; lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_886_; 
v_a_862_ = lean_ctor_get(v_e_765_, 0);
lean_inc_ref(v_a_862_);
v_k_863_ = lean_ctor_get(v_e_765_, 1);
lean_inc(v_k_863_);
lean_dec_ref_known(v_e_765_, 2);
v___x_864_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v_ctx_764_, v_a_862_);
v_a_865_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_886_ == 0)
{
v___x_867_ = v___x_864_;
v_isShared_868_ = v_isSharedCheck_886_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_864_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_886_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___y_870_; lean_object* v___x_875_; uint8_t v___x_876_; 
v___x_875_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
v___x_876_ = lean_int_dec_le(v___x_875_, v_k_863_);
if (v___x_876_ == 0)
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_877_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12);
v___x_878_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14);
v___x_879_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17);
v___x_880_ = lean_int_neg(v_k_863_);
lean_dec(v_k_863_);
v___x_881_ = l_Int_toNat(v___x_880_);
lean_dec(v___x_880_);
v___x_882_ = l_Lean_instToExprInt_mkNat(v___x_881_);
v___x_883_ = l_Lean_mkApp3(v___x_877_, v___x_878_, v___x_879_, v___x_882_);
v___y_870_ = v___x_883_;
goto v___jp_869_;
}
else
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = l_Int_toNat(v_k_863_);
lean_dec(v_k_863_);
v___x_885_ = l_Lean_instToExprInt_mkNat(v___x_884_);
v___y_870_ = v___x_885_;
goto v___jp_869_;
}
v___jp_869_:
{
lean_object* v___x_871_; lean_object* v___x_873_; 
v___x_871_ = l_Lean_mkIntMul(v_a_865_, v___y_870_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_871_);
v___x_873_ = v___x_867_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_871_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Int_Internal_Linear_Expr_denoteExpr___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_764_ = stack[0].m_obj;
lean_object* v_e_765_ = stack[1].m_obj;
lean_object* v_res_887_;
v_res_887_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v_ctx_764_, v_e_765_);
stack->m_obj
 = v_res_887_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_denoteExpr___redArg___boxed(lean_object* v_ctx_888_, lean_object* v_e_889_, lean_object* v_a_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v_ctx_888_, v_e_889_);
return v_res_891_;
}
}
lean_object* l_Int_Internal_Linear_Expr_denoteExpr(lean_object* v_ctx_892_, lean_object* v_e_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v_ctx_892_, v_e_893_);
return v___x_899_;
}
}
LEAN_EXPORT void l_Int_Internal_Linear_Expr_denoteExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_892_ = stack[0].m_obj;
lean_object* v_e_893_ = stack[1].m_obj;
lean_object* v_a_894_ = stack[2].m_obj;
lean_object* v_a_895_ = stack[3].m_obj;
lean_object* v_a_896_ = stack[4].m_obj;
lean_object* v_a_897_ = stack[5].m_obj;
lean_object* v_res_900_;
v_res_900_ = l_Int_Internal_Linear_Expr_denoteExpr(v_ctx_892_, v_e_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_);
stack->m_obj
 = v_res_900_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_denoteExpr___boxed(lean_object* v_ctx_901_, lean_object* v_e_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Int_Internal_Linear_Expr_denoteExpr(v_ctx_901_, v_e_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
lean_dec(v_a_904_);
lean_dec_ref(v_a_903_);
return v_res_908_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_denoteExpr_go___redArg(lean_object* v_ctx_909_, lean_object* v_r_910_, lean_object* v_p_911_){
_start:
{
lean_object* v___y_914_; 
if (lean_obj_tag(v_p_911_) == 0)
{
lean_object* v_k_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_936_; 
lean_dec_ref(v_ctx_909_);
v_k_917_ = lean_ctor_get(v_p_911_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v_p_911_);
if (v_isSharedCheck_936_ == 0)
{
v___x_919_ = v_p_911_;
v_isShared_920_ = v_isSharedCheck_936_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_k_917_);
lean_dec(v_p_911_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_936_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_921_; uint8_t v___x_922_; 
v___x_921_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
v___x_922_ = lean_int_dec_eq(v_k_917_, v___x_921_);
if (v___x_922_ == 0)
{
uint8_t v___x_923_; 
lean_del_object(v___x_919_);
v___x_923_ = lean_int_dec_le(v___x_921_, v_k_917_);
if (v___x_923_ == 0)
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_924_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12);
v___x_925_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14);
v___x_926_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17);
v___x_927_ = lean_int_neg(v_k_917_);
lean_dec(v_k_917_);
v___x_928_ = l_Int_toNat(v___x_927_);
lean_dec(v___x_927_);
v___x_929_ = l_Lean_instToExprInt_mkNat(v___x_928_);
v___x_930_ = l_Lean_mkApp3(v___x_924_, v___x_925_, v___x_926_, v___x_929_);
v___y_914_ = v___x_930_;
goto v___jp_913_;
}
else
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = l_Int_toNat(v_k_917_);
lean_dec(v_k_917_);
v___x_932_ = l_Lean_instToExprInt_mkNat(v___x_931_);
v___y_914_ = v___x_932_;
goto v___jp_913_;
}
}
else
{
lean_object* v___x_934_; 
lean_dec(v_k_917_);
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 0, v_r_910_);
v___x_934_ = v___x_919_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_r_910_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
else
{
lean_object* v_k_937_; lean_object* v_v_938_; lean_object* v_p_939_; lean_object* v___y_941_; lean_object* v___x_946_; uint8_t v___x_947_; 
v_k_937_ = lean_ctor_get(v_p_911_, 0);
lean_inc(v_k_937_);
v_v_938_ = lean_ctor_get(v_p_911_, 1);
lean_inc(v_v_938_);
v_p_939_ = lean_ctor_get(v_p_911_, 2);
lean_inc_ref(v_p_939_);
lean_dec_ref_known(v_p_911_, 3);
v___x_946_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0);
v___x_947_ = lean_int_dec_eq(v_k_937_, v___x_946_);
if (v___x_947_ == 0)
{
lean_object* v___x_948_; uint8_t v___x_949_; 
v___x_948_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
v___x_949_ = lean_int_dec_le(v___x_948_, v_k_937_);
if (v___x_949_ == 0)
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_950_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12);
v___x_951_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14);
v___x_952_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17);
v___x_953_ = lean_int_neg(v_k_937_);
lean_dec(v_k_937_);
v___x_954_ = l_Int_toNat(v___x_953_);
lean_dec(v___x_953_);
v___x_955_ = l_Lean_instToExprInt_mkNat(v___x_954_);
v___x_956_ = l_Lean_mkApp3(v___x_950_, v___x_951_, v___x_952_, v___x_955_);
v___y_941_ = v___x_956_;
goto v___jp_940_;
}
else
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = l_Int_toNat(v_k_937_);
lean_dec(v_k_937_);
v___x_958_ = l_Lean_instToExprInt_mkNat(v___x_957_);
v___y_941_ = v___x_958_;
goto v___jp_940_;
}
}
else
{
lean_object* v___x_959_; lean_object* v___x_960_; 
lean_dec(v_k_937_);
lean_inc_ref(v_ctx_909_);
v___x_959_ = lean_apply_1(v_ctx_909_, v_v_938_);
v___x_960_ = l_Lean_mkIntAdd(v_r_910_, v___x_959_);
v_r_910_ = v___x_960_;
v_p_911_ = v_p_939_;
goto _start;
}
v___jp_940_:
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
lean_inc_ref(v_ctx_909_);
v___x_942_ = lean_apply_1(v_ctx_909_, v_v_938_);
v___x_943_ = l_Lean_mkIntMul(v___y_941_, v___x_942_);
v___x_944_ = l_Lean_mkIntAdd(v_r_910_, v___x_943_);
v_r_910_ = v___x_944_;
v_p_911_ = v_p_939_;
goto _start;
}
}
v___jp_913_:
{
lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_915_ = l_Lean_mkIntAdd(v_r_910_, v___y_914_);
v___x_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
return v___x_916_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_denoteExpr_go___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_909_ = stack[0].m_obj;
lean_object* v_r_910_ = stack[1].m_obj;
lean_object* v_p_911_ = stack[2].m_obj;
lean_object* v_res_962_;
v_res_962_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_denoteExpr_go___redArg(v_ctx_909_, v_r_910_, v_p_911_);
stack->m_obj
 = v_res_962_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_denoteExpr_go___redArg___boxed(lean_object* v_ctx_963_, lean_object* v_r_964_, lean_object* v_p_965_, lean_object* v_a_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_denoteExpr_go___redArg(v_ctx_963_, v_r_964_, v_p_965_);
return v_res_967_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_denoteExpr_go(lean_object* v_ctx_968_, lean_object* v_r_969_, lean_object* v_p_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_denoteExpr_go___redArg(v_ctx_968_, v_r_969_, v_p_970_);
return v___x_976_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_denoteExpr_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_968_ = stack[0].m_obj;
lean_object* v_r_969_ = stack[1].m_obj;
lean_object* v_p_970_ = stack[2].m_obj;
lean_object* v_a_971_ = stack[3].m_obj;
lean_object* v_a_972_ = stack[4].m_obj;
lean_object* v_a_973_ = stack[5].m_obj;
lean_object* v_a_974_ = stack[6].m_obj;
lean_object* v_res_977_;
v_res_977_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_denoteExpr_go(v_ctx_968_, v_r_969_, v_p_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
stack->m_obj
 = v_res_977_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_denoteExpr_go___boxed(lean_object* v_ctx_978_, lean_object* v_r_979_, lean_object* v_p_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_denoteExpr_go(v_ctx_978_, v_r_979_, v_p_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
return v_res_986_;
}
}
lean_object* l_Int_Internal_Linear_Poly_denoteExpr___redArg(lean_object* v_ctx_987_, lean_object* v_p_988_){
_start:
{
if (lean_obj_tag(v_p_988_) == 0)
{
lean_object* v_k_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1011_; 
lean_dec_ref(v_ctx_987_);
v_k_990_ = lean_ctor_get(v_p_988_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v_p_988_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_992_ = v_p_988_;
v_isShared_993_ = v_isSharedCheck_1011_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_k_990_);
lean_dec(v_p_988_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1011_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_994_; uint8_t v___x_995_; 
v___x_994_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
v___x_995_ = lean_int_dec_le(v___x_994_, v_k_990_);
if (v___x_995_ == 0)
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1004_; 
v___x_996_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12);
v___x_997_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14);
v___x_998_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17);
v___x_999_ = lean_int_neg(v_k_990_);
lean_dec(v_k_990_);
v___x_1000_ = l_Int_toNat(v___x_999_);
lean_dec(v___x_999_);
v___x_1001_ = l_Lean_instToExprInt_mkNat(v___x_1000_);
v___x_1002_ = l_Lean_mkApp3(v___x_996_, v___x_997_, v___x_998_, v___x_1001_);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 0, v___x_1002_);
v___x_1004_ = v___x_992_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v___x_1002_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
else
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1009_; 
v___x_1006_ = l_Int_toNat(v_k_990_);
lean_dec(v_k_990_);
v___x_1007_ = l_Lean_instToExprInt_mkNat(v___x_1006_);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 0, v___x_1007_);
v___x_1009_ = v___x_992_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1007_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
else
{
lean_object* v_k_1012_; lean_object* v_v_1013_; lean_object* v_p_1014_; lean_object* v___y_1016_; lean_object* v___x_1020_; uint8_t v___x_1021_; 
v_k_1012_ = lean_ctor_get(v_p_988_, 0);
lean_inc(v_k_1012_);
v_v_1013_ = lean_ctor_get(v_p_988_, 1);
lean_inc(v_v_1013_);
v_p_1014_ = lean_ctor_get(v_p_988_, 2);
lean_inc_ref(v_p_1014_);
lean_dec_ref_known(v_p_988_, 3);
v___x_1020_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0);
v___x_1021_ = lean_int_dec_eq(v_k_1012_, v___x_1020_);
if (v___x_1021_ == 0)
{
lean_object* v___x_1022_; uint8_t v___x_1023_; 
v___x_1022_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
v___x_1023_ = lean_int_dec_le(v___x_1022_, v_k_1012_);
if (v___x_1023_ == 0)
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1024_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12);
v___x_1025_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14);
v___x_1026_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17);
v___x_1027_ = lean_int_neg(v_k_1012_);
lean_dec(v_k_1012_);
v___x_1028_ = l_Int_toNat(v___x_1027_);
lean_dec(v___x_1027_);
v___x_1029_ = l_Lean_instToExprInt_mkNat(v___x_1028_);
v___x_1030_ = l_Lean_mkApp3(v___x_1024_, v___x_1025_, v___x_1026_, v___x_1029_);
v___y_1016_ = v___x_1030_;
goto v___jp_1015_;
}
else
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = l_Int_toNat(v_k_1012_);
lean_dec(v_k_1012_);
v___x_1032_ = l_Lean_instToExprInt_mkNat(v___x_1031_);
v___y_1016_ = v___x_1032_;
goto v___jp_1015_;
}
}
else
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
lean_dec(v_k_1012_);
lean_inc_ref(v_ctx_987_);
v___x_1033_ = lean_apply_1(v_ctx_987_, v_v_1013_);
v___x_1034_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_denoteExpr_go___redArg(v_ctx_987_, v___x_1033_, v_p_1014_);
return v___x_1034_;
}
v___jp_1015_:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
lean_inc_ref(v_ctx_987_);
v___x_1017_ = lean_apply_1(v_ctx_987_, v_v_1013_);
v___x_1018_ = l_Lean_mkIntMul(v___y_1016_, v___x_1017_);
v___x_1019_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_denoteExpr_go___redArg(v_ctx_987_, v___x_1018_, v_p_1014_);
return v___x_1019_;
}
}
}
}
LEAN_EXPORT void l_Int_Internal_Linear_Poly_denoteExpr___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_987_ = stack[0].m_obj;
lean_object* v_p_988_ = stack[1].m_obj;
lean_object* v_res_1035_;
v_res_1035_ = l_Int_Internal_Linear_Poly_denoteExpr___redArg(v_ctx_987_, v_p_988_);
stack->m_obj
 = v_res_1035_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr___redArg___boxed(lean_object* v_ctx_1036_, lean_object* v_p_1037_, lean_object* v_a_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l_Int_Internal_Linear_Poly_denoteExpr___redArg(v_ctx_1036_, v_p_1037_);
return v_res_1039_;
}
}
lean_object* l_Int_Internal_Linear_Poly_denoteExpr(lean_object* v_ctx_1040_, lean_object* v_p_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = l_Int_Internal_Linear_Poly_denoteExpr___redArg(v_ctx_1040_, v_p_1041_);
return v___x_1047_;
}
}
LEAN_EXPORT void l_Int_Internal_Linear_Poly_denoteExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_1040_ = stack[0].m_obj;
lean_object* v_p_1041_ = stack[1].m_obj;
lean_object* v_a_1042_ = stack[2].m_obj;
lean_object* v_a_1043_ = stack[3].m_obj;
lean_object* v_a_1044_ = stack[4].m_obj;
lean_object* v_a_1045_ = stack[5].m_obj;
lean_object* v_res_1048_;
v_res_1048_ = l_Int_Internal_Linear_Poly_denoteExpr(v_ctx_1040_, v_p_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_);
stack->m_obj
 = v_res_1048_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr___boxed(lean_object* v_ctx_1049_, lean_object* v_p_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Int_Internal_Linear_Poly_denoteExpr(v_ctx_1049_, v_p_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
lean_dec(v_a_1054_);
lean_dec_ref(v_a_1053_);
lean_dec(v_a_1052_);
lean_dec_ref(v_a_1051_);
return v_res_1056_;
}
}
lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(lean_object* v_e_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_){
_start:
{
lean_object* v___x_1064_; lean_object* v_varMap_1065_; lean_object* v___x_1066_; 
v___x_1064_ = lean_st_ref_get(v_a_1058_);
v_varMap_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc_ref(v_varMap_1065_);
lean_dec(v___x_1064_);
lean_inc_ref(v_e_1057_);
v___x_1066_ = l_Lean_Meta_KExprMap_find_x3f___redArg(v_varMap_1065_, v_e_1057_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_);
lean_dec_ref(v_varMap_1065_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1115_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1069_ = v___x_1066_;
v_isShared_1070_ = v_isSharedCheck_1115_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1066_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1115_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
if (lean_obj_tag(v_a_1067_) == 1)
{
lean_object* v_val_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1081_; 
lean_dec_ref(v_e_1057_);
v_val_1071_ = lean_ctor_get(v_a_1067_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_a_1067_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1073_ = v_a_1067_;
v_isShared_1074_ = v_isSharedCheck_1081_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_val_1071_);
lean_dec(v_a_1067_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1081_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1074_ == 0)
{
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_val_1071_);
v___x_1076_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
lean_object* v___x_1078_; 
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 0, v___x_1076_);
v___x_1078_ = v___x_1069_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1076_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
else
{
lean_object* v___x_1082_; lean_object* v_vars_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v_varMap_1086_; lean_object* v_vars_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1114_; 
lean_del_object(v___x_1069_);
lean_dec(v_a_1067_);
v___x_1082_ = lean_st_ref_get(v_a_1058_);
v_vars_1083_ = lean_ctor_get(v___x_1082_, 1);
lean_inc_ref(v_vars_1083_);
lean_dec(v___x_1082_);
v___x_1084_ = lean_array_get_size(v_vars_1083_);
lean_dec_ref(v_vars_1083_);
v___x_1085_ = lean_st_ref_get(v_a_1058_);
v_varMap_1086_ = lean_ctor_get(v___x_1085_, 0);
v_vars_1087_ = lean_ctor_get(v___x_1085_, 1);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1089_ = v___x_1085_;
v_isShared_1090_ = v_isSharedCheck_1114_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_vars_1087_);
lean_inc(v_varMap_1086_);
lean_dec(v___x_1085_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1114_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1091_; 
lean_inc_ref(v_e_1057_);
v___x_1091_ = l_Lean_Meta_KExprMap_insert___redArg(v_varMap_1086_, v_e_1057_, v___x_1084_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1105_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1094_ = v___x_1091_;
v_isShared_1095_ = v_isSharedCheck_1105_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1091_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1105_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1096_; lean_object* v___x_1098_; 
v___x_1096_ = lean_array_push(v_vars_1087_, v_e_1057_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 1, v___x_1096_);
lean_ctor_set(v___x_1089_, 0, v_a_1092_);
v___x_1098_ = v___x_1089_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1092_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v___x_1096_);
v___x_1098_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1102_; 
v___x_1099_ = lean_st_ref_swap(v_a_1058_, v___x_1098_);
lean_dec(v___x_1099_);
v___x_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1084_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 0, v___x_1100_);
v___x_1102_ = v___x_1094_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v___x_1100_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
else
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
lean_del_object(v___x_1089_);
lean_dec_ref(v_vars_1087_);
lean_dec_ref(v_e_1057_);
v_a_1106_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1091_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1091_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1106_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
lean_dec_ref(v_e_1057_);
v_a_1116_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1066_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1066_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1057_ = stack[0].m_obj;
lean_object* v_a_1058_ = stack[1].m_obj;
lean_object* v_a_1059_ = stack[2].m_obj;
lean_object* v_a_1060_ = stack[3].m_obj;
lean_object* v_a_1061_ = stack[4].m_obj;
lean_object* v_a_1062_ = stack[5].m_obj;
lean_object* v_res_1124_;
v_res_1124_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_);
stack->m_obj
 = v_res_1124_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar___boxed(lean_object* v_e_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
lean_dec(v_a_1128_);
lean_dec_ref(v_a_1127_);
lean_dec(v_a_1126_);
return v_res_1132_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit(lean_object* v_e_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_){
_start:
{
lean_object* v_a_1186_; lean_object* v_b_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1192_; lean_object* v___x_1236_; 
lean_inc_ref(v_e_1178_);
v___x_1236_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1178_, v_a_1181_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_a_1237_; lean_object* v___x_1238_; uint8_t v___x_1239_; 
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_a_1237_);
lean_dec_ref_known(v___x_1236_, 1);
v___x_1238_ = l_Lean_Expr_cleanupAnnotations(v_a_1237_);
v___x_1239_ = l_Lean_Expr_isApp(v___x_1238_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; 
lean_dec_ref(v___x_1238_);
v___x_1240_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
return v___x_1240_;
}
else
{
lean_object* v_arg_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; uint8_t v___x_1244_; 
v_arg_1241_ = lean_ctor_get(v___x_1238_, 1);
lean_inc_ref(v_arg_1241_);
v___x_1242_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1238_);
v___x_1243_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__0));
v___x_1244_ = l_Lean_Expr_isConstOf(v___x_1242_, v___x_1243_);
if (v___x_1244_ == 0)
{
uint8_t v___x_1245_; 
v___x_1245_ = l_Lean_Expr_isApp(v___x_1242_);
if (v___x_1245_ == 0)
{
lean_object* v___x_1246_; 
lean_dec_ref(v___x_1242_);
lean_dec_ref(v_arg_1241_);
v___x_1246_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
return v___x_1246_;
}
else
{
lean_object* v_arg_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; uint8_t v___x_1250_; 
v_arg_1247_ = lean_ctor_get(v___x_1242_, 1);
lean_inc_ref(v_arg_1247_);
v___x_1248_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1242_);
v___x_1249_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__2));
v___x_1250_ = l_Lean_Expr_isConstOf(v___x_1248_, v___x_1249_);
if (v___x_1250_ == 0)
{
lean_object* v___x_1251_; uint8_t v___x_1252_; 
v___x_1251_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__3));
v___x_1252_ = l_Lean_Expr_isConstOf(v___x_1248_, v___x_1251_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; uint8_t v___x_1254_; 
v___x_1253_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__4));
v___x_1254_ = l_Lean_Expr_isConstOf(v___x_1248_, v___x_1253_);
if (v___x_1254_ == 0)
{
uint8_t v___x_1255_; 
v___x_1255_ = l_Lean_Expr_isApp(v___x_1248_);
if (v___x_1255_ == 0)
{
lean_object* v___x_1256_; 
lean_dec_ref(v___x_1248_);
lean_dec_ref(v_arg_1247_);
lean_dec_ref(v_arg_1241_);
v___x_1256_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
return v___x_1256_;
}
else
{
lean_object* v_arg_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; uint8_t v___x_1260_; 
v_arg_1257_ = lean_ctor_get(v___x_1248_, 1);
lean_inc_ref(v_arg_1257_);
v___x_1258_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1248_);
v___x_1259_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__9));
v___x_1260_ = l_Lean_Expr_isConstOf(v___x_1258_, v___x_1259_);
if (v___x_1260_ == 0)
{
lean_object* v___x_1261_; uint8_t v___x_1262_; 
v___x_1261_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__7));
v___x_1262_ = l_Lean_Expr_isConstOf(v___x_1258_, v___x_1261_);
if (v___x_1262_ == 0)
{
uint8_t v___x_1263_; 
v___x_1263_ = l_Lean_Expr_isApp(v___x_1258_);
if (v___x_1263_ == 0)
{
lean_object* v___x_1264_; 
lean_dec_ref(v___x_1258_);
lean_dec_ref(v_arg_1257_);
lean_dec_ref(v_arg_1247_);
lean_dec_ref(v_arg_1241_);
v___x_1264_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
return v___x_1264_;
}
else
{
lean_object* v___x_1265_; lean_object* v___x_1266_; uint8_t v___x_1267_; 
v___x_1265_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1258_);
v___x_1266_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__9));
v___x_1267_ = l_Lean_Expr_isConstOf(v___x_1265_, v___x_1266_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; uint8_t v___x_1269_; 
v___x_1268_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__11));
v___x_1269_ = l_Lean_Expr_isConstOf(v___x_1265_, v___x_1268_);
if (v___x_1269_ == 0)
{
lean_object* v___x_1270_; uint8_t v___x_1271_; 
v___x_1270_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__13));
v___x_1271_ = l_Lean_Expr_isConstOf(v___x_1265_, v___x_1270_);
if (v___x_1271_ == 0)
{
uint8_t v___x_1272_; 
v___x_1272_ = l_Lean_Expr_isApp(v___x_1265_);
if (v___x_1272_ == 0)
{
lean_object* v___x_1273_; 
lean_dec_ref(v___x_1265_);
lean_dec_ref(v_arg_1257_);
lean_dec_ref(v_arg_1247_);
lean_dec_ref(v_arg_1241_);
v___x_1273_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
return v___x_1273_;
}
else
{
lean_object* v___x_1274_; uint8_t v___x_1275_; 
v___x_1274_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1265_);
v___x_1275_ = l_Lean_Expr_isApp(v___x_1274_);
if (v___x_1275_ == 0)
{
lean_object* v___x_1276_; 
lean_dec_ref(v___x_1274_);
lean_dec_ref(v_arg_1257_);
lean_dec_ref(v_arg_1247_);
lean_dec_ref(v_arg_1241_);
v___x_1276_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
return v___x_1276_;
}
else
{
lean_object* v___x_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; 
v___x_1277_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1274_);
v___x_1278_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__16));
v___x_1279_ = l_Lean_Expr_isConstOf(v___x_1277_, v___x_1278_);
if (v___x_1279_ == 0)
{
lean_object* v___x_1280_; uint8_t v___x_1281_; 
v___x_1280_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__19));
v___x_1281_ = l_Lean_Expr_isConstOf(v___x_1277_, v___x_1280_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; uint8_t v___x_1283_; 
v___x_1282_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__22));
v___x_1283_ = l_Lean_Expr_isConstOf(v___x_1277_, v___x_1282_);
lean_dec_ref(v___x_1277_);
if (v___x_1283_ == 0)
{
lean_object* v___x_1284_; 
lean_dec_ref(v_arg_1257_);
lean_dec_ref(v_arg_1247_);
lean_dec_ref(v_arg_1241_);
v___x_1284_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
return v___x_1284_;
}
else
{
lean_object* v___x_1285_; 
v___x_1285_ = l_Lean_Meta_DefEq_isInstHAddInt(v_arg_1257_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v_a_1286_; uint8_t v___x_1287_; 
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_a_1286_);
lean_dec_ref_known(v___x_1285_, 1);
v___x_1287_ = lean_unbox(v_a_1286_);
lean_dec(v_a_1286_);
if (v___x_1287_ == 0)
{
lean_object* v___x_1288_; 
lean_dec_ref(v_arg_1247_);
lean_dec_ref(v_arg_1241_);
v___x_1288_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
return v___x_1288_;
}
else
{
lean_object* v___x_1289_; 
lean_dec_ref(v_e_1178_);
v___x_1289_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1247_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_object* v_a_1290_; lean_object* v___x_1291_; 
v_a_1290_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_a_1290_);
lean_dec_ref_known(v___x_1289_, 1);
v___x_1291_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1241_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1300_; 
v_a_1292_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1294_ = v___x_1291_;
v_isShared_1295_ = v_isSharedCheck_1300_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1291_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1300_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1296_; lean_object* v___x_1298_; 
v___x_1296_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1296_, 0, v_a_1290_);
lean_ctor_set(v___x_1296_, 1, v_a_1292_);
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 0, v___x_1296_);
v___x_1298_ = v___x_1294_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v___x_1296_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
else
{
lean_dec(v_a_1290_);
return v___x_1291_;
}
}
else
{
lean_dec_ref(v_arg_1241_);
return v___x_1289_;
}
}
}
else
{
lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1308_; 
lean_dec_ref(v_arg_1247_);
lean_dec_ref(v_arg_1241_);
lean_dec_ref(v_e_1178_);
v_a_1301_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1303_ = v___x_1285_;
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_dec(v___x_1285_);
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
}
else
{
lean_object* v___x_1309_; 
lean_dec_ref(v___x_1277_);
v___x_1309_ = l_Lean_Meta_DefEq_isInstHSubInt(v_arg_1257_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v_a_1310_; uint8_t v___x_1311_; 
v_a_1310_ = lean_ctor_get(v___x_1309_, 0);
lean_inc(v_a_1310_);
lean_dec_ref_known(v___x_1309_, 1);
v___x_1311_ = lean_unbox(v_a_1310_);
lean_dec(v_a_1310_);
if (v___x_1311_ == 0)
{
lean_object* v___x_1312_; 
lean_dec_ref(v_arg_1247_);
lean_dec_ref(v_arg_1241_);
v___x_1312_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
return v___x_1312_;
}
else
{
lean_object* v___x_1313_; 
lean_dec_ref(v_e_1178_);
v___x_1313_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1247_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v_a_1314_; lean_object* v___x_1315_; 
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_a_1314_);
lean_dec_ref_known(v___x_1313_, 1);
v___x_1315_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1241_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1324_; 
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1318_ = v___x_1315_;
v_isShared_1319_ = v_isSharedCheck_1324_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1315_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1324_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1320_; lean_object* v___x_1322_; 
v___x_1320_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1320_, 0, v_a_1314_);
lean_ctor_set(v___x_1320_, 1, v_a_1316_);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 0, v___x_1320_);
v___x_1322_ = v___x_1318_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1320_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
else
{
lean_dec(v_a_1314_);
return v___x_1315_;
}
}
else
{
lean_dec_ref(v_arg_1241_);
return v___x_1313_;
}
}
}
else
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
lean_dec_ref(v_arg_1247_);
lean_dec_ref(v_arg_1241_);
lean_dec_ref(v_e_1178_);
v_a_1325_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1309_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1309_);
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
lean_object* v___x_1333_; 
lean_dec_ref(v___x_1277_);
v___x_1333_ = l_Lean_Meta_DefEq_isInstHMulInt(v_arg_1257_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v_a_1334_; uint8_t v___x_1335_; 
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
lean_inc(v_a_1334_);
lean_dec_ref_known(v___x_1333_, 1);
v___x_1335_ = lean_unbox(v_a_1334_);
lean_dec(v_a_1334_);
if (v___x_1335_ == 0)
{
lean_object* v___x_1336_; 
lean_dec_ref(v_arg_1247_);
lean_dec_ref(v_arg_1241_);
v___x_1336_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
return v___x_1336_;
}
else
{
v_a_1186_ = v_arg_1247_;
v_b_1187_ = v_arg_1241_;
v___y_1188_ = v_a_1179_;
v___y_1189_ = v_a_1180_;
v___y_1190_ = v_a_1181_;
v___y_1191_ = v_a_1182_;
v___y_1192_ = v_a_1183_;
goto v___jp_1185_;
}
}
else
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1344_; 
lean_dec_ref(v_arg_1247_);
lean_dec_ref(v_arg_1241_);
lean_dec_ref(v_e_1178_);
v_a_1337_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1339_ = v___x_1333_;
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1333_);
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
}
else
{
lean_object* v___x_1345_; 
lean_dec_ref(v___x_1265_);
v___x_1345_ = l_Lean_Meta_DefEq_isInstAddInt(v_arg_1257_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; uint8_t v___x_1347_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_a_1346_);
lean_dec_ref_known(v___x_1345_, 1);
v___x_1347_ = lean_unbox(v_a_1346_);
lean_dec(v_a_1346_);
if (v___x_1347_ == 0)
{
lean_object* v___x_1348_; 
lean_dec_ref(v_arg_1247_);
lean_dec_ref(v_arg_1241_);
v___x_1348_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
return v___x_1348_;
}
else
{
lean_object* v___x_1349_; 
lean_dec_ref(v_e_1178_);
v___x_1349_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1247_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; lean_object* v___x_1351_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_a_1350_);
lean_dec_ref_known(v___x_1349_, 1);
v___x_1351_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1241_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1360_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1354_ = v___x_1351_;
v_isShared_1355_ = v_isSharedCheck_1360_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1351_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1360_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1356_; lean_object* v___x_1358_; 
v___x_1356_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1356_, 0, v_a_1350_);
lean_ctor_set(v___x_1356_, 1, v_a_1352_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 0, v___x_1356_);
v___x_1358_ = v___x_1354_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
else
{
lean_dec(v_a_1350_);
return v___x_1351_;
}
}
else
{
lean_dec_ref(v_arg_1241_);
return v___x_1349_;
}
}
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
lean_dec_ref(v_arg_1247_);
lean_dec_ref(v_arg_1241_);
lean_dec_ref(v_e_1178_);
v_a_1361_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1345_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1345_);
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
else
{
lean_object* v___x_1369_; 
lean_dec_ref(v___x_1265_);
v___x_1369_ = l_Lean_Meta_DefEq_isInstSubInt(v_arg_1257_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_a_1370_; uint8_t v___x_1371_; 
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_a_1370_);
lean_dec_ref_known(v___x_1369_, 1);
v___x_1371_ = lean_unbox(v_a_1370_);
lean_dec(v_a_1370_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; 
lean_dec_ref(v_arg_1247_);
lean_dec_ref(v_arg_1241_);
v___x_1372_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
return v___x_1372_;
}
else
{
lean_object* v___x_1373_; 
lean_dec_ref(v_e_1178_);
v___x_1373_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1247_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v_a_1374_; lean_object* v___x_1375_; 
v_a_1374_ = lean_ctor_get(v___x_1373_, 0);
lean_inc(v_a_1374_);
lean_dec_ref_known(v___x_1373_, 1);
v___x_1375_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1241_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1384_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1378_ = v___x_1375_;
v_isShared_1379_ = v_isSharedCheck_1384_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1375_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1384_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1380_; lean_object* v___x_1382_; 
v___x_1380_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1380_, 0, v_a_1374_);
lean_ctor_set(v___x_1380_, 1, v_a_1376_);
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 0, v___x_1380_);
v___x_1382_ = v___x_1378_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1380_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
else
{
lean_dec(v_a_1374_);
return v___x_1375_;
}
}
else
{
lean_dec_ref(v_arg_1241_);
return v___x_1373_;
}
}
}
else
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1392_; 
lean_dec_ref(v_arg_1247_);
lean_dec_ref(v_arg_1241_);
lean_dec_ref(v_e_1178_);
v_a_1385_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1387_ = v___x_1369_;
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1369_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; 
if (v_isShared_1388_ == 0)
{
v___x_1390_ = v___x_1387_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_a_1385_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
}
}
else
{
lean_object* v___x_1393_; 
lean_dec_ref(v___x_1265_);
v___x_1393_ = l_Lean_Meta_DefEq_isInstMulInt(v_arg_1257_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_a_1394_; uint8_t v___x_1395_; 
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_a_1394_);
lean_dec_ref_known(v___x_1393_, 1);
v___x_1395_ = lean_unbox(v_a_1394_);
lean_dec(v_a_1394_);
if (v___x_1395_ == 0)
{
lean_object* v___x_1396_; 
lean_dec_ref(v_arg_1247_);
lean_dec_ref(v_arg_1241_);
v___x_1396_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
return v___x_1396_;
}
else
{
v_a_1186_ = v_arg_1247_;
v_b_1187_ = v_arg_1241_;
v___y_1188_ = v_a_1179_;
v___y_1189_ = v_a_1180_;
v___y_1190_ = v_a_1181_;
v___y_1191_ = v_a_1182_;
v___y_1192_ = v_a_1183_;
goto v___jp_1185_;
}
}
else
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1404_; 
lean_dec_ref(v_arg_1247_);
lean_dec_ref(v_arg_1241_);
lean_dec_ref(v_e_1178_);
v_a_1397_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1399_ = v___x_1393_;
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1393_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1397_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
}
}
else
{
lean_object* v___x_1405_; 
lean_dec_ref(v___x_1258_);
lean_dec_ref(v_arg_1257_);
lean_dec_ref(v_arg_1247_);
lean_dec_ref(v_arg_1241_);
lean_inc_ref(v_e_1178_);
v___x_1405_ = l_Lean_Meta_getIntValue_x3f(v_e_1178_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1422_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1408_ = v___x_1405_;
v_isShared_1409_ = v_isSharedCheck_1422_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1405_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1422_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
if (lean_obj_tag(v_a_1406_) == 1)
{
lean_object* v_val_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1420_; 
lean_dec_ref(v_e_1178_);
v_val_1410_ = lean_ctor_get(v_a_1406_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v_a_1406_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1412_ = v_a_1406_;
v_isShared_1413_ = v_isSharedCheck_1420_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_val_1410_);
lean_dec(v_a_1406_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1420_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1415_; 
if (v_isShared_1413_ == 0)
{
lean_ctor_set_tag(v___x_1412_, 0);
v___x_1415_ = v___x_1412_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_val_1410_);
v___x_1415_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
lean_object* v___x_1417_; 
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v___x_1415_);
v___x_1417_ = v___x_1408_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1415_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
else
{
lean_object* v___x_1421_; 
lean_del_object(v___x_1408_);
lean_dec(v_a_1406_);
v___x_1421_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
return v___x_1421_;
}
}
}
else
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1430_; 
lean_dec_ref(v_e_1178_);
v_a_1423_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1425_ = v___x_1405_;
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1405_);
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
else
{
lean_object* v___x_1431_; 
lean_dec_ref(v___x_1258_);
lean_dec_ref(v_arg_1257_);
v___x_1431_ = l_Lean_Meta_DefEq_isInstNegInt(v_arg_1247_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; uint8_t v___x_1433_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
lean_inc(v_a_1432_);
lean_dec_ref_known(v___x_1431_, 1);
v___x_1433_ = lean_unbox(v_a_1432_);
lean_dec(v_a_1432_);
if (v___x_1433_ == 0)
{
lean_object* v___x_1434_; 
lean_dec_ref(v_arg_1241_);
v___x_1434_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
return v___x_1434_;
}
else
{
lean_object* v___x_1435_; 
lean_dec_ref(v_e_1178_);
v___x_1435_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1241_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
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
v___x_1440_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1440_, 0, v_a_1436_);
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
return v___x_1435_;
}
}
}
else
{
lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1452_; 
lean_dec_ref(v_arg_1241_);
lean_dec_ref(v_e_1178_);
v_a_1445_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1447_ = v___x_1431_;
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_dec(v___x_1431_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1450_; 
if (v_isShared_1448_ == 0)
{
v___x_1450_ = v___x_1447_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_a_1445_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
}
}
else
{
lean_object* v___x_1453_; 
lean_dec_ref(v___x_1248_);
lean_dec_ref(v_e_1178_);
v___x_1453_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1247_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v_a_1454_; lean_object* v___x_1455_; 
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
lean_inc(v_a_1454_);
lean_dec_ref_known(v___x_1453_, 1);
v___x_1455_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1241_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1464_; 
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1458_ = v___x_1455_;
v_isShared_1459_ = v_isSharedCheck_1464_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1455_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1464_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1460_; lean_object* v___x_1462_; 
v___x_1460_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1460_, 0, v_a_1454_);
lean_ctor_set(v___x_1460_, 1, v_a_1456_);
if (v_isShared_1459_ == 0)
{
lean_ctor_set(v___x_1458_, 0, v___x_1460_);
v___x_1462_ = v___x_1458_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1460_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
else
{
lean_dec(v_a_1454_);
return v___x_1455_;
}
}
else
{
lean_dec_ref(v_arg_1241_);
return v___x_1453_;
}
}
}
else
{
lean_object* v___x_1465_; 
lean_dec_ref(v___x_1248_);
lean_dec_ref(v_e_1178_);
v___x_1465_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1247_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_a_1466_; lean_object* v___x_1467_; 
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
lean_inc(v_a_1466_);
lean_dec_ref_known(v___x_1465_, 1);
v___x_1467_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1241_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1476_; 
v_a_1468_ = lean_ctor_get(v___x_1467_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1470_ = v___x_1467_;
v_isShared_1471_ = v_isSharedCheck_1476_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1467_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1476_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1472_; lean_object* v___x_1474_; 
v___x_1472_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1472_, 0, v_a_1466_);
lean_ctor_set(v___x_1472_, 1, v_a_1468_);
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 0, v___x_1472_);
v___x_1474_ = v___x_1470_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1472_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
else
{
lean_dec(v_a_1466_);
return v___x_1467_;
}
}
else
{
lean_dec_ref(v_arg_1241_);
return v___x_1465_;
}
}
}
else
{
lean_dec_ref(v___x_1248_);
v_a_1186_ = v_arg_1247_;
v_b_1187_ = v_arg_1241_;
v___y_1188_ = v_a_1179_;
v___y_1189_ = v_a_1180_;
v___y_1190_ = v_a_1181_;
v___y_1191_ = v_a_1182_;
v___y_1192_ = v_a_1183_;
goto v___jp_1185_;
}
}
}
else
{
lean_object* v___x_1477_; 
lean_dec_ref(v___x_1242_);
lean_dec_ref(v_e_1178_);
v___x_1477_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1241_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1486_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1480_ = v___x_1477_;
v_isShared_1481_ = v_isSharedCheck_1486_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1477_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1486_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1482_; lean_object* v___x_1484_; 
v___x_1482_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1482_, 0, v_a_1478_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 0, v___x_1482_);
v___x_1484_ = v___x_1480_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1482_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
else
{
return v___x_1477_;
}
}
}
}
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
lean_dec_ref(v_e_1178_);
v_a_1487_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1236_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1236_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
v___jp_1185_:
{
lean_object* v___x_1193_; 
lean_inc_ref(v_a_1186_);
v___x_1193_ = l_Lean_Meta_getIntValue_x3f(v_a_1186_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v_a_1194_; 
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
lean_inc(v_a_1194_);
lean_dec_ref_known(v___x_1193_, 1);
if (lean_obj_tag(v_a_1194_) == 0)
{
lean_object* v___x_1195_; 
v___x_1195_ = l_Lean_Meta_getIntValue_x3f(v_b_1187_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_object* v_a_1196_; 
v_a_1196_ = lean_ctor_get(v___x_1195_, 0);
lean_inc(v_a_1196_);
lean_dec_ref_known(v___x_1195_, 1);
if (lean_obj_tag(v_a_1196_) == 0)
{
lean_object* v___x_1197_; 
lean_dec_ref(v_a_1186_);
v___x_1197_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1178_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
return v___x_1197_;
}
else
{
lean_object* v_val_1198_; lean_object* v___x_1199_; 
lean_dec_ref(v_e_1178_);
v_val_1198_ = lean_ctor_get(v_a_1196_, 0);
lean_inc(v_val_1198_);
lean_dec_ref_known(v_a_1196_, 1);
v___x_1199_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_a_1186_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
if (lean_obj_tag(v___x_1199_) == 0)
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1208_; 
v_a_1200_ = lean_ctor_get(v___x_1199_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1202_ = v___x_1199_;
v_isShared_1203_ = v_isSharedCheck_1208_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1199_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1208_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1204_; lean_object* v___x_1206_; 
v___x_1204_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1204_, 0, v_a_1200_);
lean_ctor_set(v___x_1204_, 1, v_val_1198_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 0, v___x_1204_);
v___x_1206_ = v___x_1202_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1204_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
else
{
lean_dec(v_val_1198_);
return v___x_1199_;
}
}
}
else
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
lean_dec_ref(v_a_1186_);
lean_dec_ref(v_e_1178_);
v_a_1209_ = lean_ctor_get(v___x_1195_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1195_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1195_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
else
{
lean_object* v_val_1217_; lean_object* v___x_1218_; 
lean_dec_ref(v_a_1186_);
lean_dec_ref(v_e_1178_);
v_val_1217_ = lean_ctor_get(v_a_1194_, 0);
lean_inc(v_val_1217_);
lean_dec_ref_known(v_a_1194_, 1);
v___x_1218_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_b_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1227_; 
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1221_ = v___x_1218_;
v_isShared_1222_ = v_isSharedCheck_1227_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1218_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1227_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1223_; lean_object* v___x_1225_; 
v___x_1223_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1223_, 0, v_val_1217_);
lean_ctor_set(v___x_1223_, 1, v_a_1219_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 0, v___x_1223_);
v___x_1225_ = v___x_1221_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1223_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
else
{
lean_dec(v_val_1217_);
return v___x_1218_;
}
}
}
else
{
lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
lean_dec_ref(v_b_1187_);
lean_dec_ref(v_a_1186_);
lean_dec_ref(v_e_1178_);
v_a_1228_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1230_ = v___x_1193_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v___x_1193_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1228_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1178_ = stack[0].m_obj;
lean_object* v_a_1179_ = stack[1].m_obj;
lean_object* v_a_1180_ = stack[2].m_obj;
lean_object* v_a_1181_ = stack[3].m_obj;
lean_object* v_a_1182_ = stack[4].m_obj;
lean_object* v_a_1183_ = stack[5].m_obj;
lean_object* v_res_1495_;
v_res_1495_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit(v_e_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
stack->m_obj
 = v_res_1495_;
}
lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(lean_object* v_e_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_){
_start:
{
switch(lean_obj_tag(v_e_1496_))
{
case 10:
{
lean_object* v_expr_1503_; 
v_expr_1503_ = lean_ctor_get(v_e_1496_, 1);
lean_inc_ref(v_expr_1503_);
lean_dec_ref_known(v_e_1496_, 2);
v_e_1496_ = v_expr_1503_;
goto _start;
}
case 5:
{
lean_object* v___x_1505_; 
v___x_1505_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit(v_e_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_);
return v___x_1505_;
}
case 2:
{
lean_object* v___x_1506_; 
v___x_1506_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit(v_e_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_);
return v___x_1506_;
}
default: 
{
lean_object* v___x_1507_; 
v___x_1507_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_);
return v___x_1507_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1496_ = stack[0].m_obj;
lean_object* v_a_1497_ = stack[1].m_obj;
lean_object* v_a_1498_ = stack[2].m_obj;
lean_object* v_a_1499_ = stack[3].m_obj;
lean_object* v_a_1500_ = stack[4].m_obj;
lean_object* v_a_1501_ = stack[5].m_obj;
lean_object* v_res_1508_;
v_res_1508_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_e_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_);
stack->m_obj
 = v_res_1508_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr___boxed(lean_object* v_e_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_e_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
lean_dec(v_a_1514_);
lean_dec_ref(v_a_1513_);
lean_dec(v_a_1512_);
lean_dec_ref(v_a_1511_);
lean_dec(v_a_1510_);
return v_res_1516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___boxed(lean_object* v_e_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit(v_e_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_);
lean_dec(v_a_1522_);
lean_dec_ref(v_a_1521_);
lean_dec(v_a_1520_);
lean_dec_ref(v_a_1519_);
lean_dec(v_a_1518_);
return v_res_1524_;
}
}
lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f(lean_object* v_e_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_){
_start:
{
lean_object* v___x_1538_; 
v___x_1538_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1528_, v_a_1531_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v_a_1539_; lean_object* v___x_1540_; uint8_t v___x_1541_; 
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
lean_inc(v_a_1539_);
lean_dec_ref_known(v___x_1538_, 1);
v___x_1540_ = l_Lean_Expr_cleanupAnnotations(v_a_1539_);
v___x_1541_ = l_Lean_Expr_isApp(v___x_1540_);
if (v___x_1541_ == 0)
{
lean_dec_ref(v___x_1540_);
goto v___jp_1535_;
}
else
{
lean_object* v_arg_1542_; lean_object* v___x_1543_; uint8_t v___x_1544_; 
v_arg_1542_ = lean_ctor_get(v___x_1540_, 1);
lean_inc_ref(v_arg_1542_);
v___x_1543_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1540_);
v___x_1544_ = l_Lean_Expr_isApp(v___x_1543_);
if (v___x_1544_ == 0)
{
lean_dec_ref(v___x_1543_);
lean_dec_ref(v_arg_1542_);
goto v___jp_1535_;
}
else
{
lean_object* v_arg_1545_; lean_object* v___x_1546_; uint8_t v___x_1547_; 
v_arg_1545_ = lean_ctor_get(v___x_1543_, 1);
lean_inc_ref(v_arg_1545_);
v___x_1546_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1543_);
v___x_1547_ = l_Lean_Expr_isApp(v___x_1546_);
if (v___x_1547_ == 0)
{
lean_dec_ref(v___x_1546_);
lean_dec_ref(v_arg_1545_);
lean_dec_ref(v_arg_1542_);
goto v___jp_1535_;
}
else
{
lean_object* v_arg_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; uint8_t v___x_1551_; 
v_arg_1548_ = lean_ctor_get(v___x_1546_, 1);
lean_inc_ref(v_arg_1548_);
v___x_1549_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1546_);
v___x_1550_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___closed__1));
v___x_1551_ = l_Lean_Expr_isConstOf(v___x_1549_, v___x_1550_);
lean_dec_ref(v___x_1549_);
if (v___x_1551_ == 0)
{
lean_dec_ref(v_arg_1548_);
lean_dec_ref(v_arg_1545_);
lean_dec_ref(v_arg_1542_);
goto v___jp_1535_;
}
else
{
lean_object* v___x_1552_; 
v___x_1552_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1548_, v_a_1531_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1610_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1555_ = v___x_1552_;
v_isShared_1556_ = v_isSharedCheck_1610_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1552_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1610_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; uint8_t v___x_1559_; 
v___x_1557_ = l_Lean_Expr_cleanupAnnotations(v_a_1553_);
v___x_1558_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13));
v___x_1559_ = l_Lean_Expr_isConstOf(v___x_1557_, v___x_1558_);
lean_dec_ref(v___x_1557_);
if (v___x_1559_ == 0)
{
lean_object* v___x_1560_; lean_object* v___x_1562_; 
lean_dec_ref(v_arg_1545_);
lean_dec_ref(v_arg_1542_);
v___x_1560_ = lean_box(0);
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v___x_1560_);
v___x_1562_ = v___x_1555_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v___x_1560_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
else
{
lean_object* v___x_1564_; 
lean_del_object(v___x_1555_);
v___x_1564_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1545_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1601_; 
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1567_ = v___x_1564_;
v_isShared_1568_ = v_isSharedCheck_1601_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1564_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1601_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1569_; 
v___x_1569_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1542_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1592_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1572_ = v___x_1569_;
v_isShared_1573_ = v_isSharedCheck_1592_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1569_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1592_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
switch(lean_obj_tag(v_a_1565_))
{
case 1:
{
switch(lean_obj_tag(v_a_1570_))
{
case 1:
{
lean_object* v___x_1580_; lean_object* v___x_1582_; 
lean_dec_ref_known(v_a_1570_, 1);
lean_dec_ref_known(v_a_1565_, 1);
lean_del_object(v___x_1572_);
v___x_1580_ = lean_box(0);
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 0, v___x_1580_);
v___x_1582_ = v___x_1567_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1580_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
case 0:
{
lean_object* v___x_1584_; lean_object* v___x_1586_; 
lean_dec_ref_known(v_a_1570_, 1);
lean_dec_ref_known(v_a_1565_, 1);
lean_del_object(v___x_1572_);
v___x_1584_ = lean_box(0);
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 0, v___x_1584_);
v___x_1586_ = v___x_1567_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1584_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
default: 
{
lean_del_object(v___x_1567_);
goto v___jp_1574_;
}
}
}
case 0:
{
if (lean_obj_tag(v_a_1570_) == 1)
{
lean_object* v___x_1588_; lean_object* v___x_1590_; 
lean_dec_ref_known(v_a_1570_, 1);
lean_dec_ref_known(v_a_1565_, 1);
lean_del_object(v___x_1572_);
v___x_1588_ = lean_box(0);
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 0, v___x_1588_);
v___x_1590_ = v___x_1567_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1588_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
else
{
lean_del_object(v___x_1567_);
goto v___jp_1574_;
}
}
default: 
{
lean_del_object(v___x_1567_);
goto v___jp_1574_;
}
}
v___jp_1574_:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1578_; 
v___x_1575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1575_, 0, v_a_1565_);
lean_ctor_set(v___x_1575_, 1, v_a_1570_);
v___x_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
if (v_isShared_1573_ == 0)
{
lean_ctor_set(v___x_1572_, 0, v___x_1576_);
v___x_1578_ = v___x_1572_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1576_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
else
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
lean_del_object(v___x_1567_);
lean_dec(v_a_1565_);
v_a_1593_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1569_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1569_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
lean_dec_ref(v_arg_1542_);
v_a_1602_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1564_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1564_);
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
}
else
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
lean_dec_ref(v_arg_1545_);
lean_dec_ref(v_arg_1542_);
v_a_1611_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1552_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1552_);
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
}
}
}
else
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
v_a_1619_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1538_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1538_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
v___jp_1535_:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1536_ = lean_box(0);
v___x_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1536_);
return v___x_1537_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1528_ = stack[0].m_obj;
lean_object* v_a_1529_ = stack[1].m_obj;
lean_object* v_a_1530_ = stack[2].m_obj;
lean_object* v_a_1531_ = stack[3].m_obj;
lean_object* v_a_1532_ = stack[4].m_obj;
lean_object* v_a_1533_ = stack[5].m_obj;
lean_object* v_res_1627_;
v_res_1627_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f(v_e_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_);
stack->m_obj
 = v_res_1627_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___boxed(lean_object* v_e_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f(v_e_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_);
lean_dec(v_a_1633_);
lean_dec_ref(v_a_1632_);
lean_dec(v_a_1631_);
lean_dec_ref(v_a_1630_);
lean_dec(v_a_1629_);
return v_res_1635_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14(void){
_start:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1662_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0);
v___x_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1662_);
return v___x_1663_;
}
}
lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f(lean_object* v_e_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1664_, v_a_1667_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_object* v_a_1675_; lean_object* v___x_1676_; uint8_t v___x_1677_; 
v_a_1675_ = lean_ctor_get(v___x_1674_, 0);
lean_inc(v_a_1675_);
lean_dec_ref_known(v___x_1674_, 1);
v___x_1676_ = l_Lean_Expr_cleanupAnnotations(v_a_1675_);
v___x_1677_ = l_Lean_Expr_isApp(v___x_1676_);
if (v___x_1677_ == 0)
{
lean_dec_ref(v___x_1676_);
goto v___jp_1671_;
}
else
{
lean_object* v_arg_1678_; lean_object* v___x_1679_; uint8_t v___x_1680_; 
v_arg_1678_ = lean_ctor_get(v___x_1676_, 1);
lean_inc_ref(v_arg_1678_);
v___x_1679_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1676_);
v___x_1680_ = l_Lean_Expr_isApp(v___x_1679_);
if (v___x_1680_ == 0)
{
lean_dec_ref(v___x_1679_);
lean_dec_ref(v_arg_1678_);
goto v___jp_1671_;
}
else
{
lean_object* v_arg_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; uint8_t v___x_1684_; 
v_arg_1681_ = lean_ctor_get(v___x_1679_, 1);
lean_inc_ref(v_arg_1681_);
v___x_1682_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1679_);
v___x_1683_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__1));
v___x_1684_ = l_Lean_Expr_isConstOf(v___x_1682_, v___x_1683_);
if (v___x_1684_ == 0)
{
lean_object* v___x_1685_; uint8_t v___x_1686_; 
v___x_1685_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__3));
v___x_1686_ = l_Lean_Expr_isConstOf(v___x_1682_, v___x_1685_);
if (v___x_1686_ == 0)
{
uint8_t v___x_1687_; 
v___x_1687_ = l_Lean_Expr_isApp(v___x_1682_);
if (v___x_1687_ == 0)
{
lean_dec_ref(v___x_1682_);
lean_dec_ref(v_arg_1681_);
lean_dec_ref(v_arg_1678_);
goto v___jp_1671_;
}
else
{
lean_object* v_arg_1688_; lean_object* v___x_1689_; uint8_t v___x_1690_; 
v_arg_1688_ = lean_ctor_get(v___x_1682_, 1);
lean_inc_ref(v_arg_1688_);
v___x_1689_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1682_);
v___x_1690_ = l_Lean_Expr_isApp(v___x_1689_);
if (v___x_1690_ == 0)
{
lean_dec_ref(v___x_1689_);
lean_dec_ref(v_arg_1688_);
lean_dec_ref(v_arg_1681_);
lean_dec_ref(v_arg_1678_);
goto v___jp_1671_;
}
else
{
lean_object* v___x_1691_; lean_object* v___x_1692_; uint8_t v___x_1693_; 
v___x_1691_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1689_);
v___x_1692_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__6));
v___x_1693_ = l_Lean_Expr_isConstOf(v___x_1691_, v___x_1692_);
if (v___x_1693_ == 0)
{
lean_object* v___x_1694_; uint8_t v___x_1695_; 
v___x_1694_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__9));
v___x_1695_ = l_Lean_Expr_isConstOf(v___x_1691_, v___x_1694_);
if (v___x_1695_ == 0)
{
lean_object* v___x_1696_; uint8_t v___x_1697_; 
v___x_1696_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__11));
v___x_1697_ = l_Lean_Expr_isConstOf(v___x_1691_, v___x_1696_);
if (v___x_1697_ == 0)
{
lean_object* v___x_1698_; uint8_t v___x_1699_; 
v___x_1698_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__13));
v___x_1699_ = l_Lean_Expr_isConstOf(v___x_1691_, v___x_1698_);
lean_dec_ref(v___x_1691_);
if (v___x_1699_ == 0)
{
lean_dec_ref(v_arg_1688_);
lean_dec_ref(v_arg_1681_);
lean_dec_ref(v_arg_1678_);
goto v___jp_1671_;
}
else
{
lean_object* v___x_1700_; 
v___x_1700_ = l_Lean_Meta_DefEq_isInstLEInt(v_arg_1688_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1739_; 
v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1703_ = v___x_1700_;
v_isShared_1704_ = v_isSharedCheck_1739_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1700_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1739_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
uint8_t v___x_1705_; 
v___x_1705_ = lean_unbox(v_a_1701_);
lean_dec(v_a_1701_);
if (v___x_1705_ == 0)
{
lean_object* v___x_1706_; lean_object* v___x_1708_; 
lean_dec_ref(v_arg_1681_);
lean_dec_ref(v_arg_1678_);
v___x_1706_ = lean_box(0);
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
else
{
lean_object* v___x_1710_; 
lean_del_object(v___x_1703_);
v___x_1710_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1681_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v_a_1711_; lean_object* v___x_1712_; 
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
lean_inc(v_a_1711_);
lean_dec_ref_known(v___x_1710_, 1);
v___x_1712_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1678_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1722_; 
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1715_ = v___x_1712_;
v_isShared_1716_ = v_isSharedCheck_1722_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1712_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1722_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1720_; 
v___x_1717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1717_, 0, v_a_1711_);
lean_ctor_set(v___x_1717_, 1, v_a_1713_);
v___x_1718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1717_);
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 0, v___x_1718_);
v___x_1720_ = v___x_1715_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v___x_1718_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
else
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1730_; 
lean_dec(v_a_1711_);
v_a_1723_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1725_ = v___x_1712_;
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1712_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1728_; 
if (v_isShared_1726_ == 0)
{
v___x_1728_ = v___x_1725_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_a_1723_);
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
lean_dec_ref(v_arg_1678_);
v_a_1731_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1733_ = v___x_1710_;
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1710_);
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
}
else
{
lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1747_; 
lean_dec_ref(v_arg_1681_);
lean_dec_ref(v_arg_1678_);
v_a_1740_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1742_ = v___x_1700_;
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v___x_1700_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1745_; 
if (v_isShared_1743_ == 0)
{
v___x_1745_ = v___x_1742_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1740_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
}
}
else
{
lean_object* v___x_1748_; 
lean_dec_ref(v___x_1691_);
v___x_1748_ = l_Lean_Meta_DefEq_isInstLTInt(v_arg_1688_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1789_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1751_ = v___x_1748_;
v_isShared_1752_ = v_isSharedCheck_1789_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___x_1748_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1789_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
uint8_t v___x_1753_; 
v___x_1753_ = lean_unbox(v_a_1749_);
lean_dec(v_a_1749_);
if (v___x_1753_ == 0)
{
lean_object* v___x_1754_; lean_object* v___x_1756_; 
lean_dec_ref(v_arg_1681_);
lean_dec_ref(v_arg_1678_);
v___x_1754_ = lean_box(0);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 0, v___x_1754_);
v___x_1756_ = v___x_1751_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v___x_1754_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
else
{
lean_object* v___x_1758_; 
lean_del_object(v___x_1751_);
v___x_1758_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1681_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; lean_object* v___x_1760_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_a_1759_);
lean_dec_ref_known(v___x_1758_, 1);
v___x_1760_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1678_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1772_; 
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1763_ = v___x_1760_;
v_isShared_1764_ = v_isSharedCheck_1772_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1760_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1772_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1770_; 
v___x_1765_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14, &l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14);
v___x_1766_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1766_, 0, v_a_1759_);
lean_ctor_set(v___x_1766_, 1, v___x_1765_);
v___x_1767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1766_);
lean_ctor_set(v___x_1767_, 1, v_a_1761_);
v___x_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1767_);
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 0, v___x_1768_);
v___x_1770_ = v___x_1763_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1768_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
else
{
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
lean_dec(v_a_1759_);
v_a_1773_ = lean_ctor_get(v___x_1760_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1775_ = v___x_1760_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1760_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1773_);
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
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
lean_dec_ref(v_arg_1678_);
v_a_1781_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1758_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1758_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
}
}
else
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1797_; 
lean_dec_ref(v_arg_1681_);
lean_dec_ref(v_arg_1678_);
v_a_1790_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1792_ = v___x_1748_;
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1748_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1795_; 
if (v_isShared_1793_ == 0)
{
v___x_1795_ = v___x_1792_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_a_1790_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
}
}
else
{
lean_object* v___x_1798_; 
lean_dec_ref(v___x_1691_);
v___x_1798_ = l_Lean_Meta_DefEq_isInstLEInt(v_arg_1688_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1837_; 
v_a_1799_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1801_ = v___x_1798_;
v_isShared_1802_ = v_isSharedCheck_1837_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1798_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1837_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
uint8_t v___x_1803_; 
v___x_1803_ = lean_unbox(v_a_1799_);
lean_dec(v_a_1799_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; lean_object* v___x_1806_; 
lean_dec_ref(v_arg_1681_);
lean_dec_ref(v_arg_1678_);
v___x_1804_ = lean_box(0);
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
else
{
lean_object* v___x_1808_; 
lean_del_object(v___x_1801_);
v___x_1808_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1678_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; lean_object* v___x_1810_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_a_1809_);
lean_dec_ref_known(v___x_1808_, 1);
v___x_1810_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1681_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1820_; 
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1813_ = v___x_1810_;
v_isShared_1814_ = v_isSharedCheck_1820_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1810_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1820_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1818_; 
v___x_1815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1815_, 0, v_a_1809_);
lean_ctor_set(v___x_1815_, 1, v_a_1811_);
v___x_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 0, v___x_1816_);
v___x_1818_ = v___x_1813_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1816_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
else
{
lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1828_; 
lean_dec(v_a_1809_);
v_a_1821_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1823_ = v___x_1810_;
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v___x_1810_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1826_; 
if (v_isShared_1824_ == 0)
{
v___x_1826_ = v___x_1823_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1821_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
}
else
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1836_; 
lean_dec_ref(v_arg_1681_);
v_a_1829_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1831_ = v___x_1808_;
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1808_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1834_; 
if (v_isShared_1832_ == 0)
{
v___x_1834_ = v___x_1831_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_a_1829_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
}
}
}
else
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1845_; 
lean_dec_ref(v_arg_1681_);
lean_dec_ref(v_arg_1678_);
v_a_1838_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1840_ = v___x_1798_;
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1798_);
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
else
{
lean_object* v___x_1846_; 
lean_dec_ref(v___x_1691_);
v___x_1846_ = l_Lean_Meta_DefEq_isInstLTInt(v_arg_1688_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1887_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1849_ = v___x_1846_;
v_isShared_1850_ = v_isSharedCheck_1887_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1846_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1887_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
uint8_t v___x_1851_; 
v___x_1851_ = lean_unbox(v_a_1847_);
lean_dec(v_a_1847_);
if (v___x_1851_ == 0)
{
lean_object* v___x_1852_; lean_object* v___x_1854_; 
lean_dec_ref(v_arg_1681_);
lean_dec_ref(v_arg_1678_);
v___x_1852_ = lean_box(0);
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 0, v___x_1852_);
v___x_1854_ = v___x_1849_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1852_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
else
{
lean_object* v___x_1856_; 
lean_del_object(v___x_1849_);
v___x_1856_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1678_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v_a_1857_; lean_object* v___x_1858_; 
v_a_1857_ = lean_ctor_get(v___x_1856_, 0);
lean_inc(v_a_1857_);
lean_dec_ref_known(v___x_1856_, 1);
v___x_1858_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1681_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1870_; 
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1861_ = v___x_1858_;
v_isShared_1862_ = v_isSharedCheck_1870_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1858_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1870_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1868_; 
v___x_1863_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14, &l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14);
v___x_1864_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1864_, 0, v_a_1857_);
lean_ctor_set(v___x_1864_, 1, v___x_1863_);
v___x_1865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1864_);
lean_ctor_set(v___x_1865_, 1, v_a_1859_);
v___x_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1865_);
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 0, v___x_1866_);
v___x_1868_ = v___x_1861_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v___x_1866_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
else
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1878_; 
lean_dec(v_a_1857_);
v_a_1871_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1873_ = v___x_1858_;
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1858_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1876_; 
if (v_isShared_1874_ == 0)
{
v___x_1876_ = v___x_1873_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_a_1871_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
}
else
{
lean_object* v_a_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1886_; 
lean_dec_ref(v_arg_1681_);
v_a_1879_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1886_ == 0)
{
v___x_1881_ = v___x_1856_;
v_isShared_1882_ = v_isSharedCheck_1886_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_a_1879_);
lean_dec(v___x_1856_);
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
}
}
}
else
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
lean_dec_ref(v_arg_1681_);
lean_dec_ref(v_arg_1678_);
v_a_1888_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1890_ = v___x_1846_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1846_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1888_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1896_; 
lean_dec_ref(v___x_1682_);
v___x_1896_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1681_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v_a_1897_; lean_object* v___x_1898_; 
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
lean_inc(v_a_1897_);
lean_dec_ref_known(v___x_1896_, 1);
v___x_1898_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1678_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1908_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1901_ = v___x_1898_;
v_isShared_1902_ = v_isSharedCheck_1908_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1898_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1908_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1906_; 
v___x_1903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1903_, 0, v_a_1897_);
lean_ctor_set(v___x_1903_, 1, v_a_1899_);
v___x_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1903_);
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 0, v___x_1904_);
v___x_1906_ = v___x_1901_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v___x_1904_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
else
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
lean_dec(v_a_1897_);
v_a_1909_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1911_ = v___x_1898_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1898_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1909_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
lean_dec_ref(v_arg_1678_);
v_a_1917_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1896_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1896_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1917_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
}
else
{
lean_object* v___x_1925_; 
lean_dec_ref(v___x_1682_);
v___x_1925_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1681_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v___x_1927_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_a_1926_);
lean_dec_ref_known(v___x_1925_, 1);
v___x_1927_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1678_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1939_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1930_ = v___x_1927_;
v_isShared_1931_ = v_isSharedCheck_1939_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1927_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1939_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1937_; 
v___x_1932_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14, &l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14);
v___x_1933_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1933_, 0, v_a_1926_);
lean_ctor_set(v___x_1933_, 1, v___x_1932_);
v___x_1934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1933_);
lean_ctor_set(v___x_1934_, 1, v_a_1928_);
v___x_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1934_);
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 0, v___x_1935_);
v___x_1937_ = v___x_1930_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v___x_1935_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
else
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1947_; 
lean_dec(v_a_1926_);
v_a_1940_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1942_ = v___x_1927_;
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1927_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1945_; 
if (v_isShared_1943_ == 0)
{
v___x_1945_ = v___x_1942_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_a_1940_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
lean_dec_ref(v_arg_1678_);
v_a_1948_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1925_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1925_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1963_; 
v_a_1956_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v___x_1674_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1674_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1959_ == 0)
{
v___x_1961_ = v___x_1958_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1956_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
v___jp_1671_:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1672_ = lean_box(0);
v___x_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1672_);
return v___x_1673_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1664_ = stack[0].m_obj;
lean_object* v_a_1665_ = stack[1].m_obj;
lean_object* v_a_1666_ = stack[2].m_obj;
lean_object* v_a_1667_ = stack[3].m_obj;
lean_object* v_a_1668_ = stack[4].m_obj;
lean_object* v_a_1669_ = stack[5].m_obj;
lean_object* v_res_1964_;
v_res_1964_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f(v_e_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_);
stack->m_obj
 = v_res_1964_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___boxed(lean_object* v_e_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f(v_e_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_);
lean_dec(v_a_1970_);
lean_dec_ref(v_a_1969_);
lean_dec(v_a_1968_);
lean_dec_ref(v_a_1967_);
lean_dec(v_a_1966_);
return v_res_1972_;
}
}
lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f(lean_object* v_e_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_){
_start:
{
lean_object* v___x_1988_; 
v___x_1988_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1978_, v_a_1981_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v_a_1989_; lean_object* v___x_1990_; uint8_t v___x_1991_; 
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
lean_inc(v_a_1989_);
lean_dec_ref_known(v___x_1988_, 1);
v___x_1990_ = l_Lean_Expr_cleanupAnnotations(v_a_1989_);
v___x_1991_ = l_Lean_Expr_isApp(v___x_1990_);
if (v___x_1991_ == 0)
{
lean_dec_ref(v___x_1990_);
goto v___jp_1985_;
}
else
{
lean_object* v_arg_1992_; lean_object* v___x_1993_; uint8_t v___x_1994_; 
v_arg_1992_ = lean_ctor_get(v___x_1990_, 1);
lean_inc_ref(v_arg_1992_);
v___x_1993_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1990_);
v___x_1994_ = l_Lean_Expr_isApp(v___x_1993_);
if (v___x_1994_ == 0)
{
lean_dec_ref(v___x_1993_);
lean_dec_ref(v_arg_1992_);
goto v___jp_1985_;
}
else
{
lean_object* v_arg_1995_; lean_object* v___x_1996_; uint8_t v___x_1997_; 
v_arg_1995_ = lean_ctor_get(v___x_1993_, 1);
lean_inc_ref(v_arg_1995_);
v___x_1996_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1993_);
v___x_1997_ = l_Lean_Expr_isApp(v___x_1996_);
if (v___x_1997_ == 0)
{
lean_dec_ref(v___x_1996_);
lean_dec_ref(v_arg_1995_);
lean_dec_ref(v_arg_1992_);
goto v___jp_1985_;
}
else
{
lean_object* v_arg_1998_; lean_object* v___x_1999_; uint8_t v___x_2000_; 
v_arg_1998_ = lean_ctor_get(v___x_1996_, 1);
lean_inc_ref(v_arg_1998_);
v___x_1999_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1996_);
v___x_2000_ = l_Lean_Expr_isApp(v___x_1999_);
if (v___x_2000_ == 0)
{
lean_dec_ref(v___x_1999_);
lean_dec_ref(v_arg_1998_);
lean_dec_ref(v_arg_1995_);
lean_dec_ref(v_arg_1992_);
goto v___jp_1985_;
}
else
{
lean_object* v___x_2001_; lean_object* v___x_2002_; uint8_t v___x_2003_; 
v___x_2001_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1999_);
v___x_2002_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__2));
v___x_2003_ = l_Lean_Expr_isConstOf(v___x_2001_, v___x_2002_);
lean_dec_ref(v___x_2001_);
if (v___x_2003_ == 0)
{
lean_dec_ref(v_arg_1998_);
lean_dec_ref(v_arg_1995_);
lean_dec_ref(v_arg_1992_);
goto v___jp_1985_;
}
else
{
lean_object* v___x_2004_; 
v___x_2004_ = l_Lean_Meta_DefEq_isInstDvdInt(v_arg_1998_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2058_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2007_ = v___x_2004_;
v_isShared_2008_ = v_isSharedCheck_2058_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_2004_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2058_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
uint8_t v___x_2009_; 
v___x_2009_ = lean_unbox(v_a_2005_);
lean_dec(v_a_2005_);
if (v___x_2009_ == 0)
{
lean_object* v___x_2010_; lean_object* v___x_2012_; 
lean_dec_ref(v_arg_1995_);
lean_dec_ref(v_arg_1992_);
v___x_2010_ = lean_box(0);
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 0, v___x_2010_);
v___x_2012_ = v___x_2007_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2010_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
else
{
lean_object* v___x_2014_; 
lean_del_object(v___x_2007_);
v___x_2014_ = l_Lean_Meta_getIntValue_x3f(v_arg_1995_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2049_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2017_ = v___x_2014_;
v_isShared_2018_ = v_isSharedCheck_2049_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_2014_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2049_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
if (lean_obj_tag(v_a_2015_) == 1)
{
lean_object* v_val_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2044_; 
lean_del_object(v___x_2017_);
v_val_2019_ = lean_ctor_get(v_a_2015_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v_a_2015_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2021_ = v_a_2015_;
v_isShared_2022_ = v_isSharedCheck_2044_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_val_2019_);
lean_dec(v_a_2015_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2044_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2023_; 
v___x_2023_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1992_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2035_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2026_ = v___x_2023_;
v_isShared_2027_ = v_isSharedCheck_2035_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_2023_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2035_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2028_; lean_object* v___x_2030_; 
v___x_2028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2028_, 0, v_val_2019_);
lean_ctor_set(v___x_2028_, 1, v_a_2024_);
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 0, v___x_2028_);
v___x_2030_ = v___x_2021_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2028_);
v___x_2030_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
lean_object* v___x_2032_; 
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 0, v___x_2030_);
v___x_2032_ = v___x_2026_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_2030_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
else
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2043_; 
lean_del_object(v___x_2021_);
lean_dec(v_val_2019_);
v_a_2036_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2038_ = v___x_2023_;
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_2023_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
if (v_isShared_2039_ == 0)
{
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_a_2036_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
}
}
else
{
lean_object* v___x_2045_; lean_object* v___x_2047_; 
lean_dec(v_a_2015_);
lean_dec_ref(v_arg_1992_);
v___x_2045_ = lean_box(0);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 0, v___x_2045_);
v___x_2047_ = v___x_2017_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2045_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
}
else
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2057_; 
lean_dec_ref(v_arg_1992_);
v_a_2050_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2052_ = v___x_2014_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2014_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2055_; 
if (v_isShared_2053_ == 0)
{
v___x_2055_ = v___x_2052_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_a_2050_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
}
}
}
else
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
lean_dec_ref(v_arg_1995_);
lean_dec_ref(v_arg_1992_);
v_a_2059_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_2004_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2004_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
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
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
v_a_2067_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2069_ = v___x_1988_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_1988_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2070_ == 0)
{
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
v___jp_1985_:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1986_ = lean_box(0);
v___x_1987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1986_);
return v___x_1987_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1978_ = stack[0].m_obj;
lean_object* v_a_1979_ = stack[1].m_obj;
lean_object* v_a_1980_ = stack[2].m_obj;
lean_object* v_a_1981_ = stack[3].m_obj;
lean_object* v_a_1982_ = stack[4].m_obj;
lean_object* v_a_1983_ = stack[5].m_obj;
lean_object* v_res_2075_;
v_res_2075_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f(v_e_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_);
stack->m_obj
 = v_res_2075_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___boxed(lean_object* v_e_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f(v_e_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_);
lean_dec(v_a_2081_);
lean_dec_ref(v_a_2080_);
lean_dec(v_a_2079_);
lean_dec_ref(v_a_2078_);
lean_dec(v_a_2077_);
return v_res_2083_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_2084_; 
v___x_2084_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2084_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2085_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__0, &l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__0_once, _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__0);
v___x_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2085_);
return v___x_2086_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__3(void){
_start:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2089_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__2));
v___x_2090_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__1, &l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__1_once, _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__1);
v___x_2091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2090_);
lean_ctor_set(v___x_2091_, 1, v___x_2089_);
return v___x_2091_;
}
}
lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(lean_object* v_x_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_){
_start:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2098_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__3, &l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__3);
v___x_2099_ = lean_st_mk_ref(v___x_2098_);
lean_inc(v_a_2096_);
lean_inc_ref(v_a_2095_);
lean_inc(v_a_2094_);
lean_inc_ref(v_a_2093_);
lean_inc(v___x_2099_);
v___x_2100_ = lean_apply_6(v_x_2092_, v___x_2099_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_, lean_box(0));
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_a_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2118_; 
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2103_ = v___x_2100_;
v_isShared_2104_ = v_isSharedCheck_2118_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_a_2101_);
lean_dec(v___x_2100_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2118_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2105_; lean_object* v_vars_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2116_; 
v___x_2105_ = lean_st_ref_get(v___x_2099_);
lean_dec(v___x_2099_);
v_vars_2106_ = lean_ctor_get(v___x_2105_, 1);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2116_ == 0)
{
lean_object* v_unused_2117_; 
v_unused_2117_ = lean_ctor_get(v___x_2105_, 0);
lean_dec(v_unused_2117_);
v___x_2108_ = v___x_2105_;
v_isShared_2109_ = v_isSharedCheck_2116_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_vars_2106_);
lean_dec(v___x_2105_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2116_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
lean_ctor_set(v___x_2108_, 0, v_a_2101_);
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2101_);
lean_ctor_set(v_reuseFailAlloc_2115_, 1, v_vars_2106_);
v___x_2111_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
lean_object* v___x_2113_; 
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 0, v___x_2111_);
v___x_2113_ = v___x_2103_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v___x_2111_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
}
}
else
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2126_; 
lean_dec(v___x_2099_);
v_a_2119_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v___x_2100_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2100_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2124_; 
if (v_isShared_2122_ == 0)
{
v___x_2124_ = v___x_2121_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_a_2119_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2092_ = stack[0].m_obj;
lean_object* v_a_2093_ = stack[1].m_obj;
lean_object* v_a_2094_ = stack[2].m_obj;
lean_object* v_a_2095_ = stack[3].m_obj;
lean_object* v_a_2096_ = stack[4].m_obj;
lean_object* v_res_2127_;
v_res_2127_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(v_x_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_);
stack->m_obj
 = v_res_2127_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___boxed(lean_object* v_x_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_){
_start:
{
lean_object* v_res_2134_; 
v_res_2134_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(v_x_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_);
lean_dec(v_a_2132_);
lean_dec_ref(v_a_2131_);
lean_dec(v_a_2130_);
lean_dec_ref(v_a_2129_);
return v_res_2134_;
}
}
lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run(lean_object* v_00_u03b1_2135_, lean_object* v_x_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_){
_start:
{
lean_object* v___x_2142_; 
v___x_2142_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(v_x_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_);
return v___x_2142_;
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_Arith_Int_ToLinear_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2136_ = stack[1].m_obj;
lean_object* v_a_2137_ = stack[2].m_obj;
lean_object* v_a_2138_ = stack[3].m_obj;
lean_object* v_a_2139_ = stack[4].m_obj;
lean_object* v_a_2140_ = stack[5].m_obj;
lean_object* v_res_2143_;
v_res_2143_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run(lean_box(0), v_x_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_);
stack->m_obj
 = v_res_2143_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run___boxed(lean_object* v_00_u03b1_2144_, lean_object* v_x_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_){
_start:
{
lean_object* v_res_2151_; 
v_res_2151_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run(v_00_u03b1_2144_, v_x_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_);
lean_dec(v_a_2149_);
lean_dec_ref(v_a_2148_);
lean_dec(v_a_2147_);
lean_dec_ref(v_a_2146_);
return v_res_2151_;
}
}
lean_object* l_Lean_Meta_Simp_Arith_Int_toLinearExpr(lean_object* v_e_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_){
_start:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2158_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr___boxed), 7, 1);
lean_closure_set(v___x_2158_, 0, v_e_2152_);
v___x_2159_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(v___x_2158_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v_a_2160_; lean_object* v_fst_2161_; lean_object* v_snd_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; uint8_t v___x_2165_; 
v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
v_fst_2161_ = lean_ctor_get(v_a_2160_, 0);
v_snd_2162_ = lean_ctor_get(v_a_2160_, 1);
v___x_2163_ = lean_array_get_size(v_snd_2162_);
v___x_2164_ = lean_unsigned_to_nat(1u);
v___x_2165_ = lean_nat_dec_eq(v___x_2163_, v___x_2164_);
if (v___x_2165_ == 0)
{
lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2183_; 
lean_inc(v_snd_2162_);
lean_inc(v_fst_2161_);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2183_ == 0)
{
lean_object* v_unused_2184_; 
v_unused_2184_ = lean_ctor_get(v___x_2159_, 0);
lean_dec(v_unused_2184_);
v___x_2167_ = v___x_2159_;
v_isShared_2168_ = v_isSharedCheck_2183_;
goto v_resetjp_2166_;
}
else
{
lean_dec(v___x_2159_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2183_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2169_; lean_object* v_fst_2170_; lean_object* v_snd_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2182_; 
v___x_2169_ = l_Lean_sortExprs(v_snd_2162_, v___x_2165_);
v_fst_2170_ = lean_ctor_get(v___x_2169_, 0);
v_snd_2171_ = lean_ctor_get(v___x_2169_, 1);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2173_ = v___x_2169_;
v_isShared_2174_ = v_isSharedCheck_2182_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_snd_2171_);
lean_inc(v_fst_2170_);
lean_dec(v___x_2169_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2182_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2175_; lean_object* v___x_2177_; 
v___x_2175_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_snd_2171_, v_fst_2161_);
lean_dec(v_snd_2171_);
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 1, v_fst_2170_);
lean_ctor_set(v___x_2173_, 0, v___x_2175_);
v___x_2177_ = v___x_2173_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2175_);
lean_ctor_set(v_reuseFailAlloc_2181_, 1, v_fst_2170_);
v___x_2177_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
lean_object* v___x_2179_; 
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 0, v___x_2177_);
v___x_2179_ = v___x_2167_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2177_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
}
else
{
return v___x_2159_;
}
}
else
{
return v___x_2159_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_Arith_Int_toLinearExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2152_ = stack[0].m_obj;
lean_object* v_a_2153_ = stack[1].m_obj;
lean_object* v_a_2154_ = stack[2].m_obj;
lean_object* v_a_2155_ = stack[3].m_obj;
lean_object* v_a_2156_ = stack[4].m_obj;
lean_object* v_res_2185_;
v_res_2185_ = l_Lean_Meta_Simp_Arith_Int_toLinearExpr(v_e_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_);
stack->m_obj
 = v_res_2185_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toLinearExpr___boxed(lean_object* v_e_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = l_Lean_Meta_Simp_Arith_Int_toLinearExpr(v_e_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_);
lean_dec(v_a_2190_);
lean_dec_ref(v_a_2189_);
lean_dec(v_a_2188_);
lean_dec_ref(v_a_2187_);
return v_res_2192_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_adapter(lean_object* v_e_2193_, lean_object* v_k_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2200_ = lean_apply_1(v_k_2194_, v_e_2193_);
v___x_2201_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(v___x_2200_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2264_; 
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2204_ = v___x_2201_;
v_isShared_2205_ = v_isSharedCheck_2264_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_2201_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2264_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v_fst_2206_; 
v_fst_2206_ = lean_ctor_get(v_a_2202_, 0);
lean_inc(v_fst_2206_);
if (lean_obj_tag(v_fst_2206_) == 1)
{
lean_object* v_val_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2259_; 
v_val_2207_ = lean_ctor_get(v_fst_2206_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v_fst_2206_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2209_ = v_fst_2206_;
v_isShared_2210_ = v_isSharedCheck_2259_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_val_2207_);
lean_dec(v_fst_2206_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2259_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v_snd_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2257_; 
v_snd_2211_ = lean_ctor_get(v_a_2202_, 1);
v_isSharedCheck_2257_ = !lean_is_exclusive(v_a_2202_);
if (v_isSharedCheck_2257_ == 0)
{
lean_object* v_unused_2258_; 
v_unused_2258_ = lean_ctor_get(v_a_2202_, 0);
lean_dec(v_unused_2258_);
v___x_2213_ = v_a_2202_;
v_isShared_2214_ = v_isSharedCheck_2257_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_snd_2211_);
lean_dec(v_a_2202_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2257_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v_fst_2215_; lean_object* v_snd_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2256_; 
v_fst_2215_ = lean_ctor_get(v_val_2207_, 0);
v_snd_2216_ = lean_ctor_get(v_val_2207_, 1);
v_isSharedCheck_2256_ = !lean_is_exclusive(v_val_2207_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2218_ = v_val_2207_;
v_isShared_2219_ = v_isSharedCheck_2256_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_snd_2216_);
lean_inc(v_fst_2215_);
lean_dec(v_val_2207_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2256_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; uint8_t v___x_2222_; 
v___x_2220_ = lean_array_get_size(v_snd_2211_);
v___x_2221_ = lean_unsigned_to_nat(1u);
v___x_2222_ = lean_nat_dec_le(v___x_2220_, v___x_2221_);
if (v___x_2222_ == 0)
{
lean_object* v___x_2223_; lean_object* v_fst_2224_; lean_object* v_snd_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2243_; 
lean_del_object(v___x_2213_);
v___x_2223_ = l_Lean_sortExprs(v_snd_2211_, v___x_2222_);
v_fst_2224_ = lean_ctor_get(v___x_2223_, 0);
v_snd_2225_ = lean_ctor_get(v___x_2223_, 1);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2223_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2227_ = v___x_2223_;
v_isShared_2228_ = v_isSharedCheck_2243_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_snd_2225_);
lean_inc(v_fst_2224_);
lean_dec(v___x_2223_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2243_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2232_; 
v___x_2229_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_snd_2225_, v_fst_2215_);
v___x_2230_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_snd_2225_, v_snd_2216_);
lean_dec(v_snd_2225_);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 1, v_fst_2224_);
lean_ctor_set(v___x_2227_, 0, v___x_2230_);
v___x_2232_ = v___x_2227_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v___x_2230_);
lean_ctor_set(v_reuseFailAlloc_2242_, 1, v_fst_2224_);
v___x_2232_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
lean_object* v___x_2234_; 
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 1, v___x_2232_);
lean_ctor_set(v___x_2218_, 0, v___x_2229_);
v___x_2234_ = v___x_2218_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2229_);
lean_ctor_set(v_reuseFailAlloc_2241_, 1, v___x_2232_);
v___x_2234_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
lean_object* v___x_2236_; 
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 0, v___x_2234_);
v___x_2236_ = v___x_2209_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2234_);
v___x_2236_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
lean_object* v___x_2238_; 
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 0, v___x_2236_);
v___x_2238_ = v___x_2204_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v___x_2236_);
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
}
else
{
lean_object* v___x_2245_; 
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 1, v_snd_2211_);
lean_ctor_set(v___x_2218_, 0, v_snd_2216_);
v___x_2245_ = v___x_2218_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_snd_2216_);
lean_ctor_set(v_reuseFailAlloc_2255_, 1, v_snd_2211_);
v___x_2245_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
lean_object* v___x_2247_; 
if (v_isShared_2214_ == 0)
{
lean_ctor_set(v___x_2213_, 1, v___x_2245_);
lean_ctor_set(v___x_2213_, 0, v_fst_2215_);
v___x_2247_ = v___x_2213_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_fst_2215_);
lean_ctor_set(v_reuseFailAlloc_2254_, 1, v___x_2245_);
v___x_2247_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
lean_object* v___x_2249_; 
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 0, v___x_2247_);
v___x_2249_ = v___x_2209_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v___x_2247_);
v___x_2249_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
lean_object* v___x_2251_; 
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 0, v___x_2249_);
v___x_2251_ = v___x_2204_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v___x_2249_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
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
lean_object* v___x_2260_; lean_object* v___x_2262_; 
lean_dec(v_fst_2206_);
lean_dec(v_a_2202_);
v___x_2260_ = lean_box(0);
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 0, v___x_2260_);
v___x_2262_ = v___x_2204_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v___x_2260_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
}
else
{
lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2272_; 
v_a_2265_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2267_ = v___x_2201_;
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2201_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2272_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2270_; 
if (v_isShared_2268_ == 0)
{
v___x_2270_ = v___x_2267_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_a_2265_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_adapter_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2193_ = stack[0].m_obj;
lean_object* v_k_2194_ = stack[1].m_obj;
lean_object* v_a_2195_ = stack[2].m_obj;
lean_object* v_a_2196_ = stack[3].m_obj;
lean_object* v_a_2197_ = stack[4].m_obj;
lean_object* v_a_2198_ = stack[5].m_obj;
lean_object* v_res_2273_;
v_res_2273_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_adapter(v_e_2193_, v_k_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
stack->m_obj
 = v_res_2273_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_adapter___boxed(lean_object* v_e_2274_, lean_object* v_k_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_){
_start:
{
lean_object* v_res_2281_; 
v_res_2281_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_adapter(v_e_2274_, v_k_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_);
lean_dec(v_a_2279_);
lean_dec_ref(v_a_2278_);
lean_dec(v_a_2277_);
lean_dec_ref(v_a_2276_);
return v_res_2281_;
}
}
lean_object* l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(lean_object* v_e_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_){
_start:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2288_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___boxed), 7, 1);
lean_closure_set(v___x_2288_, 0, v_e_2282_);
v___x_2289_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(v___x_2288_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_);
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2352_; 
v_a_2290_ = lean_ctor_get(v___x_2289_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2292_ = v___x_2289_;
v_isShared_2293_ = v_isSharedCheck_2352_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2289_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2352_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v_fst_2294_; 
v_fst_2294_ = lean_ctor_get(v_a_2290_, 0);
lean_inc(v_fst_2294_);
if (lean_obj_tag(v_fst_2294_) == 1)
{
lean_object* v_val_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2347_; 
v_val_2295_ = lean_ctor_get(v_fst_2294_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v_fst_2294_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2297_ = v_fst_2294_;
v_isShared_2298_ = v_isSharedCheck_2347_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_val_2295_);
lean_dec(v_fst_2294_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2347_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v_snd_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2345_; 
v_snd_2299_ = lean_ctor_get(v_a_2290_, 1);
v_isSharedCheck_2345_ = !lean_is_exclusive(v_a_2290_);
if (v_isSharedCheck_2345_ == 0)
{
lean_object* v_unused_2346_; 
v_unused_2346_ = lean_ctor_get(v_a_2290_, 0);
lean_dec(v_unused_2346_);
v___x_2301_ = v_a_2290_;
v_isShared_2302_ = v_isSharedCheck_2345_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_snd_2299_);
lean_dec(v_a_2290_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2345_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v_fst_2303_; lean_object* v_snd_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2344_; 
v_fst_2303_ = lean_ctor_get(v_val_2295_, 0);
v_snd_2304_ = lean_ctor_get(v_val_2295_, 1);
v_isSharedCheck_2344_ = !lean_is_exclusive(v_val_2295_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2306_ = v_val_2295_;
v_isShared_2307_ = v_isSharedCheck_2344_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_snd_2304_);
lean_inc(v_fst_2303_);
lean_dec(v_val_2295_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2344_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; uint8_t v___x_2310_; 
v___x_2308_ = lean_array_get_size(v_snd_2299_);
v___x_2309_ = lean_unsigned_to_nat(1u);
v___x_2310_ = lean_nat_dec_le(v___x_2308_, v___x_2309_);
if (v___x_2310_ == 0)
{
lean_object* v___x_2311_; lean_object* v_fst_2312_; lean_object* v_snd_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2331_; 
lean_del_object(v___x_2301_);
v___x_2311_ = l_Lean_sortExprs(v_snd_2299_, v___x_2310_);
v_fst_2312_ = lean_ctor_get(v___x_2311_, 0);
v_snd_2313_ = lean_ctor_get(v___x_2311_, 1);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2315_ = v___x_2311_;
v_isShared_2316_ = v_isSharedCheck_2331_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_snd_2313_);
lean_inc(v_fst_2312_);
lean_dec(v___x_2311_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2331_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2320_; 
v___x_2317_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_snd_2313_, v_fst_2303_);
v___x_2318_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_snd_2313_, v_snd_2304_);
lean_dec(v_snd_2313_);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 1, v_fst_2312_);
lean_ctor_set(v___x_2315_, 0, v___x_2318_);
v___x_2320_ = v___x_2315_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2318_);
lean_ctor_set(v_reuseFailAlloc_2330_, 1, v_fst_2312_);
v___x_2320_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
lean_object* v___x_2322_; 
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 1, v___x_2320_);
lean_ctor_set(v___x_2306_, 0, v___x_2317_);
v___x_2322_ = v___x_2306_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2317_);
lean_ctor_set(v_reuseFailAlloc_2329_, 1, v___x_2320_);
v___x_2322_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
lean_object* v___x_2324_; 
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 0, v___x_2322_);
v___x_2324_ = v___x_2297_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v___x_2322_);
v___x_2324_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
lean_object* v___x_2326_; 
if (v_isShared_2293_ == 0)
{
lean_ctor_set(v___x_2292_, 0, v___x_2324_);
v___x_2326_ = v___x_2292_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2324_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
}
}
}
else
{
lean_object* v___x_2333_; 
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 1, v_snd_2299_);
lean_ctor_set(v___x_2306_, 0, v_snd_2304_);
v___x_2333_ = v___x_2306_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_snd_2304_);
lean_ctor_set(v_reuseFailAlloc_2343_, 1, v_snd_2299_);
v___x_2333_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
lean_object* v___x_2335_; 
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 1, v___x_2333_);
lean_ctor_set(v___x_2301_, 0, v_fst_2303_);
v___x_2335_ = v___x_2301_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_fst_2303_);
lean_ctor_set(v_reuseFailAlloc_2342_, 1, v___x_2333_);
v___x_2335_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
lean_object* v___x_2337_; 
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 0, v___x_2335_);
v___x_2337_ = v___x_2297_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2335_);
v___x_2337_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
lean_object* v___x_2339_; 
if (v_isShared_2293_ == 0)
{
lean_ctor_set(v___x_2292_, 0, v___x_2337_);
v___x_2339_ = v___x_2292_;
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
}
}
}
}
}
else
{
lean_object* v___x_2348_; lean_object* v___x_2350_; 
lean_dec(v_fst_2294_);
lean_dec(v_a_2290_);
v___x_2348_ = lean_box(0);
if (v_isShared_2293_ == 0)
{
lean_ctor_set(v___x_2292_, 0, v___x_2348_);
v___x_2350_ = v___x_2292_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2348_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
else
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
v_a_2353_ = lean_ctor_get(v___x_2289_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2355_ = v___x_2289_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2289_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2356_ == 0)
{
v___x_2358_ = v___x_2355_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2353_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2282_ = stack[0].m_obj;
lean_object* v_a_2283_ = stack[1].m_obj;
lean_object* v_a_2284_ = stack[2].m_obj;
lean_object* v_a_2285_ = stack[3].m_obj;
lean_object* v_a_2286_ = stack[4].m_obj;
lean_object* v_res_2361_;
v_res_2361_ = l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(v_e_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_);
stack->m_obj
 = v_res_2361_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f___boxed(lean_object* v_e_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_){
_start:
{
lean_object* v_res_2368_; 
v_res_2368_ = l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(v_e_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_);
lean_dec(v_a_2366_);
lean_dec_ref(v_a_2365_);
lean_dec(v_a_2364_);
lean_dec_ref(v_a_2363_);
return v_res_2368_;
}
}
lean_object* l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(lean_object* v_e_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_){
_start:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2375_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___boxed), 7, 1);
lean_closure_set(v___x_2375_, 0, v_e_2369_);
v___x_2376_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(v___x_2375_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2439_; 
v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2379_ = v___x_2376_;
v_isShared_2380_ = v_isSharedCheck_2439_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2376_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2439_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v_fst_2381_; 
v_fst_2381_ = lean_ctor_get(v_a_2377_, 0);
lean_inc(v_fst_2381_);
if (lean_obj_tag(v_fst_2381_) == 1)
{
lean_object* v_val_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2434_; 
v_val_2382_ = lean_ctor_get(v_fst_2381_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v_fst_2381_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2384_ = v_fst_2381_;
v_isShared_2385_ = v_isSharedCheck_2434_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_val_2382_);
lean_dec(v_fst_2381_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2434_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v_snd_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2432_; 
v_snd_2386_ = lean_ctor_get(v_a_2377_, 1);
v_isSharedCheck_2432_ = !lean_is_exclusive(v_a_2377_);
if (v_isSharedCheck_2432_ == 0)
{
lean_object* v_unused_2433_; 
v_unused_2433_ = lean_ctor_get(v_a_2377_, 0);
lean_dec(v_unused_2433_);
v___x_2388_ = v_a_2377_;
v_isShared_2389_ = v_isSharedCheck_2432_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_snd_2386_);
lean_dec(v_a_2377_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2432_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v_fst_2390_; lean_object* v_snd_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2431_; 
v_fst_2390_ = lean_ctor_get(v_val_2382_, 0);
v_snd_2391_ = lean_ctor_get(v_val_2382_, 1);
v_isSharedCheck_2431_ = !lean_is_exclusive(v_val_2382_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2393_ = v_val_2382_;
v_isShared_2394_ = v_isSharedCheck_2431_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_snd_2391_);
lean_inc(v_fst_2390_);
lean_dec(v_val_2382_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2431_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; uint8_t v___x_2397_; 
v___x_2395_ = lean_array_get_size(v_snd_2386_);
v___x_2396_ = lean_unsigned_to_nat(1u);
v___x_2397_ = lean_nat_dec_le(v___x_2395_, v___x_2396_);
if (v___x_2397_ == 0)
{
lean_object* v___x_2398_; lean_object* v_fst_2399_; lean_object* v_snd_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2418_; 
lean_del_object(v___x_2388_);
v___x_2398_ = l_Lean_sortExprs(v_snd_2386_, v___x_2397_);
v_fst_2399_ = lean_ctor_get(v___x_2398_, 0);
v_snd_2400_ = lean_ctor_get(v___x_2398_, 1);
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2402_ = v___x_2398_;
v_isShared_2403_ = v_isSharedCheck_2418_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_snd_2400_);
lean_inc(v_fst_2399_);
lean_dec(v___x_2398_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2418_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2407_; 
v___x_2404_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_snd_2400_, v_fst_2390_);
v___x_2405_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_snd_2400_, v_snd_2391_);
lean_dec(v_snd_2400_);
if (v_isShared_2403_ == 0)
{
lean_ctor_set(v___x_2402_, 1, v_fst_2399_);
lean_ctor_set(v___x_2402_, 0, v___x_2405_);
v___x_2407_ = v___x_2402_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v___x_2405_);
lean_ctor_set(v_reuseFailAlloc_2417_, 1, v_fst_2399_);
v___x_2407_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
lean_object* v___x_2409_; 
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 1, v___x_2407_);
lean_ctor_set(v___x_2393_, 0, v___x_2404_);
v___x_2409_ = v___x_2393_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v___x_2404_);
lean_ctor_set(v_reuseFailAlloc_2416_, 1, v___x_2407_);
v___x_2409_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
lean_object* v___x_2411_; 
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 0, v___x_2409_);
v___x_2411_ = v___x_2384_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v___x_2409_);
v___x_2411_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
lean_object* v___x_2413_; 
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 0, v___x_2411_);
v___x_2413_ = v___x_2379_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v___x_2411_);
v___x_2413_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
return v___x_2413_;
}
}
}
}
}
}
else
{
lean_object* v___x_2420_; 
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 1, v_snd_2386_);
lean_ctor_set(v___x_2393_, 0, v_snd_2391_);
v___x_2420_ = v___x_2393_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_snd_2391_);
lean_ctor_set(v_reuseFailAlloc_2430_, 1, v_snd_2386_);
v___x_2420_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
lean_object* v___x_2422_; 
if (v_isShared_2389_ == 0)
{
lean_ctor_set(v___x_2388_, 1, v___x_2420_);
lean_ctor_set(v___x_2388_, 0, v_fst_2390_);
v___x_2422_ = v___x_2388_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_fst_2390_);
lean_ctor_set(v_reuseFailAlloc_2429_, 1, v___x_2420_);
v___x_2422_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
lean_object* v___x_2424_; 
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 0, v___x_2422_);
v___x_2424_ = v___x_2384_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2422_);
v___x_2424_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
lean_object* v___x_2426_; 
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 0, v___x_2424_);
v___x_2426_ = v___x_2379_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2424_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
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
lean_object* v___x_2435_; lean_object* v___x_2437_; 
lean_dec(v_fst_2381_);
lean_dec(v_a_2377_);
v___x_2435_ = lean_box(0);
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 0, v___x_2435_);
v___x_2437_ = v___x_2379_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v___x_2435_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
}
}
else
{
lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2447_; 
v_a_2440_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2442_ = v___x_2376_;
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v___x_2376_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2445_; 
if (v_isShared_2443_ == 0)
{
v___x_2445_ = v___x_2442_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_a_2440_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2369_ = stack[0].m_obj;
lean_object* v_a_2370_ = stack[1].m_obj;
lean_object* v_a_2371_ = stack[2].m_obj;
lean_object* v_a_2372_ = stack[3].m_obj;
lean_object* v_a_2373_ = stack[4].m_obj;
lean_object* v_res_2448_;
v_res_2448_ = l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(v_e_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_);
stack->m_obj
 = v_res_2448_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f___boxed(lean_object* v_e_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_){
_start:
{
lean_object* v_res_2455_; 
v_res_2455_ = l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(v_e_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_);
lean_dec(v_a_2453_);
lean_dec_ref(v_a_2452_);
lean_dec(v_a_2451_);
lean_dec_ref(v_a_2450_);
return v_res_2455_;
}
}
lean_object* l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(lean_object* v_e_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_){
_start:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2462_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___boxed), 7, 1);
lean_closure_set(v___x_2462_, 0, v_e_2456_);
v___x_2463_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(v___x_2462_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2525_; 
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2466_ = v___x_2463_;
v_isShared_2467_ = v_isSharedCheck_2525_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2463_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2525_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v_fst_2468_; 
v_fst_2468_ = lean_ctor_get(v_a_2464_, 0);
lean_inc(v_fst_2468_);
if (lean_obj_tag(v_fst_2468_) == 1)
{
lean_object* v_val_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2520_; 
v_val_2469_ = lean_ctor_get(v_fst_2468_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v_fst_2468_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2471_ = v_fst_2468_;
v_isShared_2472_ = v_isSharedCheck_2520_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_val_2469_);
lean_dec(v_fst_2468_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2520_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v_snd_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2518_; 
v_snd_2473_ = lean_ctor_get(v_a_2464_, 1);
v_isSharedCheck_2518_ = !lean_is_exclusive(v_a_2464_);
if (v_isSharedCheck_2518_ == 0)
{
lean_object* v_unused_2519_; 
v_unused_2519_ = lean_ctor_get(v_a_2464_, 0);
lean_dec(v_unused_2519_);
v___x_2475_ = v_a_2464_;
v_isShared_2476_ = v_isSharedCheck_2518_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_snd_2473_);
lean_dec(v_a_2464_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2518_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v_fst_2477_; lean_object* v_snd_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2517_; 
v_fst_2477_ = lean_ctor_get(v_val_2469_, 0);
v_snd_2478_ = lean_ctor_get(v_val_2469_, 1);
v_isSharedCheck_2517_ = !lean_is_exclusive(v_val_2469_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2480_ = v_val_2469_;
v_isShared_2481_ = v_isSharedCheck_2517_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_snd_2478_);
lean_inc(v_fst_2477_);
lean_dec(v_val_2469_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2517_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; uint8_t v___x_2484_; 
v___x_2482_ = lean_array_get_size(v_snd_2473_);
v___x_2483_ = lean_unsigned_to_nat(1u);
v___x_2484_ = lean_nat_dec_le(v___x_2482_, v___x_2483_);
if (v___x_2484_ == 0)
{
lean_object* v___x_2485_; lean_object* v_fst_2486_; lean_object* v_snd_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2504_; 
lean_del_object(v___x_2475_);
v___x_2485_ = l_Lean_sortExprs(v_snd_2473_, v___x_2484_);
v_fst_2486_ = lean_ctor_get(v___x_2485_, 0);
v_snd_2487_ = lean_ctor_get(v___x_2485_, 1);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2489_ = v___x_2485_;
v_isShared_2490_ = v_isSharedCheck_2504_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_snd_2487_);
lean_inc(v_fst_2486_);
lean_dec(v___x_2485_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2504_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2491_; lean_object* v___x_2493_; 
v___x_2491_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_snd_2487_, v_snd_2478_);
lean_dec(v_snd_2487_);
if (v_isShared_2490_ == 0)
{
lean_ctor_set(v___x_2489_, 1, v_fst_2486_);
lean_ctor_set(v___x_2489_, 0, v___x_2491_);
v___x_2493_ = v___x_2489_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v___x_2491_);
lean_ctor_set(v_reuseFailAlloc_2503_, 1, v_fst_2486_);
v___x_2493_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
lean_object* v___x_2495_; 
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 1, v___x_2493_);
v___x_2495_ = v___x_2480_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_fst_2477_);
lean_ctor_set(v_reuseFailAlloc_2502_, 1, v___x_2493_);
v___x_2495_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
lean_object* v___x_2497_; 
if (v_isShared_2472_ == 0)
{
lean_ctor_set(v___x_2471_, 0, v___x_2495_);
v___x_2497_ = v___x_2471_;
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
if (v_isShared_2467_ == 0)
{
lean_ctor_set(v___x_2466_, 0, v___x_2497_);
v___x_2499_ = v___x_2466_;
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
else
{
lean_object* v___x_2506_; 
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 1, v_snd_2473_);
lean_ctor_set(v___x_2480_, 0, v_snd_2478_);
v___x_2506_ = v___x_2480_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_snd_2478_);
lean_ctor_set(v_reuseFailAlloc_2516_, 1, v_snd_2473_);
v___x_2506_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
lean_object* v___x_2508_; 
if (v_isShared_2476_ == 0)
{
lean_ctor_set(v___x_2475_, 1, v___x_2506_);
lean_ctor_set(v___x_2475_, 0, v_fst_2477_);
v___x_2508_ = v___x_2475_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_fst_2477_);
lean_ctor_set(v_reuseFailAlloc_2515_, 1, v___x_2506_);
v___x_2508_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
lean_object* v___x_2510_; 
if (v_isShared_2472_ == 0)
{
lean_ctor_set(v___x_2471_, 0, v___x_2508_);
v___x_2510_ = v___x_2471_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v___x_2508_);
v___x_2510_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
lean_object* v___x_2512_; 
if (v_isShared_2467_ == 0)
{
lean_ctor_set(v___x_2466_, 0, v___x_2510_);
v___x_2512_ = v___x_2466_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2510_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
return v___x_2512_;
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
lean_object* v___x_2521_; lean_object* v___x_2523_; 
lean_dec(v_fst_2468_);
lean_dec(v_a_2464_);
v___x_2521_ = lean_box(0);
if (v_isShared_2467_ == 0)
{
lean_ctor_set(v___x_2466_, 0, v___x_2521_);
v___x_2523_ = v___x_2466_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___x_2521_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
}
else
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
v_a_2526_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2528_ = v___x_2463_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2463_);
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
LEAN_EXPORT void l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2456_ = stack[0].m_obj;
lean_object* v_a_2457_ = stack[1].m_obj;
lean_object* v_a_2458_ = stack[2].m_obj;
lean_object* v_a_2459_ = stack[3].m_obj;
lean_object* v_a_2460_ = stack[4].m_obj;
lean_object* v_res_2534_;
v_res_2534_ = l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(v_e_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_);
stack->m_obj
 = v_res_2534_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f___boxed(lean_object* v_e_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_){
_start:
{
lean_object* v_res_2541_; 
v_res_2541_ = l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(v_e_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_);
lean_dec(v_a_2539_);
lean_dec_ref(v_a_2538_);
lean_dec(v_a_2537_);
lean_dec_ref(v_a_2536_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr___lam__0(lean_object* v___y_2542_){
_start:
{
lean_inc_ref(v___y_2542_);
return v___y_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr___lam__0___boxed(lean_object* v___y_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr___lam__0(v___y_2543_);
lean_dec_ref(v___y_2543_);
return v_res_2544_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1(void){
_start:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2546_ = lean_box(0);
v___x_2547_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13));
v___x_2548_ = l_Lean_mkConst(v___x_2547_, v___x_2546_);
return v___x_2548_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__2(void){
_start:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2549_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
v___x_2550_ = l_Lean_mkIntLit(v___x_2549_);
return v___x_2550_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__3(void){
_start:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__2, &l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__2);
v___x_2552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2551_);
return v___x_2552_;
}
}
lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr(lean_object* v_ctx_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_){
_start:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; uint8_t v___x_2561_; 
v___x_2559_ = lean_unsigned_to_nat(0u);
v___x_2560_ = lean_array_get_size(v_ctx_2553_);
v___x_2561_ = lean_nat_dec_lt(v___x_2559_, v___x_2560_);
if (v___x_2561_ == 0)
{
lean_object* v___f_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
lean_dec_ref(v_ctx_2553_);
v___f_2562_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__0));
v___x_2563_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1, &l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1_once, _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1);
v___x_2564_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__3, &l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__3);
v___x_2565_ = l_Lean_RArray_toExpr___redArg(v___x_2563_, v___f_2562_, v___x_2564_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_);
return v___x_2565_;
}
else
{
lean_object* v___f_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; 
v___f_2566_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__0));
v___x_2567_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1, &l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1_once, _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1);
v___x_2568_ = l_Lean_RArray_ofArray___redArg(v_ctx_2553_);
v___x_2569_ = l_Lean_RArray_toExpr___redArg(v___x_2567_, v___f_2566_, v___x_2568_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_);
return v___x_2569_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_Arith_Int_toContextExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_2553_ = stack[0].m_obj;
lean_object* v_a_2554_ = stack[1].m_obj;
lean_object* v_a_2555_ = stack[2].m_obj;
lean_object* v_a_2556_ = stack[3].m_obj;
lean_object* v_a_2557_ = stack[4].m_obj;
lean_object* v_res_2570_;
v_res_2570_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_ctx_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_);
stack->m_obj
 = v_res_2570_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr___boxed(lean_object* v_ctx_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_ctx_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_);
lean_dec(v_a_2575_);
lean_dec_ref(v_a_2574_);
lean_dec(v_a_2573_);
lean_dec_ref(v_a_2572_);
return v_res_2577_;
}
}
lean_object* runtime_initialize_Init_Data_Int_Linear(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_SortExprs(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_IntInstTesters(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_KExprMap(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_RArray(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_LitValues(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
