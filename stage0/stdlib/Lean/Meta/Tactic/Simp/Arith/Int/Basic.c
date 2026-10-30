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
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_denoteExpr___redArg(lean_object* v_ctx_764_, lean_object* v_e_765_){
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
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_denoteExpr___redArg___boxed(lean_object* v_ctx_887_, lean_object* v_e_888_, lean_object* v_a_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v_ctx_887_, v_e_888_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_denoteExpr(lean_object* v_ctx_891_, lean_object* v_e_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v_ctx_891_, v_e_892_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_denoteExpr___boxed(lean_object* v_ctx_899_, lean_object* v_e_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Int_Internal_Linear_Expr_denoteExpr(v_ctx_899_, v_e_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_);
lean_dec(v_a_904_);
lean_dec_ref(v_a_903_);
lean_dec(v_a_902_);
lean_dec_ref(v_a_901_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_denoteExpr_go___redArg(lean_object* v_ctx_907_, lean_object* v_r_908_, lean_object* v_p_909_){
_start:
{
lean_object* v___y_912_; 
if (lean_obj_tag(v_p_909_) == 0)
{
lean_object* v_k_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_934_; 
lean_dec_ref(v_ctx_907_);
v_k_915_ = lean_ctor_get(v_p_909_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v_p_909_);
if (v_isSharedCheck_934_ == 0)
{
v___x_917_ = v_p_909_;
v_isShared_918_ = v_isSharedCheck_934_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_k_915_);
lean_dec(v_p_909_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_934_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_919_; uint8_t v___x_920_; 
v___x_919_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
v___x_920_ = lean_int_dec_eq(v_k_915_, v___x_919_);
if (v___x_920_ == 0)
{
uint8_t v___x_921_; 
lean_del_object(v___x_917_);
v___x_921_ = lean_int_dec_le(v___x_919_, v_k_915_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_922_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12);
v___x_923_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14);
v___x_924_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17);
v___x_925_ = lean_int_neg(v_k_915_);
lean_dec(v_k_915_);
v___x_926_ = l_Int_toNat(v___x_925_);
lean_dec(v___x_925_);
v___x_927_ = l_Lean_instToExprInt_mkNat(v___x_926_);
v___x_928_ = l_Lean_mkApp3(v___x_922_, v___x_923_, v___x_924_, v___x_927_);
v___y_912_ = v___x_928_;
goto v___jp_911_;
}
else
{
lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_929_ = l_Int_toNat(v_k_915_);
lean_dec(v_k_915_);
v___x_930_ = l_Lean_instToExprInt_mkNat(v___x_929_);
v___y_912_ = v___x_930_;
goto v___jp_911_;
}
}
else
{
lean_object* v___x_932_; 
lean_dec(v_k_915_);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v_r_908_);
v___x_932_ = v___x_917_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_r_908_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
else
{
lean_object* v_k_935_; lean_object* v_v_936_; lean_object* v_p_937_; lean_object* v___y_939_; lean_object* v___x_944_; uint8_t v___x_945_; 
v_k_935_ = lean_ctor_get(v_p_909_, 0);
lean_inc(v_k_935_);
v_v_936_ = lean_ctor_get(v_p_909_, 1);
lean_inc(v_v_936_);
v_p_937_ = lean_ctor_get(v_p_909_, 2);
lean_inc_ref(v_p_937_);
lean_dec_ref_known(v_p_909_, 3);
v___x_944_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0);
v___x_945_ = lean_int_dec_eq(v_k_935_, v___x_944_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; uint8_t v___x_947_; 
v___x_946_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
v___x_947_ = lean_int_dec_le(v___x_946_, v_k_935_);
if (v___x_947_ == 0)
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_948_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12);
v___x_949_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14);
v___x_950_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17);
v___x_951_ = lean_int_neg(v_k_935_);
lean_dec(v_k_935_);
v___x_952_ = l_Int_toNat(v___x_951_);
lean_dec(v___x_951_);
v___x_953_ = l_Lean_instToExprInt_mkNat(v___x_952_);
v___x_954_ = l_Lean_mkApp3(v___x_948_, v___x_949_, v___x_950_, v___x_953_);
v___y_939_ = v___x_954_;
goto v___jp_938_;
}
else
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = l_Int_toNat(v_k_935_);
lean_dec(v_k_935_);
v___x_956_ = l_Lean_instToExprInt_mkNat(v___x_955_);
v___y_939_ = v___x_956_;
goto v___jp_938_;
}
}
else
{
lean_object* v___x_957_; lean_object* v___x_958_; 
lean_dec(v_k_935_);
lean_inc_ref(v_ctx_907_);
v___x_957_ = lean_apply_1(v_ctx_907_, v_v_936_);
v___x_958_ = l_Lean_mkIntAdd(v_r_908_, v___x_957_);
v_r_908_ = v___x_958_;
v_p_909_ = v_p_937_;
goto _start;
}
v___jp_938_:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
lean_inc_ref(v_ctx_907_);
v___x_940_ = lean_apply_1(v_ctx_907_, v_v_936_);
v___x_941_ = l_Lean_mkIntMul(v___y_939_, v___x_940_);
v___x_942_ = l_Lean_mkIntAdd(v_r_908_, v___x_941_);
v_r_908_ = v___x_942_;
v_p_909_ = v_p_937_;
goto _start;
}
}
v___jp_911_:
{
lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_913_ = l_Lean_mkIntAdd(v_r_908_, v___y_912_);
v___x_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
return v___x_914_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_denoteExpr_go___redArg___boxed(lean_object* v_ctx_960_, lean_object* v_r_961_, lean_object* v_p_962_, lean_object* v_a_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_denoteExpr_go___redArg(v_ctx_960_, v_r_961_, v_p_962_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_denoteExpr_go(lean_object* v_ctx_965_, lean_object* v_r_966_, lean_object* v_p_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_denoteExpr_go___redArg(v_ctx_965_, v_r_966_, v_p_967_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_denoteExpr_go___boxed(lean_object* v_ctx_974_, lean_object* v_r_975_, lean_object* v_p_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_denoteExpr_go(v_ctx_974_, v_r_975_, v_p_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
lean_dec(v_a_978_);
lean_dec_ref(v_a_977_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr___redArg(lean_object* v_ctx_983_, lean_object* v_p_984_){
_start:
{
if (lean_obj_tag(v_p_984_) == 0)
{
lean_object* v_k_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1007_; 
lean_dec_ref(v_ctx_983_);
v_k_986_ = lean_ctor_get(v_p_984_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v_p_984_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_988_ = v_p_984_;
v_isShared_989_ = v_isSharedCheck_1007_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_k_986_);
lean_dec(v_p_984_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1007_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_990_; uint8_t v___x_991_; 
v___x_990_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
v___x_991_ = lean_int_dec_le(v___x_990_, v_k_986_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_1000_; 
v___x_992_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12);
v___x_993_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14);
v___x_994_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17);
v___x_995_ = lean_int_neg(v_k_986_);
lean_dec(v_k_986_);
v___x_996_ = l_Int_toNat(v___x_995_);
lean_dec(v___x_995_);
v___x_997_ = l_Lean_instToExprInt_mkNat(v___x_996_);
v___x_998_ = l_Lean_mkApp3(v___x_992_, v___x_993_, v___x_994_, v___x_997_);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 0, v___x_998_);
v___x_1000_ = v___x_988_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_998_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
else
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1005_; 
v___x_1002_ = l_Int_toNat(v_k_986_);
lean_dec(v_k_986_);
v___x_1003_ = l_Lean_instToExprInt_mkNat(v___x_1002_);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 0, v___x_1003_);
v___x_1005_ = v___x_988_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_1003_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
else
{
lean_object* v_k_1008_; lean_object* v_v_1009_; lean_object* v_p_1010_; lean_object* v___y_1012_; lean_object* v___x_1016_; uint8_t v___x_1017_; 
v_k_1008_ = lean_ctor_get(v_p_984_, 0);
lean_inc(v_k_1008_);
v_v_1009_ = lean_ctor_get(v_p_984_, 1);
lean_inc(v_v_1009_);
v_p_1010_ = lean_ctor_get(v_p_984_, 2);
lean_inc_ref(v_p_1010_);
lean_dec_ref_known(v_p_984_, 3);
v___x_1016_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0);
v___x_1017_ = lean_int_dec_eq(v_k_1008_, v___x_1016_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; uint8_t v___x_1019_; 
v___x_1018_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
v___x_1019_ = lean_int_dec_le(v___x_1018_, v_k_1008_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1020_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12);
v___x_1021_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14);
v___x_1022_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17);
v___x_1023_ = lean_int_neg(v_k_1008_);
lean_dec(v_k_1008_);
v___x_1024_ = l_Int_toNat(v___x_1023_);
lean_dec(v___x_1023_);
v___x_1025_ = l_Lean_instToExprInt_mkNat(v___x_1024_);
v___x_1026_ = l_Lean_mkApp3(v___x_1020_, v___x_1021_, v___x_1022_, v___x_1025_);
v___y_1012_ = v___x_1026_;
goto v___jp_1011_;
}
else
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = l_Int_toNat(v_k_1008_);
lean_dec(v_k_1008_);
v___x_1028_ = l_Lean_instToExprInt_mkNat(v___x_1027_);
v___y_1012_ = v___x_1028_;
goto v___jp_1011_;
}
}
else
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
lean_dec(v_k_1008_);
lean_inc_ref(v_ctx_983_);
v___x_1029_ = lean_apply_1(v_ctx_983_, v_v_1009_);
v___x_1030_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_denoteExpr_go___redArg(v_ctx_983_, v___x_1029_, v_p_1010_);
return v___x_1030_;
}
v___jp_1011_:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
lean_inc_ref(v_ctx_983_);
v___x_1013_ = lean_apply_1(v_ctx_983_, v_v_1009_);
v___x_1014_ = l_Lean_mkIntMul(v___y_1012_, v___x_1013_);
v___x_1015_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_denoteExpr_go___redArg(v_ctx_983_, v___x_1014_, v_p_1010_);
return v___x_1015_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr___redArg___boxed(lean_object* v_ctx_1031_, lean_object* v_p_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Int_Internal_Linear_Poly_denoteExpr___redArg(v_ctx_1031_, v_p_1032_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr(lean_object* v_ctx_1035_, lean_object* v_p_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_Int_Internal_Linear_Poly_denoteExpr___redArg(v_ctx_1035_, v_p_1036_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr___boxed(lean_object* v_ctx_1043_, lean_object* v_p_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Int_Internal_Linear_Poly_denoteExpr(v_ctx_1043_, v_p_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_);
lean_dec(v_a_1048_);
lean_dec_ref(v_a_1047_);
lean_dec(v_a_1046_);
lean_dec_ref(v_a_1045_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(lean_object* v_e_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_){
_start:
{
lean_object* v___x_1058_; lean_object* v_varMap_1059_; lean_object* v___x_1060_; 
v___x_1058_ = lean_st_ref_get(v_a_1052_);
v_varMap_1059_ = lean_ctor_get(v___x_1058_, 0);
lean_inc_ref(v_varMap_1059_);
lean_dec(v___x_1058_);
lean_inc_ref(v_e_1051_);
v___x_1060_ = l_Lean_Meta_KExprMap_find_x3f___redArg(v_varMap_1059_, v_e_1051_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_);
lean_dec_ref(v_varMap_1059_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1109_; 
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1063_ = v___x_1060_;
v_isShared_1064_ = v_isSharedCheck_1109_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1060_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1109_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
if (lean_obj_tag(v_a_1061_) == 1)
{
lean_object* v_val_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1075_; 
lean_dec_ref(v_e_1051_);
v_val_1065_ = lean_ctor_get(v_a_1061_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v_a_1061_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1067_ = v_a_1061_;
v_isShared_1068_ = v_isSharedCheck_1075_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_val_1065_);
lean_dec(v_a_1061_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1075_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1068_ == 0)
{
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_val_1065_);
v___x_1070_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
lean_object* v___x_1072_; 
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 0, v___x_1070_);
v___x_1072_ = v___x_1063_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1070_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
else
{
lean_object* v___x_1076_; lean_object* v_vars_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v_varMap_1080_; lean_object* v_vars_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1108_; 
lean_del_object(v___x_1063_);
lean_dec(v_a_1061_);
v___x_1076_ = lean_st_ref_get(v_a_1052_);
v_vars_1077_ = lean_ctor_get(v___x_1076_, 1);
lean_inc_ref(v_vars_1077_);
lean_dec(v___x_1076_);
v___x_1078_ = lean_array_get_size(v_vars_1077_);
lean_dec_ref(v_vars_1077_);
v___x_1079_ = lean_st_ref_get(v_a_1052_);
v_varMap_1080_ = lean_ctor_get(v___x_1079_, 0);
v_vars_1081_ = lean_ctor_get(v___x_1079_, 1);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1083_ = v___x_1079_;
v_isShared_1084_ = v_isSharedCheck_1108_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_vars_1081_);
lean_inc(v_varMap_1080_);
lean_dec(v___x_1079_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1108_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1085_; 
lean_inc_ref(v_e_1051_);
v___x_1085_ = l_Lean_Meta_KExprMap_insert___redArg(v_varMap_1080_, v_e_1051_, v___x_1078_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1099_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1088_ = v___x_1085_;
v_isShared_1089_ = v_isSharedCheck_1099_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1085_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1099_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1090_; lean_object* v___x_1092_; 
v___x_1090_ = lean_array_push(v_vars_1081_, v_e_1051_);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 1, v___x_1090_);
lean_ctor_set(v___x_1083_, 0, v_a_1086_);
v___x_1092_ = v___x_1083_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1086_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v___x_1090_);
v___x_1092_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1096_; 
v___x_1093_ = lean_st_ref_swap(v_a_1052_, v___x_1092_);
lean_dec(v___x_1093_);
v___x_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1078_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v___x_1094_);
v___x_1096_ = v___x_1088_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1094_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
lean_del_object(v___x_1083_);
lean_dec_ref(v_vars_1081_);
lean_dec_ref(v_e_1051_);
v_a_1100_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1085_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1085_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1117_; 
lean_dec_ref(v_e_1051_);
v_a_1110_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1112_ = v___x_1060_;
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1060_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1110_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar___boxed(lean_object* v_e_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_);
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
lean_dec(v_a_1121_);
lean_dec_ref(v_a_1120_);
lean_dec(v_a_1119_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit(lean_object* v_e_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_){
_start:
{
lean_object* v_a_1179_; lean_object* v_b_1180_; lean_object* v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1185_; lean_object* v___x_1229_; 
lean_inc_ref(v_e_1171_);
v___x_1229_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1171_, v_a_1174_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v_a_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; 
v_a_1230_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_a_1230_);
lean_dec_ref_known(v___x_1229_, 1);
v___x_1231_ = l_Lean_Expr_cleanupAnnotations(v_a_1230_);
lean_dec(v_a_1230_);
v___x_1232_ = l_Lean_Expr_isApp(v___x_1231_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1233_; 
lean_dec_ref(v___x_1231_);
v___x_1233_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1233_;
}
else
{
lean_object* v_arg_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; uint8_t v___x_1237_; 
v_arg_1234_ = lean_ctor_get(v___x_1231_, 1);
lean_inc_ref(v_arg_1234_);
v___x_1235_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1231_);
lean_dec_ref(v___x_1231_);
v___x_1236_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__0));
v___x_1237_ = l_Lean_Expr_isConstOf(v___x_1235_, v___x_1236_);
if (v___x_1237_ == 0)
{
uint8_t v___x_1238_; 
v___x_1238_ = l_Lean_Expr_isApp(v___x_1235_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; 
lean_dec_ref(v___x_1235_);
lean_dec_ref(v_arg_1234_);
v___x_1239_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1239_;
}
else
{
lean_object* v_arg_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; uint8_t v___x_1243_; 
v_arg_1240_ = lean_ctor_get(v___x_1235_, 1);
lean_inc_ref(v_arg_1240_);
v___x_1241_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1235_);
lean_dec_ref(v___x_1235_);
v___x_1242_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__2));
v___x_1243_ = l_Lean_Expr_isConstOf(v___x_1241_, v___x_1242_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; uint8_t v___x_1245_; 
v___x_1244_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__3));
v___x_1245_ = l_Lean_Expr_isConstOf(v___x_1241_, v___x_1244_);
if (v___x_1245_ == 0)
{
lean_object* v___x_1246_; uint8_t v___x_1247_; 
v___x_1246_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__4));
v___x_1247_ = l_Lean_Expr_isConstOf(v___x_1241_, v___x_1246_);
if (v___x_1247_ == 0)
{
uint8_t v___x_1248_; 
v___x_1248_ = l_Lean_Expr_isApp(v___x_1241_);
if (v___x_1248_ == 0)
{
lean_object* v___x_1249_; 
lean_dec_ref(v___x_1241_);
lean_dec_ref(v_arg_1240_);
lean_dec_ref(v_arg_1234_);
v___x_1249_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1249_;
}
else
{
lean_object* v___x_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; 
v___x_1250_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1241_);
v___x_1251_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__9));
v___x_1252_ = l_Lean_Expr_isConstOf(v___x_1250_, v___x_1251_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; uint8_t v___x_1254_; 
v___x_1253_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__7));
v___x_1254_ = l_Lean_Expr_isConstOf(v___x_1250_, v___x_1253_);
if (v___x_1254_ == 0)
{
uint8_t v___x_1255_; 
v___x_1255_ = l_Lean_Expr_isApp(v___x_1250_);
if (v___x_1255_ == 0)
{
lean_object* v___x_1256_; 
lean_dec_ref(v___x_1250_);
lean_dec_ref(v___x_1241_);
lean_dec_ref(v_arg_1240_);
lean_dec_ref(v_arg_1234_);
v___x_1256_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1256_;
}
else
{
lean_object* v_arg_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; uint8_t v___x_1260_; 
v_arg_1257_ = lean_ctor_get(v___x_1241_, 1);
lean_inc_ref(v_arg_1257_);
lean_dec_ref(v___x_1241_);
v___x_1258_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1250_);
lean_dec_ref(v___x_1250_);
v___x_1259_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__9));
v___x_1260_ = l_Lean_Expr_isConstOf(v___x_1258_, v___x_1259_);
if (v___x_1260_ == 0)
{
lean_object* v___x_1261_; uint8_t v___x_1262_; 
v___x_1261_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__11));
v___x_1262_ = l_Lean_Expr_isConstOf(v___x_1258_, v___x_1261_);
if (v___x_1262_ == 0)
{
lean_object* v___x_1263_; uint8_t v___x_1264_; 
v___x_1263_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__13));
v___x_1264_ = l_Lean_Expr_isConstOf(v___x_1258_, v___x_1263_);
if (v___x_1264_ == 0)
{
uint8_t v___x_1265_; 
v___x_1265_ = l_Lean_Expr_isApp(v___x_1258_);
if (v___x_1265_ == 0)
{
lean_object* v___x_1266_; 
lean_dec_ref(v___x_1258_);
lean_dec_ref(v_arg_1257_);
lean_dec_ref(v_arg_1240_);
lean_dec_ref(v_arg_1234_);
v___x_1266_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1266_;
}
else
{
lean_object* v___x_1267_; uint8_t v___x_1268_; 
v___x_1267_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1258_);
lean_dec_ref(v___x_1258_);
v___x_1268_ = l_Lean_Expr_isApp(v___x_1267_);
if (v___x_1268_ == 0)
{
lean_object* v___x_1269_; 
lean_dec_ref(v___x_1267_);
lean_dec_ref(v_arg_1257_);
lean_dec_ref(v_arg_1240_);
lean_dec_ref(v_arg_1234_);
v___x_1269_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1269_;
}
else
{
lean_object* v___x_1270_; lean_object* v___x_1271_; uint8_t v___x_1272_; 
v___x_1270_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1267_);
lean_dec_ref(v___x_1267_);
v___x_1271_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__16));
v___x_1272_ = l_Lean_Expr_isConstOf(v___x_1270_, v___x_1271_);
if (v___x_1272_ == 0)
{
lean_object* v___x_1273_; uint8_t v___x_1274_; 
v___x_1273_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__19));
v___x_1274_ = l_Lean_Expr_isConstOf(v___x_1270_, v___x_1273_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1275_; uint8_t v___x_1276_; 
v___x_1275_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__22));
v___x_1276_ = l_Lean_Expr_isConstOf(v___x_1270_, v___x_1275_);
lean_dec_ref(v___x_1270_);
if (v___x_1276_ == 0)
{
lean_object* v___x_1277_; 
lean_dec_ref(v_arg_1257_);
lean_dec_ref(v_arg_1240_);
lean_dec_ref(v_arg_1234_);
v___x_1277_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1277_;
}
else
{
lean_object* v___x_1278_; 
v___x_1278_ = l_Lean_Meta_DefEq_isInstHAddInt(v_arg_1257_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; uint8_t v___x_1280_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1279_);
lean_dec_ref_known(v___x_1278_, 1);
v___x_1280_ = lean_unbox(v_a_1279_);
lean_dec(v_a_1279_);
if (v___x_1280_ == 0)
{
lean_object* v___x_1281_; 
lean_dec_ref(v_arg_1240_);
lean_dec_ref(v_arg_1234_);
v___x_1281_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1281_;
}
else
{
lean_object* v___x_1282_; 
lean_dec_ref(v_e_1171_);
v___x_1282_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1240_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; lean_object* v___x_1284_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_a_1283_);
lean_dec_ref_known(v___x_1282_, 1);
v___x_1284_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1234_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1293_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1287_ = v___x_1284_;
v_isShared_1288_ = v_isSharedCheck_1293_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1284_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1293_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1289_; lean_object* v___x_1291_; 
v___x_1289_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1289_, 0, v_a_1283_);
lean_ctor_set(v___x_1289_, 1, v_a_1285_);
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 0, v___x_1289_);
v___x_1291_ = v___x_1287_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1289_);
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
lean_dec(v_a_1283_);
return v___x_1284_;
}
}
else
{
lean_dec_ref(v_arg_1234_);
return v___x_1282_;
}
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
lean_dec_ref(v_arg_1240_);
lean_dec_ref(v_arg_1234_);
lean_dec_ref(v_e_1171_);
v_a_1294_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1278_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1278_);
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
else
{
lean_object* v___x_1302_; 
lean_dec_ref(v___x_1270_);
v___x_1302_ = l_Lean_Meta_DefEq_isInstHSubInt(v_arg_1257_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v_a_1303_; uint8_t v___x_1304_; 
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_a_1303_);
lean_dec_ref_known(v___x_1302_, 1);
v___x_1304_ = lean_unbox(v_a_1303_);
lean_dec(v_a_1303_);
if (v___x_1304_ == 0)
{
lean_object* v___x_1305_; 
lean_dec_ref(v_arg_1240_);
lean_dec_ref(v_arg_1234_);
v___x_1305_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1305_;
}
else
{
lean_object* v___x_1306_; 
lean_dec_ref(v_e_1171_);
v___x_1306_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1240_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_a_1307_; lean_object* v___x_1308_; 
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_a_1307_);
lean_dec_ref_known(v___x_1306_, 1);
v___x_1308_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1234_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1317_; 
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1311_ = v___x_1308_;
v_isShared_1312_ = v_isSharedCheck_1317_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1308_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1317_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1313_; lean_object* v___x_1315_; 
v___x_1313_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1313_, 0, v_a_1307_);
lean_ctor_set(v___x_1313_, 1, v_a_1309_);
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 0, v___x_1313_);
v___x_1315_ = v___x_1311_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1313_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
else
{
lean_dec(v_a_1307_);
return v___x_1308_;
}
}
else
{
lean_dec_ref(v_arg_1234_);
return v___x_1306_;
}
}
}
else
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1325_; 
lean_dec_ref(v_arg_1240_);
lean_dec_ref(v_arg_1234_);
lean_dec_ref(v_e_1171_);
v_a_1318_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1320_ = v___x_1302_;
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1302_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1323_; 
if (v_isShared_1321_ == 0)
{
v___x_1323_ = v___x_1320_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1318_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
}
else
{
lean_object* v___x_1326_; 
lean_dec_ref(v___x_1270_);
v___x_1326_ = l_Lean_Meta_DefEq_isInstHMulInt(v_arg_1257_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v_a_1327_; uint8_t v___x_1328_; 
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
lean_inc(v_a_1327_);
lean_dec_ref_known(v___x_1326_, 1);
v___x_1328_ = lean_unbox(v_a_1327_);
lean_dec(v_a_1327_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1329_; 
lean_dec_ref(v_arg_1240_);
lean_dec_ref(v_arg_1234_);
v___x_1329_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1329_;
}
else
{
v_a_1179_ = v_arg_1240_;
v_b_1180_ = v_arg_1234_;
v___y_1181_ = v_a_1172_;
v___y_1182_ = v_a_1173_;
v___y_1183_ = v_a_1174_;
v___y_1184_ = v_a_1175_;
v___y_1185_ = v_a_1176_;
goto v___jp_1178_;
}
}
else
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
lean_dec_ref(v_arg_1240_);
lean_dec_ref(v_arg_1234_);
lean_dec_ref(v_e_1171_);
v_a_1330_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1332_ = v___x_1326_;
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1326_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
if (v_isShared_1333_ == 0)
{
v___x_1335_ = v___x_1332_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1330_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1338_; 
lean_dec_ref(v___x_1258_);
v___x_1338_ = l_Lean_Meta_DefEq_isInstAddInt(v_arg_1257_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v_a_1339_; uint8_t v___x_1340_; 
v_a_1339_ = lean_ctor_get(v___x_1338_, 0);
lean_inc(v_a_1339_);
lean_dec_ref_known(v___x_1338_, 1);
v___x_1340_ = lean_unbox(v_a_1339_);
lean_dec(v_a_1339_);
if (v___x_1340_ == 0)
{
lean_object* v___x_1341_; 
lean_dec_ref(v_arg_1240_);
lean_dec_ref(v_arg_1234_);
v___x_1341_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1341_;
}
else
{
lean_object* v___x_1342_; 
lean_dec_ref(v_e_1171_);
v___x_1342_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1240_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_a_1343_; lean_object* v___x_1344_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
lean_inc(v_a_1343_);
lean_dec_ref_known(v___x_1342_, 1);
v___x_1344_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1234_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1353_; 
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1347_ = v___x_1344_;
v_isShared_1348_ = v_isSharedCheck_1353_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1344_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1353_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1349_; lean_object* v___x_1351_; 
v___x_1349_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1349_, 0, v_a_1343_);
lean_ctor_set(v___x_1349_, 1, v_a_1345_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 0, v___x_1349_);
v___x_1351_ = v___x_1347_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___x_1349_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
else
{
lean_dec(v_a_1343_);
return v___x_1344_;
}
}
else
{
lean_dec_ref(v_arg_1234_);
return v___x_1342_;
}
}
}
else
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
lean_dec_ref(v_arg_1240_);
lean_dec_ref(v_arg_1234_);
lean_dec_ref(v_e_1171_);
v_a_1354_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1356_ = v___x_1338_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1338_);
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
else
{
lean_object* v___x_1362_; 
lean_dec_ref(v___x_1258_);
v___x_1362_ = l_Lean_Meta_DefEq_isInstSubInt(v_arg_1257_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v_a_1363_; uint8_t v___x_1364_; 
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_a_1363_);
lean_dec_ref_known(v___x_1362_, 1);
v___x_1364_ = lean_unbox(v_a_1363_);
lean_dec(v_a_1363_);
if (v___x_1364_ == 0)
{
lean_object* v___x_1365_; 
lean_dec_ref(v_arg_1240_);
lean_dec_ref(v_arg_1234_);
v___x_1365_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1365_;
}
else
{
lean_object* v___x_1366_; 
lean_dec_ref(v_e_1171_);
v___x_1366_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1240_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v_a_1367_; lean_object* v___x_1368_; 
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_a_1367_);
lean_dec_ref_known(v___x_1366_, 1);
v___x_1368_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1234_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1377_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1371_ = v___x_1368_;
v_isShared_1372_ = v_isSharedCheck_1377_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1368_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1377_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1373_; lean_object* v___x_1375_; 
v___x_1373_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1373_, 0, v_a_1367_);
lean_ctor_set(v___x_1373_, 1, v_a_1369_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v___x_1373_);
v___x_1375_ = v___x_1371_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1373_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
else
{
lean_dec(v_a_1367_);
return v___x_1368_;
}
}
else
{
lean_dec_ref(v_arg_1234_);
return v___x_1366_;
}
}
}
else
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1385_; 
lean_dec_ref(v_arg_1240_);
lean_dec_ref(v_arg_1234_);
lean_dec_ref(v_e_1171_);
v_a_1378_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1380_ = v___x_1362_;
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1362_);
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
}
else
{
lean_object* v___x_1386_; 
lean_dec_ref(v___x_1258_);
v___x_1386_ = l_Lean_Meta_DefEq_isInstMulInt(v_arg_1257_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; uint8_t v___x_1388_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_a_1387_);
lean_dec_ref_known(v___x_1386_, 1);
v___x_1388_ = lean_unbox(v_a_1387_);
lean_dec(v_a_1387_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; 
lean_dec_ref(v_arg_1240_);
lean_dec_ref(v_arg_1234_);
v___x_1389_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1389_;
}
else
{
v_a_1179_ = v_arg_1240_;
v_b_1180_ = v_arg_1234_;
v___y_1181_ = v_a_1172_;
v___y_1182_ = v_a_1173_;
v___y_1183_ = v_a_1174_;
v___y_1184_ = v_a_1175_;
v___y_1185_ = v_a_1176_;
goto v___jp_1178_;
}
}
else
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1397_; 
lean_dec_ref(v_arg_1240_);
lean_dec_ref(v_arg_1234_);
lean_dec_ref(v_e_1171_);
v_a_1390_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1392_ = v___x_1386_;
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1386_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1395_; 
if (v_isShared_1393_ == 0)
{
v___x_1395_ = v___x_1392_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_a_1390_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
}
}
else
{
lean_object* v___x_1398_; 
lean_dec_ref(v___x_1250_);
lean_dec_ref(v___x_1241_);
lean_dec_ref(v_arg_1240_);
lean_dec_ref(v_arg_1234_);
lean_inc_ref(v_e_1171_);
v___x_1398_ = l_Lean_Meta_getIntValue_x3f(v_e_1171_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1415_; 
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1401_ = v___x_1398_;
v_isShared_1402_ = v_isSharedCheck_1415_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1398_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1415_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
if (lean_obj_tag(v_a_1399_) == 1)
{
lean_object* v_val_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1413_; 
lean_dec_ref(v_e_1171_);
v_val_1403_ = lean_ctor_get(v_a_1399_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v_a_1399_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1405_ = v_a_1399_;
v_isShared_1406_ = v_isSharedCheck_1413_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_val_1403_);
lean_dec(v_a_1399_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1413_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1408_; 
if (v_isShared_1406_ == 0)
{
lean_ctor_set_tag(v___x_1405_, 0);
v___x_1408_ = v___x_1405_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_val_1403_);
v___x_1408_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
lean_object* v___x_1410_; 
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 0, v___x_1408_);
v___x_1410_ = v___x_1401_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___x_1408_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
else
{
lean_object* v___x_1414_; 
lean_del_object(v___x_1401_);
lean_dec(v_a_1399_);
v___x_1414_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1414_;
}
}
}
else
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
lean_dec_ref(v_e_1171_);
v_a_1416_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1418_ = v___x_1398_;
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1398_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_a_1416_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
}
else
{
lean_object* v___x_1424_; 
lean_dec_ref(v___x_1250_);
lean_dec_ref(v___x_1241_);
v___x_1424_ = l_Lean_Meta_DefEq_isInstNegInt(v_arg_1240_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_a_1425_; uint8_t v___x_1426_; 
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_a_1425_);
lean_dec_ref_known(v___x_1424_, 1);
v___x_1426_ = lean_unbox(v_a_1425_);
lean_dec(v_a_1425_);
if (v___x_1426_ == 0)
{
lean_object* v___x_1427_; 
lean_dec_ref(v_arg_1234_);
v___x_1427_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
return v___x_1427_;
}
else
{
lean_object* v___x_1428_; 
v___x_1428_ = l_Lean_Meta_getIntValue_x3f(v_e_1171_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1454_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1431_ = v___x_1428_;
v_isShared_1432_ = v_isSharedCheck_1454_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1428_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1454_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
if (lean_obj_tag(v_a_1429_) == 1)
{
lean_object* v_val_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1443_; 
lean_dec_ref(v_arg_1234_);
v_val_1433_ = lean_ctor_get(v_a_1429_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v_a_1429_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1435_ = v_a_1429_;
v_isShared_1436_ = v_isSharedCheck_1443_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_val_1433_);
lean_dec(v_a_1429_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1443_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
lean_ctor_set_tag(v___x_1435_, 0);
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_val_1433_);
v___x_1438_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
lean_object* v___x_1440_; 
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 0, v___x_1438_);
v___x_1440_ = v___x_1431_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1438_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
}
else
{
lean_object* v___x_1444_; 
lean_del_object(v___x_1431_);
lean_dec(v_a_1429_);
v___x_1444_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1234_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1453_; 
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1447_ = v___x_1444_;
v_isShared_1448_ = v_isSharedCheck_1453_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_dec(v___x_1444_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1453_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1449_; lean_object* v___x_1451_; 
v___x_1449_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1449_, 0, v_a_1445_);
if (v_isShared_1448_ == 0)
{
lean_ctor_set(v___x_1447_, 0, v___x_1449_);
v___x_1451_ = v___x_1447_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1449_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
else
{
return v___x_1444_;
}
}
}
}
else
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1462_; 
lean_dec_ref(v_arg_1234_);
v_a_1455_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1457_ = v___x_1428_;
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1428_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1460_; 
if (v_isShared_1458_ == 0)
{
v___x_1460_ = v___x_1457_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_a_1455_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
}
else
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
lean_dec_ref(v_arg_1234_);
lean_dec_ref(v_e_1171_);
v_a_1463_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1465_ = v___x_1424_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1424_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1463_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
}
}
else
{
lean_object* v___x_1471_; 
lean_dec_ref(v___x_1241_);
lean_dec_ref(v_e_1171_);
v___x_1471_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1240_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v_a_1472_; lean_object* v___x_1473_; 
v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
lean_inc(v_a_1472_);
lean_dec_ref_known(v___x_1471_, 1);
v___x_1473_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1234_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1482_; 
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1476_ = v___x_1473_;
v_isShared_1477_ = v_isSharedCheck_1482_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1473_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1482_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1478_; lean_object* v___x_1480_; 
v___x_1478_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1478_, 0, v_a_1472_);
lean_ctor_set(v___x_1478_, 1, v_a_1474_);
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 0, v___x_1478_);
v___x_1480_ = v___x_1476_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1478_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
else
{
lean_dec(v_a_1472_);
return v___x_1473_;
}
}
else
{
lean_dec_ref(v_arg_1234_);
return v___x_1471_;
}
}
}
else
{
lean_object* v___x_1483_; 
lean_dec_ref(v___x_1241_);
lean_dec_ref(v_e_1171_);
v___x_1483_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1240_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1484_; lean_object* v___x_1485_; 
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_a_1484_);
lean_dec_ref_known(v___x_1483_, 1);
v___x_1485_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1234_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1494_; 
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1488_ = v___x_1485_;
v_isShared_1489_ = v_isSharedCheck_1494_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1485_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1494_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1490_; lean_object* v___x_1492_; 
v___x_1490_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1490_, 0, v_a_1484_);
lean_ctor_set(v___x_1490_, 1, v_a_1486_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 0, v___x_1490_);
v___x_1492_ = v___x_1488_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1490_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
else
{
lean_dec(v_a_1484_);
return v___x_1485_;
}
}
else
{
lean_dec_ref(v_arg_1234_);
return v___x_1483_;
}
}
}
else
{
lean_dec_ref(v___x_1241_);
v_a_1179_ = v_arg_1240_;
v_b_1180_ = v_arg_1234_;
v___y_1181_ = v_a_1172_;
v___y_1182_ = v_a_1173_;
v___y_1183_ = v_a_1174_;
v___y_1184_ = v_a_1175_;
v___y_1185_ = v_a_1176_;
goto v___jp_1178_;
}
}
}
else
{
lean_object* v___x_1495_; 
lean_dec_ref(v___x_1235_);
lean_dec_ref(v_e_1171_);
v___x_1495_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1234_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1504_; 
v_a_1496_ = lean_ctor_get(v___x_1495_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1498_ = v___x_1495_;
v_isShared_1499_ = v_isSharedCheck_1504_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1495_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1504_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1500_; lean_object* v___x_1502_; 
v___x_1500_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1500_, 0, v_a_1496_);
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 0, v___x_1500_);
v___x_1502_ = v___x_1498_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v___x_1500_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
else
{
return v___x_1495_;
}
}
}
}
else
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1512_; 
lean_dec_ref(v_e_1171_);
v_a_1505_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1507_ = v___x_1229_;
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v___x_1229_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1510_; 
if (v_isShared_1508_ == 0)
{
v___x_1510_ = v___x_1507_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_a_1505_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
v___jp_1178_:
{
lean_object* v___x_1186_; 
lean_inc_ref(v_a_1179_);
v___x_1186_ = l_Lean_Meta_getIntValue_x3f(v_a_1179_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_a_1187_);
lean_dec_ref_known(v___x_1186_, 1);
if (lean_obj_tag(v_a_1187_) == 0)
{
lean_object* v___x_1188_; 
v___x_1188_ = l_Lean_Meta_getIntValue_x3f(v_b_1180_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v_a_1189_; 
v_a_1189_ = lean_ctor_get(v___x_1188_, 0);
lean_inc(v_a_1189_);
lean_dec_ref_known(v___x_1188_, 1);
if (lean_obj_tag(v_a_1189_) == 0)
{
lean_object* v___x_1190_; 
lean_dec_ref(v_a_1179_);
v___x_1190_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1171_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
return v___x_1190_;
}
else
{
lean_object* v_val_1191_; lean_object* v___x_1192_; 
lean_dec_ref(v_e_1171_);
v_val_1191_ = lean_ctor_get(v_a_1189_, 0);
lean_inc(v_val_1191_);
lean_dec_ref_known(v_a_1189_, 1);
v___x_1192_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_a_1179_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1201_; 
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1195_ = v___x_1192_;
v_isShared_1196_ = v_isSharedCheck_1201_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1192_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1201_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1197_; lean_object* v___x_1199_; 
v___x_1197_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1197_, 0, v_a_1193_);
lean_ctor_set(v___x_1197_, 1, v_val_1191_);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 0, v___x_1197_);
v___x_1199_ = v___x_1195_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1197_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
else
{
lean_dec(v_val_1191_);
return v___x_1192_;
}
}
}
else
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1209_; 
lean_dec_ref(v_a_1179_);
lean_dec_ref(v_e_1171_);
v_a_1202_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1204_ = v___x_1188_;
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1188_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1207_; 
if (v_isShared_1205_ == 0)
{
v___x_1207_ = v___x_1204_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_a_1202_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
else
{
lean_object* v_val_1210_; lean_object* v___x_1211_; 
lean_dec_ref(v_a_1179_);
lean_dec_ref(v_e_1171_);
v_val_1210_ = lean_ctor_get(v_a_1187_, 0);
lean_inc(v_val_1210_);
lean_dec_ref_known(v_a_1187_, 1);
v___x_1211_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_b_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1220_; 
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1214_ = v___x_1211_;
v_isShared_1215_ = v_isSharedCheck_1220_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1211_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1220_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1216_; lean_object* v___x_1218_; 
v___x_1216_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1216_, 0, v_val_1210_);
lean_ctor_set(v___x_1216_, 1, v_a_1212_);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v___x_1216_);
v___x_1218_ = v___x_1214_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1216_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
else
{
lean_dec(v_val_1210_);
return v___x_1211_;
}
}
}
else
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
lean_dec_ref(v_b_1180_);
lean_dec_ref(v_a_1179_);
lean_dec_ref(v_e_1171_);
v_a_1221_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v___x_1186_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1186_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1221_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(lean_object* v_e_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_){
_start:
{
switch(lean_obj_tag(v_e_1513_))
{
case 10:
{
lean_object* v_expr_1520_; 
v_expr_1520_ = lean_ctor_get(v_e_1513_, 1);
lean_inc_ref(v_expr_1520_);
lean_dec_ref_known(v_e_1513_, 2);
v_e_1513_ = v_expr_1520_;
goto _start;
}
case 5:
{
lean_object* v___x_1522_; 
v___x_1522_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit(v_e_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
return v___x_1522_;
}
case 2:
{
lean_object* v___x_1523_; 
v___x_1523_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit(v_e_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
return v___x_1523_;
}
default: 
{
lean_object* v___x_1524_; 
v___x_1524_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
return v___x_1524_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr___boxed(lean_object* v_e_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_e_1525_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_);
lean_dec(v_a_1530_);
lean_dec_ref(v_a_1529_);
lean_dec(v_a_1528_);
lean_dec_ref(v_a_1527_);
lean_dec(v_a_1526_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___boxed(lean_object* v_e_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit(v_e_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_);
lean_dec(v_a_1538_);
lean_dec_ref(v_a_1537_);
lean_dec(v_a_1536_);
lean_dec_ref(v_a_1535_);
lean_dec(v_a_1534_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f(lean_object* v_e_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1544_, v_a_1547_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; lean_object* v___x_1556_; uint8_t v___x_1557_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1555_);
lean_dec_ref_known(v___x_1554_, 1);
v___x_1556_ = l_Lean_Expr_cleanupAnnotations(v_a_1555_);
lean_dec(v_a_1555_);
v___x_1557_ = l_Lean_Expr_isApp(v___x_1556_);
if (v___x_1557_ == 0)
{
lean_dec_ref(v___x_1556_);
goto v___jp_1551_;
}
else
{
lean_object* v___x_1558_; uint8_t v___x_1559_; 
v___x_1558_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1556_);
v___x_1559_ = l_Lean_Expr_isApp(v___x_1558_);
if (v___x_1559_ == 0)
{
lean_dec_ref(v___x_1558_);
lean_dec_ref(v___x_1556_);
goto v___jp_1551_;
}
else
{
lean_object* v___x_1560_; uint8_t v___x_1561_; 
v___x_1560_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1558_);
v___x_1561_ = l_Lean_Expr_isApp(v___x_1560_);
if (v___x_1561_ == 0)
{
lean_dec_ref(v___x_1560_);
lean_dec_ref(v___x_1558_);
lean_dec_ref(v___x_1556_);
goto v___jp_1551_;
}
else
{
lean_object* v___x_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; 
v___x_1562_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1560_);
v___x_1563_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___closed__1));
v___x_1564_ = l_Lean_Expr_isConstOf(v___x_1562_, v___x_1563_);
lean_dec_ref(v___x_1562_);
if (v___x_1564_ == 0)
{
lean_dec_ref(v___x_1560_);
lean_dec_ref(v___x_1558_);
lean_dec_ref(v___x_1556_);
goto v___jp_1551_;
}
else
{
lean_object* v_arg_1565_; lean_object* v_arg_1566_; lean_object* v_arg_1567_; lean_object* v___x_1568_; 
v_arg_1565_ = lean_ctor_get(v___x_1556_, 1);
lean_inc_ref(v_arg_1565_);
lean_dec_ref(v___x_1556_);
v_arg_1566_ = lean_ctor_get(v___x_1558_, 1);
lean_inc_ref(v_arg_1566_);
lean_dec_ref(v___x_1558_);
v_arg_1567_ = lean_ctor_get(v___x_1560_, 1);
lean_inc_ref(v_arg_1567_);
lean_dec_ref(v___x_1560_);
v___x_1568_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1567_, v_a_1547_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1626_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1571_ = v___x_1568_;
v_isShared_1572_ = v_isSharedCheck_1626_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1568_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1626_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; uint8_t v___x_1575_; 
v___x_1573_ = l_Lean_Expr_cleanupAnnotations(v_a_1569_);
lean_dec(v_a_1569_);
v___x_1574_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13));
v___x_1575_ = l_Lean_Expr_isConstOf(v___x_1573_, v___x_1574_);
lean_dec_ref(v___x_1573_);
if (v___x_1575_ == 0)
{
lean_object* v___x_1576_; lean_object* v___x_1578_; 
lean_dec_ref(v_arg_1566_);
lean_dec_ref(v_arg_1565_);
v___x_1576_ = lean_box(0);
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 0, v___x_1576_);
v___x_1578_ = v___x_1571_;
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
else
{
lean_object* v___x_1580_; 
lean_del_object(v___x_1571_);
v___x_1580_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1566_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1617_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1583_ = v___x_1580_;
v_isShared_1584_ = v_isSharedCheck_1617_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1580_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1617_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1585_; 
v___x_1585_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1565_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1608_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1588_ = v___x_1585_;
v_isShared_1589_ = v_isSharedCheck_1608_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1585_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1608_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
switch(lean_obj_tag(v_a_1581_))
{
case 1:
{
switch(lean_obj_tag(v_a_1586_))
{
case 1:
{
lean_object* v___x_1596_; lean_object* v___x_1598_; 
lean_dec_ref_known(v_a_1586_, 1);
lean_dec_ref_known(v_a_1581_, 1);
lean_del_object(v___x_1588_);
v___x_1596_ = lean_box(0);
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 0, v___x_1596_);
v___x_1598_ = v___x_1583_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1596_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
case 0:
{
lean_object* v___x_1600_; lean_object* v___x_1602_; 
lean_dec_ref_known(v_a_1586_, 1);
lean_dec_ref_known(v_a_1581_, 1);
lean_del_object(v___x_1588_);
v___x_1600_ = lean_box(0);
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 0, v___x_1600_);
v___x_1602_ = v___x_1583_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1600_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
default: 
{
lean_del_object(v___x_1583_);
goto v___jp_1590_;
}
}
}
case 0:
{
if (lean_obj_tag(v_a_1586_) == 1)
{
lean_object* v___x_1604_; lean_object* v___x_1606_; 
lean_dec_ref_known(v_a_1586_, 1);
lean_dec_ref_known(v_a_1581_, 1);
lean_del_object(v___x_1588_);
v___x_1604_ = lean_box(0);
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 0, v___x_1604_);
v___x_1606_ = v___x_1583_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v___x_1604_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
else
{
lean_del_object(v___x_1583_);
goto v___jp_1590_;
}
}
default: 
{
lean_del_object(v___x_1583_);
goto v___jp_1590_;
}
}
v___jp_1590_:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1594_; 
v___x_1591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1591_, 0, v_a_1581_);
lean_ctor_set(v___x_1591_, 1, v_a_1586_);
v___x_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1591_);
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 0, v___x_1592_);
v___x_1594_ = v___x_1588_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1592_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
else
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1616_; 
lean_del_object(v___x_1583_);
lean_dec(v_a_1581_);
v_a_1609_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1611_ = v___x_1585_;
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1585_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1614_; 
if (v_isShared_1612_ == 0)
{
v___x_1614_ = v___x_1611_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1609_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
}
}
else
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1625_; 
lean_dec_ref(v_arg_1565_);
v_a_1618_ = lean_ctor_get(v___x_1580_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1620_ = v___x_1580_;
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1580_);
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
}
else
{
lean_object* v_a_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1634_; 
lean_dec_ref(v_arg_1566_);
lean_dec_ref(v_arg_1565_);
v_a_1627_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1629_ = v___x_1568_;
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_a_1627_);
lean_dec(v___x_1568_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1632_; 
if (v_isShared_1630_ == 0)
{
v___x_1632_ = v___x_1629_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_a_1627_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
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
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1642_; 
v_a_1635_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1637_ = v___x_1554_;
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1554_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1640_; 
if (v_isShared_1638_ == 0)
{
v___x_1640_ = v___x_1637_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_a_1635_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
}
v___jp_1551_:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1552_ = lean_box(0);
v___x_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1552_);
return v___x_1553_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___boxed(lean_object* v_e_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f(v_e_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_);
lean_dec(v_a_1648_);
lean_dec_ref(v_a_1647_);
lean_dec(v_a_1646_);
lean_dec_ref(v_a_1645_);
lean_dec(v_a_1644_);
return v_res_1650_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14(void){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1677_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0);
v___x_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1677_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f(lean_object* v_e_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_){
_start:
{
lean_object* v___x_1689_; 
v___x_1689_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1679_, v_a_1682_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v_a_1690_; lean_object* v___x_1691_; uint8_t v___x_1692_; 
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
lean_inc(v_a_1690_);
lean_dec_ref_known(v___x_1689_, 1);
v___x_1691_ = l_Lean_Expr_cleanupAnnotations(v_a_1690_);
lean_dec(v_a_1690_);
v___x_1692_ = l_Lean_Expr_isApp(v___x_1691_);
if (v___x_1692_ == 0)
{
lean_dec_ref(v___x_1691_);
goto v___jp_1686_;
}
else
{
lean_object* v___x_1693_; uint8_t v___x_1694_; 
v___x_1693_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1691_);
v___x_1694_ = l_Lean_Expr_isApp(v___x_1693_);
if (v___x_1694_ == 0)
{
lean_dec_ref(v___x_1693_);
lean_dec_ref(v___x_1691_);
goto v___jp_1686_;
}
else
{
lean_object* v_arg_1695_; lean_object* v_arg_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; uint8_t v___x_1699_; 
v_arg_1695_ = lean_ctor_get(v___x_1691_, 1);
lean_inc_ref(v_arg_1695_);
lean_dec_ref(v___x_1691_);
v_arg_1696_ = lean_ctor_get(v___x_1693_, 1);
lean_inc_ref(v_arg_1696_);
v___x_1697_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1693_);
lean_dec_ref(v___x_1693_);
v___x_1698_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__1));
v___x_1699_ = l_Lean_Expr_isConstOf(v___x_1697_, v___x_1698_);
if (v___x_1699_ == 0)
{
lean_object* v___x_1700_; uint8_t v___x_1701_; 
v___x_1700_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__3));
v___x_1701_ = l_Lean_Expr_isConstOf(v___x_1697_, v___x_1700_);
if (v___x_1701_ == 0)
{
uint8_t v___x_1702_; 
v___x_1702_ = l_Lean_Expr_isApp(v___x_1697_);
if (v___x_1702_ == 0)
{
lean_dec_ref(v___x_1697_);
lean_dec_ref(v_arg_1696_);
lean_dec_ref(v_arg_1695_);
goto v___jp_1686_;
}
else
{
lean_object* v___x_1703_; uint8_t v___x_1704_; 
v___x_1703_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1697_);
v___x_1704_ = l_Lean_Expr_isApp(v___x_1703_);
if (v___x_1704_ == 0)
{
lean_dec_ref(v___x_1703_);
lean_dec_ref(v___x_1697_);
lean_dec_ref(v_arg_1696_);
lean_dec_ref(v_arg_1695_);
goto v___jp_1686_;
}
else
{
lean_object* v_arg_1705_; lean_object* v_arg_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; uint8_t v___x_1709_; 
v_arg_1705_ = lean_ctor_get(v___x_1697_, 1);
lean_inc_ref(v_arg_1705_);
lean_dec_ref(v___x_1697_);
v_arg_1706_ = lean_ctor_get(v___x_1703_, 1);
lean_inc_ref(v_arg_1706_);
v___x_1707_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1703_);
lean_dec_ref(v___x_1703_);
v___x_1708_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__6));
v___x_1709_ = l_Lean_Expr_isConstOf(v___x_1707_, v___x_1708_);
if (v___x_1709_ == 0)
{
lean_object* v___x_1710_; uint8_t v___x_1711_; 
v___x_1710_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__9));
v___x_1711_ = l_Lean_Expr_isConstOf(v___x_1707_, v___x_1710_);
if (v___x_1711_ == 0)
{
lean_object* v___x_1712_; uint8_t v___x_1713_; 
v___x_1712_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__11));
v___x_1713_ = l_Lean_Expr_isConstOf(v___x_1707_, v___x_1712_);
if (v___x_1713_ == 0)
{
lean_object* v___x_1714_; uint8_t v___x_1715_; 
v___x_1714_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__13));
v___x_1715_ = l_Lean_Expr_isConstOf(v___x_1707_, v___x_1714_);
lean_dec_ref(v___x_1707_);
if (v___x_1715_ == 0)
{
lean_dec_ref(v_arg_1706_);
lean_dec_ref(v_arg_1705_);
lean_dec_ref(v_arg_1696_);
lean_dec_ref(v_arg_1695_);
goto v___jp_1686_;
}
else
{
lean_object* v___x_1716_; 
v___x_1716_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1706_, v_a_1682_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1776_; 
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1719_ = v___x_1716_;
v_isShared_1720_ = v_isSharedCheck_1776_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1716_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1776_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1721_; lean_object* v___x_1722_; uint8_t v___x_1723_; 
v___x_1721_ = l_Lean_Expr_cleanupAnnotations(v_a_1717_);
lean_dec(v_a_1717_);
v___x_1722_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13));
v___x_1723_ = l_Lean_Expr_isConstOf(v___x_1721_, v___x_1722_);
lean_dec_ref(v___x_1721_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; lean_object* v___x_1726_; 
lean_dec_ref(v_arg_1705_);
lean_dec_ref(v_arg_1696_);
lean_dec_ref(v_arg_1695_);
v___x_1724_ = lean_box(0);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 0, v___x_1724_);
v___x_1726_ = v___x_1719_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v___x_1724_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
else
{
lean_object* v___x_1728_; 
lean_del_object(v___x_1719_);
v___x_1728_ = l_Lean_Meta_DefEq_isInstLEInt(v_arg_1705_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1767_; 
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1731_ = v___x_1728_;
v_isShared_1732_ = v_isSharedCheck_1767_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___x_1728_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1767_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
uint8_t v___x_1733_; 
v___x_1733_ = lean_unbox(v_a_1729_);
lean_dec(v_a_1729_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; lean_object* v___x_1736_; 
lean_dec_ref(v_arg_1696_);
lean_dec_ref(v_arg_1695_);
v___x_1734_ = lean_box(0);
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 0, v___x_1734_);
v___x_1736_ = v___x_1731_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v___x_1734_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
else
{
lean_object* v___x_1738_; 
lean_del_object(v___x_1731_);
v___x_1738_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1696_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v_a_1739_; lean_object* v___x_1740_; 
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
lean_inc(v_a_1739_);
lean_dec_ref_known(v___x_1738_, 1);
v___x_1740_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1695_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1750_; 
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1743_ = v___x_1740_;
v_isShared_1744_ = v_isSharedCheck_1750_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1740_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1750_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1748_; 
v___x_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1745_, 0, v_a_1739_);
lean_ctor_set(v___x_1745_, 1, v_a_1741_);
v___x_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1745_);
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 0, v___x_1746_);
v___x_1748_ = v___x_1743_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v___x_1746_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
return v___x_1748_;
}
}
}
else
{
lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1758_; 
lean_dec(v_a_1739_);
v_a_1751_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1753_ = v___x_1740_;
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_dec(v___x_1740_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1756_; 
if (v_isShared_1754_ == 0)
{
v___x_1756_ = v___x_1753_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_a_1751_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
}
else
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1766_; 
lean_dec_ref(v_arg_1695_);
v_a_1759_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1761_ = v___x_1738_;
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1738_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1764_; 
if (v_isShared_1762_ == 0)
{
v___x_1764_ = v___x_1761_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_a_1759_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
}
}
else
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1775_; 
lean_dec_ref(v_arg_1696_);
lean_dec_ref(v_arg_1695_);
v_a_1768_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1770_ = v___x_1728_;
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1728_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1768_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
}
}
else
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1784_; 
lean_dec_ref(v_arg_1705_);
lean_dec_ref(v_arg_1696_);
lean_dec_ref(v_arg_1695_);
v_a_1777_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1779_ = v___x_1716_;
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1716_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1780_ == 0)
{
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
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
}
else
{
lean_object* v___x_1785_; 
lean_dec_ref(v___x_1707_);
v___x_1785_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1706_, v_a_1682_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1847_; 
v_a_1786_ = lean_ctor_get(v___x_1785_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1788_ = v___x_1785_;
v_isShared_1789_ = v_isSharedCheck_1847_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1785_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1847_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; uint8_t v___x_1792_; 
v___x_1790_ = l_Lean_Expr_cleanupAnnotations(v_a_1786_);
lean_dec(v_a_1786_);
v___x_1791_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13));
v___x_1792_ = l_Lean_Expr_isConstOf(v___x_1790_, v___x_1791_);
lean_dec_ref(v___x_1790_);
if (v___x_1792_ == 0)
{
lean_object* v___x_1793_; lean_object* v___x_1795_; 
lean_dec_ref(v_arg_1705_);
lean_dec_ref(v_arg_1696_);
lean_dec_ref(v_arg_1695_);
v___x_1793_ = lean_box(0);
if (v_isShared_1789_ == 0)
{
lean_ctor_set(v___x_1788_, 0, v___x_1793_);
v___x_1795_ = v___x_1788_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v___x_1793_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
else
{
lean_object* v___x_1797_; 
lean_del_object(v___x_1788_);
v___x_1797_ = l_Lean_Meta_DefEq_isInstLTInt(v_arg_1705_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1838_; 
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1800_ = v___x_1797_;
v_isShared_1801_ = v_isSharedCheck_1838_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1797_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1838_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
uint8_t v___x_1802_; 
v___x_1802_ = lean_unbox(v_a_1798_);
lean_dec(v_a_1798_);
if (v___x_1802_ == 0)
{
lean_object* v___x_1803_; lean_object* v___x_1805_; 
lean_dec_ref(v_arg_1696_);
lean_dec_ref(v_arg_1695_);
v___x_1803_ = lean_box(0);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 0, v___x_1803_);
v___x_1805_ = v___x_1800_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v___x_1803_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
else
{
lean_object* v___x_1807_; 
lean_del_object(v___x_1800_);
v___x_1807_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1696_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_a_1808_; lean_object* v___x_1809_; 
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
lean_inc(v_a_1808_);
lean_dec_ref_known(v___x_1807_, 1);
v___x_1809_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1695_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1821_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1812_ = v___x_1809_;
v_isShared_1813_ = v_isSharedCheck_1821_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1809_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1821_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1819_; 
v___x_1814_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14, &l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14);
v___x_1815_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1815_, 0, v_a_1808_);
lean_ctor_set(v___x_1815_, 1, v___x_1814_);
v___x_1816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
lean_ctor_set(v___x_1816_, 1, v_a_1810_);
v___x_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1816_);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 0, v___x_1817_);
v___x_1819_ = v___x_1812_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1817_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
else
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1829_; 
lean_dec(v_a_1808_);
v_a_1822_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1824_ = v___x_1809_;
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1809_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1822_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
}
else
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1837_; 
lean_dec_ref(v_arg_1695_);
v_a_1830_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1832_ = v___x_1807_;
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1807_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1835_; 
if (v_isShared_1833_ == 0)
{
v___x_1835_ = v___x_1832_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_a_1830_);
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
}
}
else
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1846_; 
lean_dec_ref(v_arg_1696_);
lean_dec_ref(v_arg_1695_);
v_a_1839_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1841_ = v___x_1797_;
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1797_);
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
else
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1855_; 
lean_dec_ref(v_arg_1705_);
lean_dec_ref(v_arg_1696_);
lean_dec_ref(v_arg_1695_);
v_a_1848_ = lean_ctor_get(v___x_1785_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1850_ = v___x_1785_;
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1785_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1853_; 
if (v_isShared_1851_ == 0)
{
v___x_1853_ = v___x_1850_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_a_1848_);
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
}
else
{
lean_object* v___x_1856_; 
lean_dec_ref(v___x_1707_);
v___x_1856_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1706_, v_a_1682_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1916_; 
v_a_1857_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1859_ = v___x_1856_;
v_isShared_1860_ = v_isSharedCheck_1916_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1856_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1916_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; uint8_t v___x_1863_; 
v___x_1861_ = l_Lean_Expr_cleanupAnnotations(v_a_1857_);
lean_dec(v_a_1857_);
v___x_1862_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13));
v___x_1863_ = l_Lean_Expr_isConstOf(v___x_1861_, v___x_1862_);
lean_dec_ref(v___x_1861_);
if (v___x_1863_ == 0)
{
lean_object* v___x_1864_; lean_object* v___x_1866_; 
lean_dec_ref(v_arg_1705_);
lean_dec_ref(v_arg_1696_);
lean_dec_ref(v_arg_1695_);
v___x_1864_ = lean_box(0);
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 0, v___x_1864_);
v___x_1866_ = v___x_1859_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v___x_1864_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
else
{
lean_object* v___x_1868_; 
lean_del_object(v___x_1859_);
v___x_1868_ = l_Lean_Meta_DefEq_isInstLEInt(v_arg_1705_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1907_; 
v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1871_ = v___x_1868_;
v_isShared_1872_ = v_isSharedCheck_1907_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1868_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1907_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
uint8_t v___x_1873_; 
v___x_1873_ = lean_unbox(v_a_1869_);
lean_dec(v_a_1869_);
if (v___x_1873_ == 0)
{
lean_object* v___x_1874_; lean_object* v___x_1876_; 
lean_dec_ref(v_arg_1696_);
lean_dec_ref(v_arg_1695_);
v___x_1874_ = lean_box(0);
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 0, v___x_1874_);
v___x_1876_ = v___x_1871_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v___x_1874_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
else
{
lean_object* v___x_1878_; 
lean_del_object(v___x_1871_);
v___x_1878_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1695_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v_a_1879_; lean_object* v___x_1880_; 
v_a_1879_ = lean_ctor_get(v___x_1878_, 0);
lean_inc(v_a_1879_);
lean_dec_ref_known(v___x_1878_, 1);
v___x_1880_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1696_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1890_; 
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1883_ = v___x_1880_;
v_isShared_1884_ = v_isSharedCheck_1890_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1880_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1890_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1888_; 
v___x_1885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1885_, 0, v_a_1879_);
lean_ctor_set(v___x_1885_, 1, v_a_1881_);
v___x_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1885_);
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 0, v___x_1886_);
v___x_1888_ = v___x_1883_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v___x_1886_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
else
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
lean_dec(v_a_1879_);
v_a_1891_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v___x_1880_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1880_);
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
else
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1906_; 
lean_dec_ref(v_arg_1696_);
v_a_1899_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1901_ = v___x_1878_;
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1878_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1902_ == 0)
{
v___x_1904_ = v___x_1901_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_a_1899_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
}
}
}
else
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1915_; 
lean_dec_ref(v_arg_1696_);
lean_dec_ref(v_arg_1695_);
v_a_1908_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1910_ = v___x_1868_;
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1868_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1908_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
}
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
lean_dec_ref(v_arg_1705_);
lean_dec_ref(v_arg_1696_);
lean_dec_ref(v_arg_1695_);
v_a_1917_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1856_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1856_);
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
lean_dec_ref(v___x_1707_);
v___x_1925_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1706_, v_a_1682_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1987_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1928_ = v___x_1925_;
v_isShared_1929_ = v_isSharedCheck_1987_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1925_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1987_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; uint8_t v___x_1932_; 
v___x_1930_ = l_Lean_Expr_cleanupAnnotations(v_a_1926_);
lean_dec(v_a_1926_);
v___x_1931_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13));
v___x_1932_ = l_Lean_Expr_isConstOf(v___x_1930_, v___x_1931_);
lean_dec_ref(v___x_1930_);
if (v___x_1932_ == 0)
{
lean_object* v___x_1933_; lean_object* v___x_1935_; 
lean_dec_ref(v_arg_1705_);
lean_dec_ref(v_arg_1696_);
lean_dec_ref(v_arg_1695_);
v___x_1933_ = lean_box(0);
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 0, v___x_1933_);
v___x_1935_ = v___x_1928_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v___x_1933_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
else
{
lean_object* v___x_1937_; 
lean_del_object(v___x_1928_);
v___x_1937_ = l_Lean_Meta_DefEq_isInstLTInt(v_arg_1705_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1978_; 
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1940_ = v___x_1937_;
v_isShared_1941_ = v_isSharedCheck_1978_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1937_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1978_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
uint8_t v___x_1942_; 
v___x_1942_ = lean_unbox(v_a_1938_);
lean_dec(v_a_1938_);
if (v___x_1942_ == 0)
{
lean_object* v___x_1943_; lean_object* v___x_1945_; 
lean_dec_ref(v_arg_1696_);
lean_dec_ref(v_arg_1695_);
v___x_1943_ = lean_box(0);
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 0, v___x_1943_);
v___x_1945_ = v___x_1940_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v___x_1943_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
else
{
lean_object* v___x_1947_; 
lean_del_object(v___x_1940_);
v___x_1947_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1695_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_);
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_object* v_a_1948_; lean_object* v___x_1949_; 
v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
lean_inc(v_a_1948_);
lean_dec_ref_known(v___x_1947_, 1);
v___x_1949_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1696_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1961_; 
v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1952_ = v___x_1949_;
v_isShared_1953_ = v_isSharedCheck_1961_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1949_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1961_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1959_; 
v___x_1954_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14, &l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14);
v___x_1955_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1955_, 0, v_a_1948_);
lean_ctor_set(v___x_1955_, 1, v___x_1954_);
v___x_1956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1956_, 0, v___x_1955_);
lean_ctor_set(v___x_1956_, 1, v_a_1950_);
v___x_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1956_);
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 0, v___x_1957_);
v___x_1959_ = v___x_1952_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v___x_1957_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
else
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
lean_dec(v_a_1948_);
v_a_1962_ = lean_ctor_get(v___x_1949_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___x_1949_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1949_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1962_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
else
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1977_; 
lean_dec_ref(v_arg_1696_);
v_a_1970_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1972_ = v___x_1947_;
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1947_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1975_; 
if (v_isShared_1973_ == 0)
{
v___x_1975_ = v___x_1972_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1970_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
}
}
else
{
lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1986_; 
lean_dec_ref(v_arg_1696_);
lean_dec_ref(v_arg_1695_);
v_a_1979_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1981_ = v___x_1937_;
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v___x_1937_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1984_; 
if (v_isShared_1982_ == 0)
{
v___x_1984_ = v___x_1981_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_a_1979_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
}
}
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
lean_dec_ref(v_arg_1705_);
lean_dec_ref(v_arg_1696_);
lean_dec_ref(v_arg_1695_);
v_a_1988_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1925_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1925_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1988_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1996_; 
lean_dec_ref(v___x_1697_);
v___x_1996_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1696_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_a_1997_; lean_object* v___x_1998_; 
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_a_1997_);
lean_dec_ref_known(v___x_1996_, 1);
v___x_1998_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1695_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2008_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2001_ = v___x_1998_;
v_isShared_2002_ = v_isSharedCheck_2008_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1998_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2008_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2006_; 
v___x_2003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2003_, 0, v_a_1997_);
lean_ctor_set(v___x_2003_, 1, v_a_1999_);
v___x_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2003_);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 0, v___x_2004_);
v___x_2006_ = v___x_2001_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_2004_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
else
{
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2016_; 
lean_dec(v_a_1997_);
v_a_2009_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2011_ = v___x_1998_;
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___x_1998_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2014_; 
if (v_isShared_2012_ == 0)
{
v___x_2014_ = v___x_2011_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_a_2009_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
}
else
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2024_; 
lean_dec_ref(v_arg_1695_);
v_a_2017_ = lean_ctor_get(v___x_1996_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2019_ = v___x_1996_;
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_1996_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_2017_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
}
}
else
{
lean_object* v___x_2025_; 
lean_dec_ref(v___x_1697_);
v___x_2025_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1696_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_a_2026_; lean_object* v___x_2027_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
lean_inc(v_a_2026_);
lean_dec_ref_known(v___x_2025_, 1);
v___x_2027_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1695_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2039_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2030_ = v___x_2027_;
v_isShared_2031_ = v_isSharedCheck_2039_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2027_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2039_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2037_; 
v___x_2032_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14, &l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14);
v___x_2033_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2033_, 0, v_a_2026_);
lean_ctor_set(v___x_2033_, 1, v___x_2032_);
v___x_2034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2033_);
lean_ctor_set(v___x_2034_, 1, v_a_2028_);
v___x_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2034_);
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 0, v___x_2035_);
v___x_2037_ = v___x_2030_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2035_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
else
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2047_; 
lean_dec(v_a_2026_);
v_a_2040_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2042_ = v___x_2027_;
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2027_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2040_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
else
{
lean_object* v_a_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2055_; 
lean_dec_ref(v_arg_1695_);
v_a_2048_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2050_ = v___x_2025_;
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_a_2048_);
lean_dec(v___x_2025_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2053_; 
if (v_isShared_2051_ == 0)
{
v___x_2053_ = v___x_2050_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2048_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
v_a_2056_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2058_ = v___x_1689_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_1689_);
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
v___jp_1686_:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1687_ = lean_box(0);
v___x_1688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1687_);
return v___x_1688_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___boxed(lean_object* v_e_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f(v_e_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_);
lean_dec(v_a_2069_);
lean_dec_ref(v_a_2068_);
lean_dec(v_a_2067_);
lean_dec_ref(v_a_2066_);
lean_dec(v_a_2065_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f(lean_object* v_e_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_){
_start:
{
lean_object* v___x_2087_; 
v___x_2087_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2077_, v_a_2080_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v_a_2088_; lean_object* v___x_2089_; uint8_t v___x_2090_; 
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
lean_inc(v_a_2088_);
lean_dec_ref_known(v___x_2087_, 1);
v___x_2089_ = l_Lean_Expr_cleanupAnnotations(v_a_2088_);
lean_dec(v_a_2088_);
v___x_2090_ = l_Lean_Expr_isApp(v___x_2089_);
if (v___x_2090_ == 0)
{
lean_dec_ref(v___x_2089_);
goto v___jp_2084_;
}
else
{
lean_object* v___x_2091_; uint8_t v___x_2092_; 
v___x_2091_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2089_);
v___x_2092_ = l_Lean_Expr_isApp(v___x_2091_);
if (v___x_2092_ == 0)
{
lean_dec_ref(v___x_2091_);
lean_dec_ref(v___x_2089_);
goto v___jp_2084_;
}
else
{
lean_object* v___x_2093_; uint8_t v___x_2094_; 
v___x_2093_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2091_);
v___x_2094_ = l_Lean_Expr_isApp(v___x_2093_);
if (v___x_2094_ == 0)
{
lean_dec_ref(v___x_2093_);
lean_dec_ref(v___x_2091_);
lean_dec_ref(v___x_2089_);
goto v___jp_2084_;
}
else
{
lean_object* v___x_2095_; uint8_t v___x_2096_; 
v___x_2095_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2093_);
v___x_2096_ = l_Lean_Expr_isApp(v___x_2095_);
if (v___x_2096_ == 0)
{
lean_dec_ref(v___x_2095_);
lean_dec_ref(v___x_2093_);
lean_dec_ref(v___x_2091_);
lean_dec_ref(v___x_2089_);
goto v___jp_2084_;
}
else
{
lean_object* v___x_2097_; lean_object* v___x_2098_; uint8_t v___x_2099_; 
v___x_2097_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2095_);
v___x_2098_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__2));
v___x_2099_ = l_Lean_Expr_isConstOf(v___x_2097_, v___x_2098_);
lean_dec_ref(v___x_2097_);
if (v___x_2099_ == 0)
{
lean_dec_ref(v___x_2095_);
lean_dec_ref(v___x_2093_);
lean_dec_ref(v___x_2091_);
lean_dec_ref(v___x_2089_);
goto v___jp_2084_;
}
else
{
lean_object* v_arg_2100_; lean_object* v_arg_2101_; lean_object* v_arg_2102_; lean_object* v_arg_2103_; lean_object* v___x_2104_; 
v_arg_2100_ = lean_ctor_get(v___x_2089_, 1);
lean_inc_ref(v_arg_2100_);
lean_dec_ref(v___x_2089_);
v_arg_2101_ = lean_ctor_get(v___x_2091_, 1);
lean_inc_ref(v_arg_2101_);
lean_dec_ref(v___x_2091_);
v_arg_2102_ = lean_ctor_get(v___x_2093_, 1);
lean_inc_ref(v_arg_2102_);
lean_dec_ref(v___x_2093_);
v_arg_2103_ = lean_ctor_get(v___x_2095_, 1);
lean_inc_ref(v_arg_2103_);
lean_dec_ref(v___x_2095_);
v___x_2104_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_2103_, v_a_2080_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2179_; 
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2107_ = v___x_2104_;
v_isShared_2108_ = v_isSharedCheck_2179_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_2104_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2179_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; uint8_t v___x_2111_; 
v___x_2109_ = l_Lean_Expr_cleanupAnnotations(v_a_2105_);
lean_dec(v_a_2105_);
v___x_2110_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13));
v___x_2111_ = l_Lean_Expr_isConstOf(v___x_2109_, v___x_2110_);
lean_dec_ref(v___x_2109_);
if (v___x_2111_ == 0)
{
lean_object* v___x_2112_; lean_object* v___x_2114_; 
lean_dec_ref(v_arg_2102_);
lean_dec_ref(v_arg_2101_);
lean_dec_ref(v_arg_2100_);
v___x_2112_ = lean_box(0);
if (v_isShared_2108_ == 0)
{
lean_ctor_set(v___x_2107_, 0, v___x_2112_);
v___x_2114_ = v___x_2107_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v___x_2112_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
else
{
lean_object* v___x_2116_; 
lean_del_object(v___x_2107_);
v___x_2116_ = l_Lean_Meta_DefEq_isInstDvdInt(v_arg_2102_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2170_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2119_ = v___x_2116_;
v_isShared_2120_ = v_isSharedCheck_2170_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v___x_2116_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2170_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
uint8_t v___x_2121_; 
v___x_2121_ = lean_unbox(v_a_2117_);
lean_dec(v_a_2117_);
if (v___x_2121_ == 0)
{
lean_object* v___x_2122_; lean_object* v___x_2124_; 
lean_dec_ref(v_arg_2101_);
lean_dec_ref(v_arg_2100_);
v___x_2122_ = lean_box(0);
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 0, v___x_2122_);
v___x_2124_ = v___x_2119_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v___x_2122_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
else
{
lean_object* v___x_2126_; 
lean_del_object(v___x_2119_);
v___x_2126_ = l_Lean_Meta_getIntValue_x3f(v_arg_2101_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2161_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2129_ = v___x_2126_;
v_isShared_2130_ = v_isSharedCheck_2161_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_2126_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2161_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
if (lean_obj_tag(v_a_2127_) == 1)
{
lean_object* v_val_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2156_; 
lean_del_object(v___x_2129_);
v_val_2131_ = lean_ctor_get(v_a_2127_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v_a_2127_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2133_ = v_a_2127_;
v_isShared_2134_ = v_isSharedCheck_2156_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_val_2131_);
lean_dec(v_a_2127_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2156_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2135_; 
v___x_2135_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_2100_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2147_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2138_ = v___x_2135_;
v_isShared_2139_ = v_isSharedCheck_2147_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2135_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2147_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2140_; lean_object* v___x_2142_; 
v___x_2140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2140_, 0, v_val_2131_);
lean_ctor_set(v___x_2140_, 1, v_a_2136_);
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 0, v___x_2140_);
v___x_2142_ = v___x_2133_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2140_);
v___x_2142_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
lean_object* v___x_2144_; 
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 0, v___x_2142_);
v___x_2144_ = v___x_2138_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v___x_2142_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_del_object(v___x_2133_);
lean_dec(v_val_2131_);
v_a_2148_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2135_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2135_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
}
else
{
lean_object* v___x_2157_; lean_object* v___x_2159_; 
lean_dec(v_a_2127_);
lean_dec_ref(v_arg_2100_);
v___x_2157_ = lean_box(0);
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 0, v___x_2157_);
v___x_2159_ = v___x_2129_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2157_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
lean_dec_ref(v_arg_2100_);
v_a_2162_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2164_ = v___x_2126_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2126_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
if (v_isShared_2165_ == 0)
{
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2162_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
}
}
}
else
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2178_; 
lean_dec_ref(v_arg_2101_);
lean_dec_ref(v_arg_2100_);
v_a_2171_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2173_ = v___x_2116_;
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2116_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2174_ == 0)
{
v___x_2176_ = v___x_2173_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2171_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
}
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
lean_dec_ref(v_arg_2102_);
lean_dec_ref(v_arg_2101_);
lean_dec_ref(v_arg_2100_);
v_a_2180_ = lean_ctor_get(v___x_2104_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2104_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2104_);
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
}
}
}
}
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
v_a_2188_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___x_2087_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2087_);
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
v___jp_2084_:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2085_ = lean_box(0);
v___x_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2085_);
return v___x_2086_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___boxed(lean_object* v_e_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f(v_e_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_);
lean_dec(v_a_2201_);
lean_dec_ref(v_a_2200_);
lean_dec(v_a_2199_);
lean_dec_ref(v_a_2198_);
lean_dec(v_a_2197_);
return v_res_2203_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2204_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2205_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__0, &l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__0_once, _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__0);
v___x_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2205_);
return v___x_2206_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__3(void){
_start:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2209_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__2));
v___x_2210_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__1, &l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__1_once, _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__1);
v___x_2211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2210_);
lean_ctor_set(v___x_2211_, 1, v___x_2209_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(lean_object* v_x_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_){
_start:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2218_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__3, &l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__3);
v___x_2219_ = lean_st_mk_ref(v___x_2218_);
lean_inc(v_a_2216_);
lean_inc_ref(v_a_2215_);
lean_inc(v_a_2214_);
lean_inc_ref(v_a_2213_);
lean_inc(v___x_2219_);
v___x_2220_ = lean_apply_6(v_x_2212_, v___x_2219_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_, lean_box(0));
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2238_; 
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2223_ = v___x_2220_;
v_isShared_2224_ = v_isSharedCheck_2238_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2220_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2238_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2225_; lean_object* v_vars_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2236_; 
v___x_2225_ = lean_st_ref_get(v___x_2219_);
lean_dec(v___x_2219_);
v_vars_2226_ = lean_ctor_get(v___x_2225_, 1);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2236_ == 0)
{
lean_object* v_unused_2237_; 
v_unused_2237_ = lean_ctor_get(v___x_2225_, 0);
lean_dec(v_unused_2237_);
v___x_2228_ = v___x_2225_;
v_isShared_2229_ = v_isSharedCheck_2236_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_vars_2226_);
lean_dec(v___x_2225_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2236_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2231_; 
if (v_isShared_2229_ == 0)
{
lean_ctor_set(v___x_2228_, 0, v_a_2221_);
v___x_2231_ = v___x_2228_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_a_2221_);
lean_ctor_set(v_reuseFailAlloc_2235_, 1, v_vars_2226_);
v___x_2231_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
lean_object* v___x_2233_; 
if (v_isShared_2224_ == 0)
{
lean_ctor_set(v___x_2223_, 0, v___x_2231_);
v___x_2233_ = v___x_2223_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2231_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
}
else
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
lean_dec(v___x_2219_);
v_a_2239_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_2220_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2220_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___boxed(lean_object* v_x_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_){
_start:
{
lean_object* v_res_2253_; 
v_res_2253_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(v_x_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_);
lean_dec(v_a_2251_);
lean_dec_ref(v_a_2250_);
lean_dec(v_a_2249_);
lean_dec_ref(v_a_2248_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run(lean_object* v_00_u03b1_2254_, lean_object* v_x_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_){
_start:
{
lean_object* v___x_2261_; 
v___x_2261_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(v_x_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run___boxed(lean_object* v_00_u03b1_2262_, lean_object* v_x_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_){
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run(v_00_u03b1_2262_, v_x_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_);
lean_dec(v_a_2267_);
lean_dec_ref(v_a_2266_);
lean_dec(v_a_2265_);
lean_dec_ref(v_a_2264_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toLinearExpr(lean_object* v_e_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_){
_start:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2276_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr___boxed), 7, 1);
lean_closure_set(v___x_2276_, 0, v_e_2270_);
v___x_2277_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(v___x_2276_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_object* v_a_2278_; lean_object* v_fst_2279_; lean_object* v_snd_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; uint8_t v___x_2283_; 
v_a_2278_ = lean_ctor_get(v___x_2277_, 0);
v_fst_2279_ = lean_ctor_get(v_a_2278_, 0);
v_snd_2280_ = lean_ctor_get(v_a_2278_, 1);
v___x_2281_ = lean_array_get_size(v_snd_2280_);
v___x_2282_ = lean_unsigned_to_nat(1u);
v___x_2283_ = lean_nat_dec_eq(v___x_2281_, v___x_2282_);
if (v___x_2283_ == 0)
{
lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2301_; 
lean_inc(v_snd_2280_);
lean_inc(v_fst_2279_);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2301_ == 0)
{
lean_object* v_unused_2302_; 
v_unused_2302_ = lean_ctor_get(v___x_2277_, 0);
lean_dec(v_unused_2302_);
v___x_2285_ = v___x_2277_;
v_isShared_2286_ = v_isSharedCheck_2301_;
goto v_resetjp_2284_;
}
else
{
lean_dec(v___x_2277_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2301_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2287_; lean_object* v_fst_2288_; lean_object* v_snd_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2300_; 
v___x_2287_ = l_Lean_sortExprs(v_snd_2280_, v___x_2283_);
v_fst_2288_ = lean_ctor_get(v___x_2287_, 0);
v_snd_2289_ = lean_ctor_get(v___x_2287_, 1);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2291_ = v___x_2287_;
v_isShared_2292_ = v_isSharedCheck_2300_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_snd_2289_);
lean_inc(v_fst_2288_);
lean_dec(v___x_2287_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2300_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2293_; lean_object* v___x_2295_; 
v___x_2293_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_snd_2289_, v_fst_2279_);
lean_dec(v_snd_2289_);
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 1, v_fst_2288_);
lean_ctor_set(v___x_2291_, 0, v___x_2293_);
v___x_2295_ = v___x_2291_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v___x_2293_);
lean_ctor_set(v_reuseFailAlloc_2299_, 1, v_fst_2288_);
v___x_2295_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
lean_object* v___x_2297_; 
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 0, v___x_2295_);
v___x_2297_ = v___x_2285_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v___x_2295_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
}
}
else
{
return v___x_2277_;
}
}
else
{
return v___x_2277_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toLinearExpr___boxed(lean_object* v_e_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l_Lean_Meta_Simp_Arith_Int_toLinearExpr(v_e_2303_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_);
lean_dec(v_a_2307_);
lean_dec_ref(v_a_2306_);
lean_dec(v_a_2305_);
lean_dec_ref(v_a_2304_);
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_adapter(lean_object* v_e_2310_, lean_object* v_k_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_){
_start:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2317_ = lean_apply_1(v_k_2311_, v_e_2310_);
v___x_2318_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(v___x_2317_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2381_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2321_ = v___x_2318_;
v_isShared_2322_ = v_isSharedCheck_2381_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2318_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2381_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v_fst_2323_; 
v_fst_2323_ = lean_ctor_get(v_a_2319_, 0);
lean_inc(v_fst_2323_);
if (lean_obj_tag(v_fst_2323_) == 1)
{
lean_object* v_val_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2376_; 
v_val_2324_ = lean_ctor_get(v_fst_2323_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v_fst_2323_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2326_ = v_fst_2323_;
v_isShared_2327_ = v_isSharedCheck_2376_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_val_2324_);
lean_dec(v_fst_2323_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2376_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v_snd_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2374_; 
v_snd_2328_ = lean_ctor_get(v_a_2319_, 1);
v_isSharedCheck_2374_ = !lean_is_exclusive(v_a_2319_);
if (v_isSharedCheck_2374_ == 0)
{
lean_object* v_unused_2375_; 
v_unused_2375_ = lean_ctor_get(v_a_2319_, 0);
lean_dec(v_unused_2375_);
v___x_2330_ = v_a_2319_;
v_isShared_2331_ = v_isSharedCheck_2374_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_snd_2328_);
lean_dec(v_a_2319_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2374_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v_fst_2332_; lean_object* v_snd_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2373_; 
v_fst_2332_ = lean_ctor_get(v_val_2324_, 0);
v_snd_2333_ = lean_ctor_get(v_val_2324_, 1);
v_isSharedCheck_2373_ = !lean_is_exclusive(v_val_2324_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2335_ = v_val_2324_;
v_isShared_2336_ = v_isSharedCheck_2373_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_snd_2333_);
lean_inc(v_fst_2332_);
lean_dec(v_val_2324_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2373_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; uint8_t v___x_2339_; 
v___x_2337_ = lean_array_get_size(v_snd_2328_);
v___x_2338_ = lean_unsigned_to_nat(1u);
v___x_2339_ = lean_nat_dec_le(v___x_2337_, v___x_2338_);
if (v___x_2339_ == 0)
{
lean_object* v___x_2340_; lean_object* v_fst_2341_; lean_object* v_snd_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2360_; 
lean_del_object(v___x_2330_);
v___x_2340_ = l_Lean_sortExprs(v_snd_2328_, v___x_2339_);
v_fst_2341_ = lean_ctor_get(v___x_2340_, 0);
v_snd_2342_ = lean_ctor_get(v___x_2340_, 1);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2344_ = v___x_2340_;
v_isShared_2345_ = v_isSharedCheck_2360_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_snd_2342_);
lean_inc(v_fst_2341_);
lean_dec(v___x_2340_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2360_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2349_; 
v___x_2346_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_snd_2342_, v_fst_2332_);
v___x_2347_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_snd_2342_, v_snd_2333_);
lean_dec(v_snd_2342_);
if (v_isShared_2345_ == 0)
{
lean_ctor_set(v___x_2344_, 1, v_fst_2341_);
lean_ctor_set(v___x_2344_, 0, v___x_2347_);
v___x_2349_ = v___x_2344_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v___x_2347_);
lean_ctor_set(v_reuseFailAlloc_2359_, 1, v_fst_2341_);
v___x_2349_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
lean_object* v___x_2351_; 
if (v_isShared_2336_ == 0)
{
lean_ctor_set(v___x_2335_, 1, v___x_2349_);
lean_ctor_set(v___x_2335_, 0, v___x_2346_);
v___x_2351_ = v___x_2335_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v___x_2346_);
lean_ctor_set(v_reuseFailAlloc_2358_, 1, v___x_2349_);
v___x_2351_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
lean_object* v___x_2353_; 
if (v_isShared_2327_ == 0)
{
lean_ctor_set(v___x_2326_, 0, v___x_2351_);
v___x_2353_ = v___x_2326_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2351_);
v___x_2353_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
lean_object* v___x_2355_; 
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 0, v___x_2353_);
v___x_2355_ = v___x_2321_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v___x_2353_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
}
}
else
{
lean_object* v___x_2362_; 
if (v_isShared_2336_ == 0)
{
lean_ctor_set(v___x_2335_, 1, v_snd_2328_);
lean_ctor_set(v___x_2335_, 0, v_snd_2333_);
v___x_2362_ = v___x_2335_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_snd_2333_);
lean_ctor_set(v_reuseFailAlloc_2372_, 1, v_snd_2328_);
v___x_2362_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
lean_object* v___x_2364_; 
if (v_isShared_2331_ == 0)
{
lean_ctor_set(v___x_2330_, 1, v___x_2362_);
lean_ctor_set(v___x_2330_, 0, v_fst_2332_);
v___x_2364_ = v___x_2330_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_fst_2332_);
lean_ctor_set(v_reuseFailAlloc_2371_, 1, v___x_2362_);
v___x_2364_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
lean_object* v___x_2366_; 
if (v_isShared_2327_ == 0)
{
lean_ctor_set(v___x_2326_, 0, v___x_2364_);
v___x_2366_ = v___x_2326_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2364_);
v___x_2366_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
lean_object* v___x_2368_; 
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 0, v___x_2366_);
v___x_2368_ = v___x_2321_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2366_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
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
lean_object* v___x_2377_; lean_object* v___x_2379_; 
lean_dec(v_fst_2323_);
lean_dec(v_a_2319_);
v___x_2377_ = lean_box(0);
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 0, v___x_2377_);
v___x_2379_ = v___x_2321_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v___x_2377_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
}
else
{
lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2389_; 
v_a_2382_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2384_ = v___x_2318_;
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___x_2318_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2387_; 
if (v_isShared_2385_ == 0)
{
v___x_2387_ = v___x_2384_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2382_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_adapter___boxed(lean_object* v_e_2390_, lean_object* v_k_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_){
_start:
{
lean_object* v_res_2397_; 
v_res_2397_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_adapter(v_e_2390_, v_k_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_);
lean_dec(v_a_2395_);
lean_dec_ref(v_a_2394_);
lean_dec(v_a_2393_);
lean_dec_ref(v_a_2392_);
return v_res_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(lean_object* v_e_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_){
_start:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2404_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___boxed), 7, 1);
lean_closure_set(v___x_2404_, 0, v_e_2398_);
v___x_2405_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(v___x_2404_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v_a_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2468_; 
v_a_2406_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2408_ = v___x_2405_;
v_isShared_2409_ = v_isSharedCheck_2468_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_a_2406_);
lean_dec(v___x_2405_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2468_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v_fst_2410_; 
v_fst_2410_ = lean_ctor_get(v_a_2406_, 0);
lean_inc(v_fst_2410_);
if (lean_obj_tag(v_fst_2410_) == 1)
{
lean_object* v_val_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2463_; 
v_val_2411_ = lean_ctor_get(v_fst_2410_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v_fst_2410_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2413_ = v_fst_2410_;
v_isShared_2414_ = v_isSharedCheck_2463_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_val_2411_);
lean_dec(v_fst_2410_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2463_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v_snd_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2461_; 
v_snd_2415_ = lean_ctor_get(v_a_2406_, 1);
v_isSharedCheck_2461_ = !lean_is_exclusive(v_a_2406_);
if (v_isSharedCheck_2461_ == 0)
{
lean_object* v_unused_2462_; 
v_unused_2462_ = lean_ctor_get(v_a_2406_, 0);
lean_dec(v_unused_2462_);
v___x_2417_ = v_a_2406_;
v_isShared_2418_ = v_isSharedCheck_2461_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_snd_2415_);
lean_dec(v_a_2406_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2461_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v_fst_2419_; lean_object* v_snd_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2460_; 
v_fst_2419_ = lean_ctor_get(v_val_2411_, 0);
v_snd_2420_ = lean_ctor_get(v_val_2411_, 1);
v_isSharedCheck_2460_ = !lean_is_exclusive(v_val_2411_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2422_ = v_val_2411_;
v_isShared_2423_ = v_isSharedCheck_2460_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_snd_2420_);
lean_inc(v_fst_2419_);
lean_dec(v_val_2411_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2460_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; uint8_t v___x_2426_; 
v___x_2424_ = lean_array_get_size(v_snd_2415_);
v___x_2425_ = lean_unsigned_to_nat(1u);
v___x_2426_ = lean_nat_dec_le(v___x_2424_, v___x_2425_);
if (v___x_2426_ == 0)
{
lean_object* v___x_2427_; lean_object* v_fst_2428_; lean_object* v_snd_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2447_; 
lean_del_object(v___x_2417_);
v___x_2427_ = l_Lean_sortExprs(v_snd_2415_, v___x_2426_);
v_fst_2428_ = lean_ctor_get(v___x_2427_, 0);
v_snd_2429_ = lean_ctor_get(v___x_2427_, 1);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2431_ = v___x_2427_;
v_isShared_2432_ = v_isSharedCheck_2447_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_snd_2429_);
lean_inc(v_fst_2428_);
lean_dec(v___x_2427_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2447_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2436_; 
v___x_2433_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_snd_2429_, v_fst_2419_);
v___x_2434_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_snd_2429_, v_snd_2420_);
lean_dec(v_snd_2429_);
if (v_isShared_2432_ == 0)
{
lean_ctor_set(v___x_2431_, 1, v_fst_2428_);
lean_ctor_set(v___x_2431_, 0, v___x_2434_);
v___x_2436_ = v___x_2431_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v___x_2434_);
lean_ctor_set(v_reuseFailAlloc_2446_, 1, v_fst_2428_);
v___x_2436_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
lean_object* v___x_2438_; 
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 1, v___x_2436_);
lean_ctor_set(v___x_2422_, 0, v___x_2433_);
v___x_2438_ = v___x_2422_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v___x_2433_);
lean_ctor_set(v_reuseFailAlloc_2445_, 1, v___x_2436_);
v___x_2438_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
lean_object* v___x_2440_; 
if (v_isShared_2414_ == 0)
{
lean_ctor_set(v___x_2413_, 0, v___x_2438_);
v___x_2440_ = v___x_2413_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v___x_2438_);
v___x_2440_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
lean_object* v___x_2442_; 
if (v_isShared_2409_ == 0)
{
lean_ctor_set(v___x_2408_, 0, v___x_2440_);
v___x_2442_ = v___x_2408_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v___x_2440_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
}
}
else
{
lean_object* v___x_2449_; 
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 1, v_snd_2415_);
lean_ctor_set(v___x_2422_, 0, v_snd_2420_);
v___x_2449_ = v___x_2422_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_snd_2420_);
lean_ctor_set(v_reuseFailAlloc_2459_, 1, v_snd_2415_);
v___x_2449_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
lean_object* v___x_2451_; 
if (v_isShared_2418_ == 0)
{
lean_ctor_set(v___x_2417_, 1, v___x_2449_);
lean_ctor_set(v___x_2417_, 0, v_fst_2419_);
v___x_2451_ = v___x_2417_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_fst_2419_);
lean_ctor_set(v_reuseFailAlloc_2458_, 1, v___x_2449_);
v___x_2451_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
lean_object* v___x_2453_; 
if (v_isShared_2414_ == 0)
{
lean_ctor_set(v___x_2413_, 0, v___x_2451_);
v___x_2453_ = v___x_2413_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v___x_2451_);
v___x_2453_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
lean_object* v___x_2455_; 
if (v_isShared_2409_ == 0)
{
lean_ctor_set(v___x_2408_, 0, v___x_2453_);
v___x_2455_ = v___x_2408_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v___x_2453_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
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
lean_object* v___x_2464_; lean_object* v___x_2466_; 
lean_dec(v_fst_2410_);
lean_dec(v_a_2406_);
v___x_2464_ = lean_box(0);
if (v_isShared_2409_ == 0)
{
lean_ctor_set(v___x_2408_, 0, v___x_2464_);
v___x_2466_ = v___x_2408_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v___x_2464_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
}
else
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2476_; 
v_a_2469_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2471_ = v___x_2405_;
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2405_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2474_; 
if (v_isShared_2472_ == 0)
{
v___x_2474_ = v___x_2471_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2469_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f___boxed(lean_object* v_e_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(v_e_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_);
lean_dec(v_a_2481_);
lean_dec_ref(v_a_2480_);
lean_dec(v_a_2479_);
lean_dec_ref(v_a_2478_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(lean_object* v_e_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_){
_start:
{
lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2490_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___boxed), 7, 1);
lean_closure_set(v___x_2490_, 0, v_e_2484_);
v___x_2491_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(v___x_2490_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v_a_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2554_; 
v_a_2492_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2494_ = v___x_2491_;
v_isShared_2495_ = v_isSharedCheck_2554_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_a_2492_);
lean_dec(v___x_2491_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2554_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v_fst_2496_; 
v_fst_2496_ = lean_ctor_get(v_a_2492_, 0);
lean_inc(v_fst_2496_);
if (lean_obj_tag(v_fst_2496_) == 1)
{
lean_object* v_val_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2549_; 
v_val_2497_ = lean_ctor_get(v_fst_2496_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v_fst_2496_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2499_ = v_fst_2496_;
v_isShared_2500_ = v_isSharedCheck_2549_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_val_2497_);
lean_dec(v_fst_2496_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2549_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v_snd_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2547_; 
v_snd_2501_ = lean_ctor_get(v_a_2492_, 1);
v_isSharedCheck_2547_ = !lean_is_exclusive(v_a_2492_);
if (v_isSharedCheck_2547_ == 0)
{
lean_object* v_unused_2548_; 
v_unused_2548_ = lean_ctor_get(v_a_2492_, 0);
lean_dec(v_unused_2548_);
v___x_2503_ = v_a_2492_;
v_isShared_2504_ = v_isSharedCheck_2547_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_snd_2501_);
lean_dec(v_a_2492_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2547_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v_fst_2505_; lean_object* v_snd_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2546_; 
v_fst_2505_ = lean_ctor_get(v_val_2497_, 0);
v_snd_2506_ = lean_ctor_get(v_val_2497_, 1);
v_isSharedCheck_2546_ = !lean_is_exclusive(v_val_2497_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2508_ = v_val_2497_;
v_isShared_2509_ = v_isSharedCheck_2546_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_snd_2506_);
lean_inc(v_fst_2505_);
lean_dec(v_val_2497_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2546_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; uint8_t v___x_2512_; 
v___x_2510_ = lean_array_get_size(v_snd_2501_);
v___x_2511_ = lean_unsigned_to_nat(1u);
v___x_2512_ = lean_nat_dec_le(v___x_2510_, v___x_2511_);
if (v___x_2512_ == 0)
{
lean_object* v___x_2513_; lean_object* v_fst_2514_; lean_object* v_snd_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2533_; 
lean_del_object(v___x_2503_);
v___x_2513_ = l_Lean_sortExprs(v_snd_2501_, v___x_2512_);
v_fst_2514_ = lean_ctor_get(v___x_2513_, 0);
v_snd_2515_ = lean_ctor_get(v___x_2513_, 1);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2517_ = v___x_2513_;
v_isShared_2518_ = v_isSharedCheck_2533_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_snd_2515_);
lean_inc(v_fst_2514_);
lean_dec(v___x_2513_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2533_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2522_; 
v___x_2519_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_snd_2515_, v_fst_2505_);
v___x_2520_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_snd_2515_, v_snd_2506_);
lean_dec(v_snd_2515_);
if (v_isShared_2518_ == 0)
{
lean_ctor_set(v___x_2517_, 1, v_fst_2514_);
lean_ctor_set(v___x_2517_, 0, v___x_2520_);
v___x_2522_ = v___x_2517_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2520_);
lean_ctor_set(v_reuseFailAlloc_2532_, 1, v_fst_2514_);
v___x_2522_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
lean_object* v___x_2524_; 
if (v_isShared_2509_ == 0)
{
lean_ctor_set(v___x_2508_, 1, v___x_2522_);
lean_ctor_set(v___x_2508_, 0, v___x_2519_);
v___x_2524_ = v___x_2508_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___x_2519_);
lean_ctor_set(v_reuseFailAlloc_2531_, 1, v___x_2522_);
v___x_2524_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
lean_object* v___x_2526_; 
if (v_isShared_2500_ == 0)
{
lean_ctor_set(v___x_2499_, 0, v___x_2524_);
v___x_2526_ = v___x_2499_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v___x_2524_);
v___x_2526_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
lean_object* v___x_2528_; 
if (v_isShared_2495_ == 0)
{
lean_ctor_set(v___x_2494_, 0, v___x_2526_);
v___x_2528_ = v___x_2494_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v___x_2526_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
}
}
}
else
{
lean_object* v___x_2535_; 
if (v_isShared_2509_ == 0)
{
lean_ctor_set(v___x_2508_, 1, v_snd_2501_);
lean_ctor_set(v___x_2508_, 0, v_snd_2506_);
v___x_2535_ = v___x_2508_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_snd_2506_);
lean_ctor_set(v_reuseFailAlloc_2545_, 1, v_snd_2501_);
v___x_2535_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
lean_object* v___x_2537_; 
if (v_isShared_2504_ == 0)
{
lean_ctor_set(v___x_2503_, 1, v___x_2535_);
lean_ctor_set(v___x_2503_, 0, v_fst_2505_);
v___x_2537_ = v___x_2503_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_fst_2505_);
lean_ctor_set(v_reuseFailAlloc_2544_, 1, v___x_2535_);
v___x_2537_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
lean_object* v___x_2539_; 
if (v_isShared_2500_ == 0)
{
lean_ctor_set(v___x_2499_, 0, v___x_2537_);
v___x_2539_ = v___x_2499_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v___x_2537_);
v___x_2539_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
lean_object* v___x_2541_; 
if (v_isShared_2495_ == 0)
{
lean_ctor_set(v___x_2494_, 0, v___x_2539_);
v___x_2541_ = v___x_2494_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v___x_2539_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
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
lean_object* v___x_2550_; lean_object* v___x_2552_; 
lean_dec(v_fst_2496_);
lean_dec(v_a_2492_);
v___x_2550_ = lean_box(0);
if (v_isShared_2495_ == 0)
{
lean_ctor_set(v___x_2494_, 0, v___x_2550_);
v___x_2552_ = v___x_2494_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2550_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
}
}
else
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
v_a_2555_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2557_ = v___x_2491_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2491_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_a_2555_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f___boxed(lean_object* v_e_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_){
_start:
{
lean_object* v_res_2569_; 
v_res_2569_ = l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(v_e_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_);
lean_dec(v_a_2567_);
lean_dec_ref(v_a_2566_);
lean_dec(v_a_2565_);
lean_dec_ref(v_a_2564_);
return v_res_2569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(lean_object* v_e_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_){
_start:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2576_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___boxed), 7, 1);
lean_closure_set(v___x_2576_, 0, v_e_2570_);
v___x_2577_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(v___x_2576_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2639_; 
v_a_2578_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2580_ = v___x_2577_;
v_isShared_2581_ = v_isSharedCheck_2639_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2577_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2639_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v_fst_2582_; 
v_fst_2582_ = lean_ctor_get(v_a_2578_, 0);
lean_inc(v_fst_2582_);
if (lean_obj_tag(v_fst_2582_) == 1)
{
lean_object* v_val_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2634_; 
v_val_2583_ = lean_ctor_get(v_fst_2582_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v_fst_2582_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2585_ = v_fst_2582_;
v_isShared_2586_ = v_isSharedCheck_2634_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_val_2583_);
lean_dec(v_fst_2582_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2634_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v_snd_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2632_; 
v_snd_2587_ = lean_ctor_get(v_a_2578_, 1);
v_isSharedCheck_2632_ = !lean_is_exclusive(v_a_2578_);
if (v_isSharedCheck_2632_ == 0)
{
lean_object* v_unused_2633_; 
v_unused_2633_ = lean_ctor_get(v_a_2578_, 0);
lean_dec(v_unused_2633_);
v___x_2589_ = v_a_2578_;
v_isShared_2590_ = v_isSharedCheck_2632_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_snd_2587_);
lean_dec(v_a_2578_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2632_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v_fst_2591_; lean_object* v_snd_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2631_; 
v_fst_2591_ = lean_ctor_get(v_val_2583_, 0);
v_snd_2592_ = lean_ctor_get(v_val_2583_, 1);
v_isSharedCheck_2631_ = !lean_is_exclusive(v_val_2583_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2594_ = v_val_2583_;
v_isShared_2595_ = v_isSharedCheck_2631_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_snd_2592_);
lean_inc(v_fst_2591_);
lean_dec(v_val_2583_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2631_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; uint8_t v___x_2598_; 
v___x_2596_ = lean_array_get_size(v_snd_2587_);
v___x_2597_ = lean_unsigned_to_nat(1u);
v___x_2598_ = lean_nat_dec_le(v___x_2596_, v___x_2597_);
if (v___x_2598_ == 0)
{
lean_object* v___x_2599_; lean_object* v_fst_2600_; lean_object* v_snd_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2618_; 
lean_del_object(v___x_2589_);
v___x_2599_ = l_Lean_sortExprs(v_snd_2587_, v___x_2598_);
v_fst_2600_ = lean_ctor_get(v___x_2599_, 0);
v_snd_2601_ = lean_ctor_get(v___x_2599_, 1);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2603_ = v___x_2599_;
v_isShared_2604_ = v_isSharedCheck_2618_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_snd_2601_);
lean_inc(v_fst_2600_);
lean_dec(v___x_2599_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2618_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2605_; lean_object* v___x_2607_; 
v___x_2605_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_snd_2601_, v_snd_2592_);
lean_dec(v_snd_2601_);
if (v_isShared_2604_ == 0)
{
lean_ctor_set(v___x_2603_, 1, v_fst_2600_);
lean_ctor_set(v___x_2603_, 0, v___x_2605_);
v___x_2607_ = v___x_2603_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v___x_2605_);
lean_ctor_set(v_reuseFailAlloc_2617_, 1, v_fst_2600_);
v___x_2607_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
lean_object* v___x_2609_; 
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 1, v___x_2607_);
v___x_2609_ = v___x_2594_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_fst_2591_);
lean_ctor_set(v_reuseFailAlloc_2616_, 1, v___x_2607_);
v___x_2609_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
lean_object* v___x_2611_; 
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 0, v___x_2609_);
v___x_2611_ = v___x_2585_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v___x_2609_);
v___x_2611_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
lean_object* v___x_2613_; 
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 0, v___x_2611_);
v___x_2613_ = v___x_2580_;
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
}
}
else
{
lean_object* v___x_2620_; 
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 1, v_snd_2587_);
lean_ctor_set(v___x_2594_, 0, v_snd_2592_);
v___x_2620_ = v___x_2594_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_snd_2592_);
lean_ctor_set(v_reuseFailAlloc_2630_, 1, v_snd_2587_);
v___x_2620_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
lean_object* v___x_2622_; 
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 1, v___x_2620_);
lean_ctor_set(v___x_2589_, 0, v_fst_2591_);
v___x_2622_ = v___x_2589_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_fst_2591_);
lean_ctor_set(v_reuseFailAlloc_2629_, 1, v___x_2620_);
v___x_2622_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
lean_object* v___x_2624_; 
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 0, v___x_2622_);
v___x_2624_ = v___x_2585_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v___x_2622_);
v___x_2624_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
lean_object* v___x_2626_; 
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 0, v___x_2624_);
v___x_2626_ = v___x_2580_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v___x_2624_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
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
lean_object* v___x_2635_; lean_object* v___x_2637_; 
lean_dec(v_fst_2582_);
lean_dec(v_a_2578_);
v___x_2635_ = lean_box(0);
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 0, v___x_2635_);
v___x_2637_ = v___x_2580_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v___x_2635_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
}
}
else
{
lean_object* v_a_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2647_; 
v_a_2640_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2642_ = v___x_2577_;
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_a_2640_);
lean_dec(v___x_2577_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2645_; 
if (v_isShared_2643_ == 0)
{
v___x_2645_ = v___x_2642_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_a_2640_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f___boxed(lean_object* v_e_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_){
_start:
{
lean_object* v_res_2654_; 
v_res_2654_ = l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(v_e_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
lean_dec(v_a_2652_);
lean_dec_ref(v_a_2651_);
lean_dec(v_a_2650_);
lean_dec_ref(v_a_2649_);
return v_res_2654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr___lam__0(lean_object* v___y_2655_){
_start:
{
lean_inc_ref(v___y_2655_);
return v___y_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr___lam__0___boxed(lean_object* v___y_2656_){
_start:
{
lean_object* v_res_2657_; 
v_res_2657_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr___lam__0(v___y_2656_);
lean_dec_ref(v___y_2656_);
return v_res_2657_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1(void){
_start:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2659_ = lean_box(0);
v___x_2660_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13));
v___x_2661_ = l_Lean_mkConst(v___x_2660_, v___x_2659_);
return v___x_2661_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__2(void){
_start:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2662_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
v___x_2663_ = l_Lean_mkIntLit(v___x_2662_);
return v___x_2663_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__3(void){
_start:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2664_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__2, &l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__2);
v___x_2665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2664_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr(lean_object* v_ctx_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_){
_start:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; uint8_t v___x_2674_; 
v___x_2672_ = lean_unsigned_to_nat(0u);
v___x_2673_ = lean_array_get_size(v_ctx_2666_);
v___x_2674_ = lean_nat_dec_lt(v___x_2672_, v___x_2673_);
if (v___x_2674_ == 0)
{
lean_object* v___f_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
lean_dec_ref(v_ctx_2666_);
v___f_2675_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__0));
v___x_2676_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1, &l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1_once, _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1);
v___x_2677_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__3, &l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__3);
v___x_2678_ = l_Lean_RArray_toExpr___redArg(v___x_2676_, v___f_2675_, v___x_2677_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_);
return v___x_2678_;
}
else
{
lean_object* v___f_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; 
v___f_2679_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__0));
v___x_2680_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1, &l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1_once, _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1);
v___x_2681_ = l_Lean_RArray_ofArray___redArg(v_ctx_2666_);
v___x_2682_ = l_Lean_RArray_toExpr___redArg(v___x_2680_, v___f_2679_, v___x_2681_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_);
return v___x_2682_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr___boxed(lean_object* v_ctx_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_){
_start:
{
lean_object* v_res_2689_; 
v_res_2689_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_ctx_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_);
lean_dec(v_a_2687_);
lean_dec_ref(v_a_2686_);
lean_dec(v_a_2685_);
lean_dec_ref(v_a_2684_);
return v_res_2689_;
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
