// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Arith.Nat.Basic
// Imports: public import Lean.Util.SortExprs public import Lean.Meta.KExprMap import Lean.Data.RArray import Lean.Meta.NatInstTesters import Lean.Meta.Offset public import Init.Data.Nat.Internal.Linear import Lean.OrderLevel
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_leCarrierIsSort(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatAdd(lean_object*, lean_object*);
lean_object* l_Lean_mkNatMul(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLE(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkNatEq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_DefEq_isInstLENat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_KExprMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_KExprMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DefEq_isInstHAddNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DefEq_isInstHMulNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DefEq_isInstAddNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DefEq_isInstMulNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstOfNatNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkInstOfNatNat(lean_object*);
lean_object* l_Lean_Meta_isDefEqI(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_Internal_Linear_Expr_inc(lean_object*);
lean_object* l_Lean_Meta_DefEq_isInstLTNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_sortExprs(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_RArray_toExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RArray_ofArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_applyPerm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_applyPerm___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_ExprCnstr_applyPerm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_ExprCnstr_applyPerm___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Nat.Internal.Linear.Expr.num"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__0_value)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Nat.Internal.Linear.Expr.var"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__5 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__5_value)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__6 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__7_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Nat.Internal.Linear.Expr.add"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__8 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__8_value)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__9 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__10 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__10_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Nat.Internal.Linear.Expr.mulL"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__11 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__11_value)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__12 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__12_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__13 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__13_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Nat.Internal.Linear.Expr.mulR"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__14 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__14_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__14_value)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__15 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__15_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__15_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__16 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__16_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__3_value),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__9_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lhs"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__10 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__10_value)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__11_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rhs"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__13 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__13_value)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__14 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__14_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__15 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__15_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__16;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__18 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__18_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__15_value)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__19 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__19_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean___closed__0_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*);
static const lean_string_object l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__1 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__1_value;
static const lean_string_object l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__2 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__2_value;
static lean_once_cell_t l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__3;
static lean_once_cell_t l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__4;
static const lean_ctor_object l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__0_value)}};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__5 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__5_value;
static const lean_ctor_object l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__2_value)}};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__6 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__1(lean_object*, lean_object*);
static const lean_string_object l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__0 = (const lean_object*)&l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__0_value)}};
static const lean_object* l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__1 = (const lean_object*)&l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__1_value;
static const lean_string_object l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__2 = (const lean_object*)&l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__2_value;
static const lean_string_object l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__3 = (const lean_object*)&l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__3_value;
static lean_once_cell_t l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__4;
static lean_once_cell_t l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__5;
static const lean_ctor_object l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__2_value)}};
static const lean_object* l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__6 = (const lean_object*)&l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__6_value;
static const lean_ctor_object l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__3_value)}};
static const lean_object* l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__7 = (const lean_object*)&l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__7_value;
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean___closed__0_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linear"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Expr"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__3_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(238, 85, 239, 193, 128, 115, 38, 143)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(135, 17, 186, 49, 10, 156, 173, 153)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(169, 249, 49, 128, 149, 247, 152, 46)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__5_value_aux_3),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(105, 71, 241, 172, 146, 30, 124, 174)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__5 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__6;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "var"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(238, 85, 239, 193, 128, 115, 38, 143)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(135, 17, 186, 49, 10, 156, 173, 153)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__8_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(169, 249, 49, 128, 149, 247, 152, 46)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__8_value_aux_3),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7_value),LEAN_SCALAR_PTR_LITERAL(244, 45, 39, 251, 222, 140, 116, 164)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__8 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__9;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "add"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(238, 85, 239, 193, 128, 115, 38, 143)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__11_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(135, 17, 186, 49, 10, 156, 173, 153)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__11_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__11_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(169, 249, 49, 128, 149, 247, 152, 46)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__11_value_aux_3),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10_value),LEAN_SCALAR_PTR_LITERAL(152, 194, 43, 145, 170, 16, 243, 49)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__11 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__11_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__12;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "mulL"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__14_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(238, 85, 239, 193, 128, 115, 38, 143)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__14_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(135, 17, 186, 49, 10, 156, 173, 153)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__14_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__14_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(169, 249, 49, 128, 149, 247, 152, 46)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__14_value_aux_3),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13_value),LEAN_SCALAR_PTR_LITERAL(98, 60, 158, 114, 51, 204, 90, 14)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__14 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__14_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__15;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "mulR"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(238, 85, 239, 193, 128, 115, 38, 143)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__17_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(135, 17, 186, 49, 10, 156, 173, 153)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__17_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__17_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(169, 249, 49, 128, 149, 247, 152, 46)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__17_value_aux_3),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16_value),LEAN_SCALAR_PTR_LITERAL(95, 24, 94, 154, 72, 237, 109, 87)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__17 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__17_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__18;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(lean_object*);
static const lean_closure_object l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(238, 85, 239, 193, 128, 115, 38, 143)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(135, 17, 186, 49, 10, 156, 173, 153)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(169, 249, 49, 128, 149, 247, 152, 46)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__2;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ExprCnstr"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__0_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(238, 85, 239, 193, 128, 115, 38, 143)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(135, 17, 186, 49, 10, 156, 173, 153)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 198, 254, 91, 59, 223, 24, 67)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2_value_aux_3),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(220, 231, 21, 69, 15, 252, 140, 70)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__3;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__4_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__5 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__6 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__7;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__8 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__8_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__9 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(lean_object*);
static const lean_closure_object l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(238, 85, 239, 193, 128, 115, 38, 143)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(135, 17, 186, 49, 10, 156, 173, 153)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 198, 254, 91, 59, 223, 24, 67)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__2;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zero"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "succ"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 165, 73, 246, 125, 40, 156, 223)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mul"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__2_value),LEAN_SCALAR_PTR_LITERAL(124, 230, 50, 167, 103, 237, 136, 198)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10_value),LEAN_SCALAR_PTR_LITERAL(210, 189, 86, 121, 130, 22, 242, 236)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__5_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__6_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Mul"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__8_value),LEAN_SCALAR_PTR_LITERAL(155, 25, 183, 66, 31, 85, 84, 65)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__2_value),LEAN_SCALAR_PTR_LITERAL(124, 210, 233, 157, 130, 57, 249, 157)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Add"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__10_value),LEAN_SCALAR_PTR_LITERAL(123, 91, 0, 102, 155, 93, 69, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10_value),LEAN_SCALAR_PTR_LITERAL(50, 34, 112, 179, 66, 45, 192, 92)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__12_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__13_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__15_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__16_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__17_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 181, 171, 119, 158, 138, 221, 239)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__1_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(194, 170, 199, 36, 204, 118, 150, 149)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__3_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__5 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__5_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "GT"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__6 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__6_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "gt"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(240, 16, 15, 58, 66, 186, 138, 31)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(239, 75, 137, 103, 59, 22, 209, 130)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__8 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__8_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "GE"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__9 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__9_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ge"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__10 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(74, 169, 4, 72, 62, 21, 91, 24)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__10_value),LEAN_SCALAR_PTR_LITERAL(71, 88, 92, 156, 129, 215, 23, 77)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__11 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__11_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__12 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__13 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__13_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__14 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__14_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__14_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__15_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__15 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__15_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__16 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__16_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__1;
static const lean_array_object l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearCnstr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__2;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(lean_object* v_a_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
lean_object* v___x_3_; 
v___x_3_ = lean_box(0);
return v___x_3_;
}
else
{
lean_object* v_key_4_; lean_object* v_value_5_; lean_object* v_tail_6_; uint8_t v___x_7_; 
v_key_4_ = lean_ctor_get(v_x_2_, 0);
v_value_5_ = lean_ctor_get(v_x_2_, 1);
v_tail_6_ = lean_ctor_get(v_x_2_, 2);
v___x_7_ = lean_nat_dec_eq(v_key_4_, v_a_1_);
if (v___x_7_ == 0)
{
v_x_2_ = v_tail_6_;
goto _start;
}
else
{
lean_object* v___x_9_; 
lean_inc(v_value_5_);
v___x_9_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_9_, 0, v_value_5_);
return v___x_9_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg___boxed(lean_object* v_a_10_, lean_object* v_x_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(v_a_10_, v_x_11_);
lean_dec(v_x_11_);
lean_dec(v_a_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0___redArg(lean_object* v_m_13_, lean_object* v_a_14_){
_start:
{
lean_object* v_buckets_15_; lean_object* v___x_16_; uint64_t v___x_17_; uint64_t v___x_18_; uint64_t v___x_19_; uint64_t v_fold_20_; uint64_t v___x_21_; uint64_t v___x_22_; uint64_t v___x_23_; size_t v___x_24_; size_t v___x_25_; size_t v___x_26_; size_t v___x_27_; size_t v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v_buckets_15_ = lean_ctor_get(v_m_13_, 1);
v___x_16_ = lean_array_get_size(v_buckets_15_);
v___x_17_ = lean_uint64_of_nat(v_a_14_);
v___x_18_ = 32ULL;
v___x_19_ = lean_uint64_shift_right(v___x_17_, v___x_18_);
v_fold_20_ = lean_uint64_xor(v___x_17_, v___x_19_);
v___x_21_ = 16ULL;
v___x_22_ = lean_uint64_shift_right(v_fold_20_, v___x_21_);
v___x_23_ = lean_uint64_xor(v_fold_20_, v___x_22_);
v___x_24_ = lean_uint64_to_usize(v___x_23_);
v___x_25_ = lean_usize_of_nat(v___x_16_);
v___x_26_ = ((size_t)1ULL);
v___x_27_ = lean_usize_sub(v___x_25_, v___x_26_);
v___x_28_ = lean_usize_land(v___x_24_, v___x_27_);
v___x_29_ = lean_array_uget_borrowed(v_buckets_15_, v___x_28_);
v___x_30_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(v_a_14_, v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0___redArg___boxed(lean_object* v_m_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0___redArg(v_m_31_, v_a_32_);
lean_dec(v_a_32_);
lean_dec_ref(v_m_31_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go(lean_object* v_perm_34_, lean_object* v_a_35_){
_start:
{
switch(lean_obj_tag(v_a_35_))
{
case 0:
{
return v_a_35_;
}
case 1:
{
lean_object* v_i_36_; lean_object* v___x_37_; 
v_i_36_ = lean_ctor_get(v_a_35_, 0);
v___x_37_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0___redArg(v_perm_34_, v_i_36_);
if (lean_obj_tag(v___x_37_) == 0)
{
return v_a_35_;
}
else
{
lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_45_; 
v_isSharedCheck_45_ = !lean_is_exclusive(v_a_35_);
if (v_isSharedCheck_45_ == 0)
{
lean_object* v_unused_46_; 
v_unused_46_ = lean_ctor_get(v_a_35_, 0);
lean_dec(v_unused_46_);
v___x_39_ = v_a_35_;
v_isShared_40_ = v_isSharedCheck_45_;
goto v_resetjp_38_;
}
else
{
lean_dec(v_a_35_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_45_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
lean_object* v_val_41_; lean_object* v___x_43_; 
v_val_41_ = lean_ctor_get(v___x_37_, 0);
lean_inc(v_val_41_);
lean_dec_ref_known(v___x_37_, 1);
if (v_isShared_40_ == 0)
{
lean_ctor_set(v___x_39_, 0, v_val_41_);
v___x_43_ = v___x_39_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_val_41_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
return v___x_43_;
}
}
}
}
case 2:
{
lean_object* v_a_47_; lean_object* v_b_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_57_; 
v_a_47_ = lean_ctor_get(v_a_35_, 0);
v_b_48_ = lean_ctor_get(v_a_35_, 1);
v_isSharedCheck_57_ = !lean_is_exclusive(v_a_35_);
if (v_isSharedCheck_57_ == 0)
{
v___x_50_ = v_a_35_;
v_isShared_51_ = v_isSharedCheck_57_;
goto v_resetjp_49_;
}
else
{
lean_inc(v_b_48_);
lean_inc(v_a_47_);
lean_dec(v_a_35_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_57_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_55_; 
v___x_52_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go(v_perm_34_, v_a_47_);
v___x_53_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go(v_perm_34_, v_b_48_);
if (v_isShared_51_ == 0)
{
lean_ctor_set(v___x_50_, 1, v___x_53_);
lean_ctor_set(v___x_50_, 0, v___x_52_);
v___x_55_ = v___x_50_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v___x_52_);
lean_ctor_set(v_reuseFailAlloc_56_, 1, v___x_53_);
v___x_55_ = v_reuseFailAlloc_56_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
return v___x_55_;
}
}
}
case 3:
{
lean_object* v_k_58_; lean_object* v_a_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_67_; 
v_k_58_ = lean_ctor_get(v_a_35_, 0);
v_a_59_ = lean_ctor_get(v_a_35_, 1);
v_isSharedCheck_67_ = !lean_is_exclusive(v_a_35_);
if (v_isSharedCheck_67_ == 0)
{
v___x_61_ = v_a_35_;
v_isShared_62_ = v_isSharedCheck_67_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_a_59_);
lean_inc(v_k_58_);
lean_dec(v_a_35_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_67_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___x_63_; lean_object* v___x_65_; 
v___x_63_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go(v_perm_34_, v_a_59_);
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 1, v___x_63_);
v___x_65_ = v___x_61_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v_k_58_);
lean_ctor_set(v_reuseFailAlloc_66_, 1, v___x_63_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
return v___x_65_;
}
}
}
default: 
{
lean_object* v_a_68_; lean_object* v_k_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_77_; 
v_a_68_ = lean_ctor_get(v_a_35_, 0);
v_k_69_ = lean_ctor_get(v_a_35_, 1);
v_isSharedCheck_77_ = !lean_is_exclusive(v_a_35_);
if (v_isSharedCheck_77_ == 0)
{
v___x_71_ = v_a_35_;
v_isShared_72_ = v_isSharedCheck_77_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_k_69_);
lean_inc(v_a_68_);
lean_dec(v_a_35_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_77_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v___x_73_; lean_object* v___x_75_; 
v___x_73_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go(v_perm_34_, v_a_68_);
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 0, v___x_73_);
v___x_75_ = v___x_71_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v___x_73_);
lean_ctor_set(v_reuseFailAlloc_76_, 1, v_k_69_);
v___x_75_ = v_reuseFailAlloc_76_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
return v___x_75_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go___boxed(lean_object* v_perm_78_, lean_object* v_a_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go(v_perm_78_, v_a_79_);
lean_dec_ref(v_perm_78_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0(lean_object* v_00_u03b2_81_, lean_object* v_m_82_, lean_object* v_a_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0___redArg(v_m_82_, v_a_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0___boxed(lean_object* v_00_u03b2_85_, lean_object* v_m_86_, lean_object* v_a_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0(v_00_u03b2_85_, v_m_86_, v_a_87_);
lean_dec(v_a_87_);
lean_dec_ref(v_m_86_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0(lean_object* v_00_u03b2_89_, lean_object* v_a_90_, lean_object* v_x_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(v_a_90_, v_x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_93_, lean_object* v_a_94_, lean_object* v_x_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0(v_00_u03b2_93_, v_a_94_, v_x_95_);
lean_dec(v_x_95_);
lean_dec(v_a_94_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_applyPerm(lean_object* v_perm_97_, lean_object* v_e_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go(v_perm_97_, v_e_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_applyPerm___boxed(lean_object* v_perm_100_, lean_object* v_e_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Nat_Internal_Linear_Expr_applyPerm(v_perm_100_, v_e_101_);
lean_dec_ref(v_perm_100_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_ExprCnstr_applyPerm(lean_object* v_perm_103_, lean_object* v_x_104_){
_start:
{
uint8_t v_eq_105_; lean_object* v_lhs_106_; lean_object* v_rhs_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_116_; 
v_eq_105_ = lean_ctor_get_uint8(v_x_104_, sizeof(void*)*2);
v_lhs_106_ = lean_ctor_get(v_x_104_, 0);
v_rhs_107_ = lean_ctor_get(v_x_104_, 1);
v_isSharedCheck_116_ = !lean_is_exclusive(v_x_104_);
if (v_isSharedCheck_116_ == 0)
{
v___x_109_ = v_x_104_;
v_isShared_110_ = v_isSharedCheck_116_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_rhs_107_);
lean_inc(v_lhs_106_);
lean_dec(v_x_104_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_116_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_114_; 
v___x_111_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go(v_perm_103_, v_lhs_106_);
v___x_112_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go(v_perm_103_, v_rhs_107_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 1, v___x_112_);
lean_ctor_set(v___x_109_, 0, v___x_111_);
v___x_114_ = v___x_109_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v___x_111_);
lean_ctor_set(v_reuseFailAlloc_115_, 1, v___x_112_);
lean_ctor_set_uint8(v_reuseFailAlloc_115_, sizeof(void*)*2, v_eq_105_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_ExprCnstr_applyPerm___boxed(lean_object* v_perm_117_, lean_object* v_x_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Nat_Internal_Linear_ExprCnstr_applyPerm(v_perm_117_, v_x_118_);
lean_dec_ref(v_perm_117_);
return v_res_119_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = lean_unsigned_to_nat(2u);
v___x_127_ = lean_nat_to_int(v___x_126_);
return v___x_127_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = lean_unsigned_to_nat(1u);
v___x_129_ = lean_nat_to_int(v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(lean_object* v_x_154_, lean_object* v_prec_155_){
_start:
{
switch(lean_obj_tag(v_x_154_))
{
case 0:
{
lean_object* v_v_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_176_; 
v_v_156_ = lean_ctor_get(v_x_154_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v_x_154_);
if (v_isSharedCheck_176_ == 0)
{
v___x_158_ = v_x_154_;
v_isShared_159_ = v_isSharedCheck_176_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_v_156_);
lean_dec(v_x_154_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_176_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___y_161_; lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_172_ = lean_unsigned_to_nat(1024u);
v___x_173_ = lean_nat_dec_le(v___x_172_, v_prec_155_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; 
v___x_174_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3, &l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3);
v___y_161_ = v___x_174_;
goto v___jp_160_;
}
else
{
lean_object* v___x_175_; 
v___x_175_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4, &l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4_once, _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4);
v___y_161_ = v___x_175_;
goto v___jp_160_;
}
v___jp_160_:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_165_; 
v___x_162_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__2));
v___x_163_ = l_Nat_reprFast(v_v_156_);
if (v_isShared_159_ == 0)
{
lean_ctor_set_tag(v___x_158_, 3);
lean_ctor_set(v___x_158_, 0, v___x_163_);
v___x_165_ = v___x_158_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_163_);
v___x_165_ = v_reuseFailAlloc_171_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
lean_object* v___x_166_; lean_object* v___x_167_; uint8_t v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_166_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_162_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
lean_inc(v___y_161_);
v___x_167_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_167_, 0, v___y_161_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
v___x_168_ = 0;
v___x_169_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_169_, 0, v___x_167_);
lean_ctor_set_uint8(v___x_169_, sizeof(void*)*1, v___x_168_);
v___x_170_ = l_Repr_addAppParen(v___x_169_, v_prec_155_);
return v___x_170_;
}
}
}
}
case 1:
{
lean_object* v_i_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_197_; 
v_i_177_ = lean_ctor_get(v_x_154_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v_x_154_);
if (v_isSharedCheck_197_ == 0)
{
v___x_179_ = v_x_154_;
v_isShared_180_ = v_isSharedCheck_197_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_i_177_);
lean_dec(v_x_154_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_197_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___y_182_; lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_193_ = lean_unsigned_to_nat(1024u);
v___x_194_ = lean_nat_dec_le(v___x_193_, v_prec_155_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; 
v___x_195_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3, &l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3);
v___y_182_ = v___x_195_;
goto v___jp_181_;
}
else
{
lean_object* v___x_196_; 
v___x_196_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4, &l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4_once, _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4);
v___y_182_ = v___x_196_;
goto v___jp_181_;
}
v___jp_181_:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_186_; 
v___x_183_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__7));
v___x_184_ = l_Nat_reprFast(v_i_177_);
if (v_isShared_180_ == 0)
{
lean_ctor_set_tag(v___x_179_, 3);
lean_ctor_set(v___x_179_, 0, v___x_184_);
v___x_186_ = v___x_179_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_184_);
v___x_186_ = v_reuseFailAlloc_192_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
lean_object* v___x_187_; lean_object* v___x_188_; uint8_t v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_187_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_183_);
lean_ctor_set(v___x_187_, 1, v___x_186_);
lean_inc(v___y_182_);
v___x_188_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_188_, 0, v___y_182_);
lean_ctor_set(v___x_188_, 1, v___x_187_);
v___x_189_ = 0;
v___x_190_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_190_, 0, v___x_188_);
lean_ctor_set_uint8(v___x_190_, sizeof(void*)*1, v___x_189_);
v___x_191_ = l_Repr_addAppParen(v___x_190_, v_prec_155_);
return v___x_191_;
}
}
}
}
case 2:
{
lean_object* v_a_198_; lean_object* v_b_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_222_; 
v_a_198_ = lean_ctor_get(v_x_154_, 0);
v_b_199_ = lean_ctor_get(v_x_154_, 1);
v_isSharedCheck_222_ = !lean_is_exclusive(v_x_154_);
if (v_isSharedCheck_222_ == 0)
{
v___x_201_ = v_x_154_;
v_isShared_202_ = v_isSharedCheck_222_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_b_199_);
lean_inc(v_a_198_);
lean_dec(v_x_154_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_222_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_203_; lean_object* v___y_205_; uint8_t v___x_219_; 
v___x_203_ = lean_unsigned_to_nat(1024u);
v___x_219_ = lean_nat_dec_le(v___x_203_, v_prec_155_);
if (v___x_219_ == 0)
{
lean_object* v___x_220_; 
v___x_220_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3, &l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3);
v___y_205_ = v___x_220_;
goto v___jp_204_;
}
else
{
lean_object* v___x_221_; 
v___x_221_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4, &l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4_once, _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4);
v___y_205_ = v___x_221_;
goto v___jp_204_;
}
v___jp_204_:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_210_; 
v___x_206_ = lean_box(1);
v___x_207_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__10));
v___x_208_ = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(v_a_198_, v___x_203_);
if (v_isShared_202_ == 0)
{
lean_ctor_set_tag(v___x_201_, 5);
lean_ctor_set(v___x_201_, 1, v___x_208_);
lean_ctor_set(v___x_201_, 0, v___x_207_);
v___x_210_ = v___x_201_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_207_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v___x_208_);
v___x_210_ = v_reuseFailAlloc_218_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; uint8_t v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_211_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
lean_ctor_set(v___x_211_, 1, v___x_206_);
v___x_212_ = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(v_b_199_, v___x_203_);
v___x_213_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_211_);
lean_ctor_set(v___x_213_, 1, v___x_212_);
lean_inc(v___y_205_);
v___x_214_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_214_, 0, v___y_205_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
v___x_215_ = 0;
v___x_216_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_216_, 0, v___x_214_);
lean_ctor_set_uint8(v___x_216_, sizeof(void*)*1, v___x_215_);
v___x_217_ = l_Repr_addAppParen(v___x_216_, v_prec_155_);
return v___x_217_;
}
}
}
}
case 3:
{
lean_object* v_k_223_; lean_object* v_a_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_248_; 
v_k_223_ = lean_ctor_get(v_x_154_, 0);
v_a_224_ = lean_ctor_get(v_x_154_, 1);
v_isSharedCheck_248_ = !lean_is_exclusive(v_x_154_);
if (v_isSharedCheck_248_ == 0)
{
v___x_226_ = v_x_154_;
v_isShared_227_ = v_isSharedCheck_248_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_a_224_);
lean_inc(v_k_223_);
lean_dec(v_x_154_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_248_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_228_; lean_object* v___y_230_; uint8_t v___x_245_; 
v___x_228_ = lean_unsigned_to_nat(1024u);
v___x_245_ = lean_nat_dec_le(v___x_228_, v_prec_155_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; 
v___x_246_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3, &l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3);
v___y_230_ = v___x_246_;
goto v___jp_229_;
}
else
{
lean_object* v___x_247_; 
v___x_247_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4, &l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4_once, _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4);
v___y_230_ = v___x_247_;
goto v___jp_229_;
}
v___jp_229_:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_231_ = lean_box(1);
v___x_232_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__13));
v___x_233_ = l_Nat_reprFast(v_k_223_);
v___x_234_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
if (v_isShared_227_ == 0)
{
lean_ctor_set_tag(v___x_226_, 5);
lean_ctor_set(v___x_226_, 1, v___x_234_);
lean_ctor_set(v___x_226_, 0, v___x_232_);
v___x_236_ = v___x_226_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_232_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v___x_234_);
v___x_236_ = v_reuseFailAlloc_244_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; uint8_t v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_237_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
lean_ctor_set(v___x_237_, 1, v___x_231_);
v___x_238_ = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(v_a_224_, v___x_228_);
v___x_239_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_237_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
lean_inc(v___y_230_);
v___x_240_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_240_, 0, v___y_230_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
v___x_241_ = 0;
v___x_242_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_242_, 0, v___x_240_);
lean_ctor_set_uint8(v___x_242_, sizeof(void*)*1, v___x_241_);
v___x_243_ = l_Repr_addAppParen(v___x_242_, v_prec_155_);
return v___x_243_;
}
}
}
}
default: 
{
lean_object* v_a_249_; lean_object* v_k_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_274_; 
v_a_249_ = lean_ctor_get(v_x_154_, 0);
v_k_250_ = lean_ctor_get(v_x_154_, 1);
v_isSharedCheck_274_ = !lean_is_exclusive(v_x_154_);
if (v_isSharedCheck_274_ == 0)
{
v___x_252_ = v_x_154_;
v_isShared_253_ = v_isSharedCheck_274_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_k_250_);
lean_inc(v_a_249_);
lean_dec(v_x_154_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_274_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_254_; lean_object* v___y_256_; uint8_t v___x_271_; 
v___x_254_ = lean_unsigned_to_nat(1024u);
v___x_271_ = lean_nat_dec_le(v___x_254_, v_prec_155_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; 
v___x_272_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3, &l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3);
v___y_256_ = v___x_272_;
goto v___jp_255_;
}
else
{
lean_object* v___x_273_; 
v___x_273_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4, &l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4_once, _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4);
v___y_256_ = v___x_273_;
goto v___jp_255_;
}
v___jp_255_:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_261_; 
v___x_257_ = lean_box(1);
v___x_258_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__16));
v___x_259_ = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(v_a_249_, v___x_254_);
if (v_isShared_253_ == 0)
{
lean_ctor_set_tag(v___x_252_, 5);
lean_ctor_set(v___x_252_, 1, v___x_259_);
lean_ctor_set(v___x_252_, 0, v___x_258_);
v___x_261_ = v___x_252_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v___x_258_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v___x_259_);
v___x_261_ = v_reuseFailAlloc_270_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; uint8_t v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_262_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
lean_ctor_set(v___x_262_, 1, v___x_257_);
v___x_263_ = l_Nat_reprFast(v_k_250_);
v___x_264_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
v___x_265_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_262_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
lean_inc(v___y_256_);
v___x_266_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_266_, 0, v___y_256_);
lean_ctor_set(v___x_266_, 1, v___x_265_);
v___x_267_ = 0;
v___x_268_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_268_, 0, v___x_266_);
lean_ctor_set_uint8(v___x_268_, sizeof(void*)*1, v___x_267_);
v___x_269_ = l_Repr_addAppParen(v___x_268_, v_prec_155_);
return v___x_269_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___boxed(lean_object* v_x_275_, lean_object* v_prec_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(v_x_275_, v_prec_276_);
lean_dec(v_prec_276_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr_spec__0(lean_object* v_a_280_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = lean_nat_to_int(v_a_280_);
return v___x_281_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = lean_unsigned_to_nat(6u);
v___x_296_ = lean_nat_to_int(v___x_295_);
return v___x_296_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = lean_unsigned_to_nat(7u);
v___x_304_ = lean_nat_to_int(v___x_303_);
return v___x_304_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__0));
v___x_310_ = lean_string_length(v___x_309_);
return v___x_310_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__16, &l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__16_once, _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__16);
v___x_312_ = lean_nat_to_int(v___x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg(lean_object* v_x_317_){
_start:
{
uint8_t v_eq_318_; lean_object* v_lhs_319_; lean_object* v_rhs_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; uint8_t v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v_eq_318_ = lean_ctor_get_uint8(v_x_317_, sizeof(void*)*2);
v_lhs_319_ = lean_ctor_get(v_x_317_, 0);
lean_inc_ref(v_lhs_319_);
v_rhs_320_ = lean_ctor_get(v_x_317_, 1);
lean_inc_ref(v_rhs_320_);
lean_dec_ref(v_x_317_);
v___x_321_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__5));
v___x_322_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__6));
v___x_323_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7, &l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7_once, _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7);
v___x_324_ = lean_unsigned_to_nat(0u);
v___x_325_ = l_Bool_repr___redArg(v_eq_318_);
v___x_326_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_323_);
lean_ctor_set(v___x_326_, 1, v___x_325_);
v___x_327_ = 0;
v___x_328_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_328_, 0, v___x_326_);
lean_ctor_set_uint8(v___x_328_, sizeof(void*)*1, v___x_327_);
v___x_329_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_322_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
v___x_330_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__9));
v___x_331_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_329_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
v___x_332_ = lean_box(1);
v___x_333_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_331_);
lean_ctor_set(v___x_333_, 1, v___x_332_);
v___x_334_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__11));
v___x_335_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_333_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
v___x_336_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v___x_321_);
v___x_337_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12, &l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12);
v___x_338_ = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(v_lhs_319_, v___x_324_);
v___x_339_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_337_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
v___x_340_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set_uint8(v___x_340_, sizeof(void*)*1, v___x_327_);
v___x_341_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_336_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
v___x_342_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v___x_330_);
v___x_343_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v___x_332_);
v___x_344_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__14));
v___x_345_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_343_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
v___x_346_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set(v___x_346_, 1, v___x_321_);
v___x_347_ = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(v_rhs_320_, v___x_324_);
v___x_348_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_337_);
lean_ctor_set(v___x_348_, 1, v___x_347_);
v___x_349_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_349_, 0, v___x_348_);
lean_ctor_set_uint8(v___x_349_, sizeof(void*)*1, v___x_327_);
v___x_350_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_346_);
lean_ctor_set(v___x_350_, 1, v___x_349_);
v___x_351_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17, &l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17);
v___x_352_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__18));
v___x_353_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
lean_ctor_set(v___x_353_, 1, v___x_350_);
v___x_354_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__19));
v___x_355_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_353_);
lean_ctor_set(v___x_355_, 1, v___x_354_);
v___x_356_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_351_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
v___x_357_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_357_, 0, v___x_356_);
lean_ctor_set_uint8(v___x_357_, sizeof(void*)*1, v___x_327_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr(lean_object* v_x_358_, lean_object* v_prec_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg(v_x_358_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___boxed(lean_object* v_x_361_, lean_object* v_prec_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr(v_x_361_, v_prec_362_);
lean_dec(v_prec_362_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_366_, lean_object* v_x_367_, lean_object* v_x_368_){
_start:
{
if (lean_obj_tag(v_x_368_) == 0)
{
lean_dec(v_x_366_);
return v_x_367_;
}
else
{
lean_object* v_head_369_; lean_object* v_tail_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_379_; 
v_head_369_ = lean_ctor_get(v_x_368_, 0);
v_tail_370_ = lean_ctor_get(v_x_368_, 1);
v_isSharedCheck_379_ = !lean_is_exclusive(v_x_368_);
if (v_isSharedCheck_379_ == 0)
{
v___x_372_ = v_x_368_;
v_isShared_373_ = v_isSharedCheck_379_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_tail_370_);
lean_inc(v_head_369_);
lean_dec(v_x_368_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_379_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_375_; 
lean_inc(v_x_366_);
if (v_isShared_373_ == 0)
{
lean_ctor_set_tag(v___x_372_, 5);
lean_ctor_set(v___x_372_, 1, v_x_366_);
lean_ctor_set(v___x_372_, 0, v_x_367_);
v___x_375_ = v___x_372_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_x_367_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_x_366_);
v___x_375_ = v_reuseFailAlloc_378_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
lean_object* v___x_376_; 
v___x_376_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
lean_ctor_set(v___x_376_, 1, v_head_369_);
v_x_367_ = v___x_376_;
v_x_368_ = v_tail_370_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0_spec__1(lean_object* v_x_380_, lean_object* v_x_381_){
_start:
{
if (lean_obj_tag(v_x_380_) == 0)
{
lean_object* v___x_382_; 
lean_dec(v_x_381_);
v___x_382_ = lean_box(0);
return v___x_382_;
}
else
{
lean_object* v_tail_383_; 
v_tail_383_ = lean_ctor_get(v_x_380_, 1);
if (lean_obj_tag(v_tail_383_) == 0)
{
lean_object* v_head_384_; 
lean_dec(v_x_381_);
v_head_384_ = lean_ctor_get(v_x_380_, 0);
lean_inc(v_head_384_);
lean_dec_ref_known(v_x_380_, 2);
return v_head_384_;
}
else
{
lean_object* v_head_385_; lean_object* v___x_386_; 
lean_inc(v_tail_383_);
v_head_385_ = lean_ctor_get(v_x_380_, 0);
lean_inc(v_head_385_);
lean_dec_ref_known(v_x_380_, 2);
v___x_386_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0_spec__1_spec__2(v_x_381_, v_head_385_, v_tail_383_);
return v___x_386_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__0));
v___x_393_ = lean_string_length(v___x_392_);
return v___x_393_;
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__3, &l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__3_once, _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__3);
v___x_395_ = lean_nat_to_int(v___x_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg(lean_object* v_x_400_){
_start:
{
lean_object* v_fst_401_; lean_object* v_snd_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_426_; 
v_fst_401_ = lean_ctor_get(v_x_400_, 0);
v_snd_402_ = lean_ctor_get(v_x_400_, 1);
v_isSharedCheck_426_ = !lean_is_exclusive(v_x_400_);
if (v_isSharedCheck_426_ == 0)
{
v___x_404_ = v_x_400_;
v_isShared_405_ = v_isSharedCheck_426_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_snd_402_);
lean_inc(v_fst_401_);
lean_dec(v_x_400_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_426_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_406_ = l_Nat_reprFast(v_fst_401_);
v___x_407_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
v___x_408_ = lean_box(0);
if (v_isShared_405_ == 0)
{
lean_ctor_set_tag(v___x_404_, 1);
lean_ctor_set(v___x_404_, 1, v___x_408_);
lean_ctor_set(v___x_404_, 0, v___x_407_);
v___x_410_ = v___x_404_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_407_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v___x_408_);
v___x_410_ = v_reuseFailAlloc_425_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; uint8_t v___x_423_; lean_object* v___x_424_; 
v___x_411_ = l_Nat_reprFast(v_snd_402_);
v___x_412_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
v___x_413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
lean_ctor_set(v___x_413_, 1, v___x_410_);
v___x_414_ = l_List_reverse___redArg(v___x_413_);
v___x_415_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__1));
v___x_416_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0_spec__1(v___x_414_, v___x_415_);
v___x_417_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__4, &l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__4_once, _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__4);
v___x_418_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__5));
v___x_419_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
lean_ctor_set(v___x_419_, 1, v___x_416_);
v___x_420_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__6));
v___x_421_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_419_);
lean_ctor_set(v___x_421_, 1, v___x_420_);
v___x_422_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_417_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
v___x_423_ = 0;
v___x_424_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_424_, 0, v___x_422_);
lean_ctor_set_uint8(v___x_424_, sizeof(void*)*1, v___x_423_);
return v___x_424_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__1_spec__3_spec__5(lean_object* v_x_427_, lean_object* v_x_428_, lean_object* v_x_429_){
_start:
{
if (lean_obj_tag(v_x_429_) == 0)
{
lean_dec(v_x_427_);
return v_x_428_;
}
else
{
lean_object* v_head_430_; lean_object* v_tail_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_441_; 
v_head_430_ = lean_ctor_get(v_x_429_, 0);
v_tail_431_ = lean_ctor_get(v_x_429_, 1);
v_isSharedCheck_441_ = !lean_is_exclusive(v_x_429_);
if (v_isSharedCheck_441_ == 0)
{
v___x_433_ = v_x_429_;
v_isShared_434_ = v_isSharedCheck_441_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_tail_431_);
lean_inc(v_head_430_);
lean_dec(v_x_429_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_441_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_436_; 
lean_inc(v_x_427_);
if (v_isShared_434_ == 0)
{
lean_ctor_set_tag(v___x_433_, 5);
lean_ctor_set(v___x_433_, 1, v_x_427_);
lean_ctor_set(v___x_433_, 0, v_x_428_);
v___x_436_ = v___x_433_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_x_428_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v_x_427_);
v___x_436_ = v_reuseFailAlloc_440_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg(v_head_430_);
v___x_438_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_436_);
lean_ctor_set(v___x_438_, 1, v___x_437_);
v_x_428_ = v___x_438_;
v_x_429_ = v_tail_431_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__1_spec__3(lean_object* v_x_442_, lean_object* v_x_443_, lean_object* v_x_444_){
_start:
{
if (lean_obj_tag(v_x_444_) == 0)
{
lean_dec(v_x_442_);
return v_x_443_;
}
else
{
lean_object* v_head_445_; lean_object* v_tail_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_456_; 
v_head_445_ = lean_ctor_get(v_x_444_, 0);
v_tail_446_ = lean_ctor_get(v_x_444_, 1);
v_isSharedCheck_456_ = !lean_is_exclusive(v_x_444_);
if (v_isSharedCheck_456_ == 0)
{
v___x_448_ = v_x_444_;
v_isShared_449_ = v_isSharedCheck_456_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_tail_446_);
lean_inc(v_head_445_);
lean_dec(v_x_444_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_456_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
lean_inc(v_x_442_);
if (v_isShared_449_ == 0)
{
lean_ctor_set_tag(v___x_448_, 5);
lean_ctor_set(v___x_448_, 1, v_x_442_);
lean_ctor_set(v___x_448_, 0, v_x_443_);
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_x_443_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_x_442_);
v___x_451_ = v_reuseFailAlloc_455_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_452_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg(v_head_445_);
v___x_453_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_451_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
v___x_454_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__1_spec__3_spec__5(v_x_442_, v___x_453_, v_tail_446_);
return v___x_454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__1(lean_object* v_x_457_, lean_object* v_x_458_){
_start:
{
if (lean_obj_tag(v_x_457_) == 0)
{
lean_object* v___x_459_; 
lean_dec(v_x_458_);
v___x_459_ = lean_box(0);
return v___x_459_;
}
else
{
lean_object* v_tail_460_; 
v_tail_460_ = lean_ctor_get(v_x_457_, 1);
if (lean_obj_tag(v_tail_460_) == 0)
{
lean_object* v_head_461_; lean_object* v___x_462_; 
lean_dec(v_x_458_);
v_head_461_ = lean_ctor_get(v_x_457_, 0);
lean_inc(v_head_461_);
lean_dec_ref_known(v_x_457_, 2);
v___x_462_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg(v_head_461_);
return v___x_462_;
}
else
{
lean_object* v_head_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
lean_inc(v_tail_460_);
v_head_463_ = lean_ctor_get(v_x_457_, 0);
lean_inc(v_head_463_);
lean_dec_ref_known(v_x_457_, 2);
v___x_464_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg(v_head_463_);
v___x_465_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__1_spec__3(v_x_458_, v___x_464_, v_tail_460_);
return v___x_465_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = ((lean_object*)(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__2));
v___x_472_ = lean_string_length(v___x_471_);
return v___x_472_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = lean_obj_once(&l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__4, &l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__4_once, _init_l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__4);
v___x_474_ = lean_nat_to_int(v___x_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg(lean_object* v_a_479_){
_start:
{
if (lean_obj_tag(v_a_479_) == 0)
{
lean_object* v___x_480_; 
v___x_480_ = ((lean_object*)(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__1));
return v___x_480_;
}
else
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; lean_object* v___x_490_; 
v___x_481_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__1));
v___x_482_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__1(v_a_479_, v___x_481_);
v___x_483_ = lean_obj_once(&l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__5, &l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__5_once, _init_l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__5);
v___x_484_ = ((lean_object*)(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__6));
v___x_485_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
lean_ctor_set(v___x_485_, 1, v___x_482_);
v___x_486_ = ((lean_object*)(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__7));
v___x_487_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_485_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
v___x_488_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_483_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
v___x_489_ = 0;
v___x_490_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_490_, 0, v___x_488_);
lean_ctor_set_uint8(v___x_490_, sizeof(void*)*1, v___x_489_);
return v___x_490_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr___redArg(lean_object* v_x_491_){
_start:
{
uint8_t v_eq_492_; lean_object* v_lhs_493_; lean_object* v_rhs_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; uint8_t v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v_eq_492_ = lean_ctor_get_uint8(v_x_491_, sizeof(void*)*2);
v_lhs_493_ = lean_ctor_get(v_x_491_, 0);
lean_inc(v_lhs_493_);
v_rhs_494_ = lean_ctor_get(v_x_491_, 1);
lean_inc(v_rhs_494_);
lean_dec_ref(v_x_491_);
v___x_495_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__5));
v___x_496_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__6));
v___x_497_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7, &l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7_once, _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7);
v___x_498_ = l_Bool_repr___redArg(v_eq_492_);
v___x_499_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_497_);
lean_ctor_set(v___x_499_, 1, v___x_498_);
v___x_500_ = 0;
v___x_501_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_501_, 0, v___x_499_);
lean_ctor_set_uint8(v___x_501_, sizeof(void*)*1, v___x_500_);
v___x_502_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_502_, 0, v___x_496_);
lean_ctor_set(v___x_502_, 1, v___x_501_);
v___x_503_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__9));
v___x_504_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_502_);
lean_ctor_set(v___x_504_, 1, v___x_503_);
v___x_505_ = lean_box(1);
v___x_506_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_504_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
v___x_507_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__11));
v___x_508_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_506_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
v___x_509_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
lean_ctor_set(v___x_509_, 1, v___x_495_);
v___x_510_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12, &l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12);
v___x_511_ = l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg(v_lhs_493_);
v___x_512_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_510_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
v___x_513_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_513_, 0, v___x_512_);
lean_ctor_set_uint8(v___x_513_, sizeof(void*)*1, v___x_500_);
v___x_514_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_509_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
v___x_515_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
lean_ctor_set(v___x_515_, 1, v___x_503_);
v___x_516_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
lean_ctor_set(v___x_516_, 1, v___x_505_);
v___x_517_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__14));
v___x_518_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_516_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
v___x_519_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
lean_ctor_set(v___x_519_, 1, v___x_495_);
v___x_520_ = l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg(v_rhs_494_);
v___x_521_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_510_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
v___x_522_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_522_, 0, v___x_521_);
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*1, v___x_500_);
v___x_523_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_519_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
v___x_524_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17, &l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17);
v___x_525_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__18));
v___x_526_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
lean_ctor_set(v___x_526_, 1, v___x_523_);
v___x_527_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__19));
v___x_528_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_526_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
v___x_529_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_524_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
v___x_530_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_530_, 0, v___x_529_);
lean_ctor_set_uint8(v___x_530_, sizeof(void*)*1, v___x_500_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr(lean_object* v_x_531_, lean_object* v_prec_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr___redArg(v_x_531_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr___boxed(lean_object* v_x_534_, lean_object* v_prec_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr(v_x_534_, v_prec_535_);
lean_dec(v_prec_535_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0(lean_object* v_a_537_, lean_object* v_n_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg(v_a_537_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___boxed(lean_object* v_a_540_, lean_object* v_n_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0(v_a_540_, v_n_541_);
lean_dec(v_n_541_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0(lean_object* v_x_543_, lean_object* v_x_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg(v_x_543_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___boxed(lean_object* v_x_546_, lean_object* v_x_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0(v_x_546_, v_x_547_);
lean_dec(v_x_547_);
return v_res_548_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__6(void){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_562_ = lean_box(0);
v___x_563_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__5));
v___x_564_ = l_Lean_mkConst(v___x_563_, v___x_562_);
return v___x_564_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__9(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_572_ = lean_box(0);
v___x_573_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__8));
v___x_574_ = l_Lean_mkConst(v___x_573_, v___x_572_);
return v___x_574_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__12(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_582_ = lean_box(0);
v___x_583_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__11));
v___x_584_ = l_Lean_mkConst(v___x_583_, v___x_582_);
return v___x_584_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__15(void){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_592_ = lean_box(0);
v___x_593_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__14));
v___x_594_ = l_Lean_mkConst(v___x_593_, v___x_592_);
return v___x_594_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__18(void){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_602_ = lean_box(0);
v___x_603_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__17));
v___x_604_ = l_Lean_mkConst(v___x_603_, v___x_602_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(lean_object* v_e_605_){
_start:
{
switch(lean_obj_tag(v_e_605_))
{
case 0:
{
lean_object* v_v_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v_v_606_ = lean_ctor_get(v_e_605_, 0);
lean_inc(v_v_606_);
lean_dec_ref_known(v_e_605_, 1);
v___x_607_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__6, &l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__6_once, _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__6);
v___x_608_ = l_Lean_mkNatLit(v_v_606_);
v___x_609_ = l_Lean_Expr_app___override(v___x_607_, v___x_608_);
return v___x_609_;
}
case 1:
{
lean_object* v_i_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v_i_610_ = lean_ctor_get(v_e_605_, 0);
lean_inc(v_i_610_);
lean_dec_ref_known(v_e_605_, 1);
v___x_611_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__9, &l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__9_once, _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__9);
v___x_612_ = l_Lean_mkNatLit(v_i_610_);
v___x_613_ = l_Lean_Expr_app___override(v___x_611_, v___x_612_);
return v___x_613_;
}
case 2:
{
lean_object* v_a_614_; lean_object* v_b_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v_a_614_ = lean_ctor_get(v_e_605_, 0);
lean_inc_ref(v_a_614_);
v_b_615_ = lean_ctor_get(v_e_605_, 1);
lean_inc_ref(v_b_615_);
lean_dec_ref_known(v_e_605_, 2);
v___x_616_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__12, &l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__12);
v___x_617_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v_a_614_);
v___x_618_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v_b_615_);
v___x_619_ = l_Lean_mkAppB(v___x_616_, v___x_617_, v___x_618_);
return v___x_619_;
}
case 3:
{
lean_object* v_k_620_; lean_object* v_a_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v_k_620_ = lean_ctor_get(v_e_605_, 0);
lean_inc(v_k_620_);
v_a_621_ = lean_ctor_get(v_e_605_, 1);
lean_inc_ref(v_a_621_);
lean_dec_ref_known(v_e_605_, 2);
v___x_622_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__15, &l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__15_once, _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__15);
v___x_623_ = l_Lean_mkNatLit(v_k_620_);
v___x_624_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v_a_621_);
v___x_625_ = l_Lean_mkAppB(v___x_622_, v___x_623_, v___x_624_);
return v___x_625_;
}
default: 
{
lean_object* v_a_626_; lean_object* v_k_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v_a_626_ = lean_ctor_get(v_e_605_, 0);
lean_inc_ref(v_a_626_);
v_k_627_ = lean_ctor_get(v_e_605_, 1);
lean_inc(v_k_627_);
lean_dec_ref_known(v_e_605_, 2);
v___x_628_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__18, &l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__18_once, _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__18);
v___x_629_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v_a_626_);
v___x_630_ = l_Lean_mkNatLit(v_k_627_);
v___x_631_ = l_Lean_mkAppB(v___x_628_, v___x_629_, v___x_630_);
return v___x_631_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__2(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_638_ = lean_box(0);
v___x_639_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1));
v___x_640_ = l_Lean_mkConst(v___x_639_, v___x_638_);
return v___x_640_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__3(void){
_start:
{
lean_object* v___x_641_; lean_object* v___f_642_; lean_object* v___x_643_; 
v___x_641_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__2, &l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__2);
v___f_642_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__0));
v___x_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_643_, 0, v___f_642_);
lean_ctor_set(v___x_643_, 1, v___x_641_);
return v___x_643_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr(void){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__3, &l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__3);
return v___x_644_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__3(void){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_653_ = lean_box(0);
v___x_654_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2));
v___x_655_ = l_Lean_mkConst(v___x_654_, v___x_653_);
return v___x_655_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__7(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_661_ = lean_box(0);
v___x_662_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__6));
v___x_663_ = l_Lean_mkConst(v___x_662_, v___x_661_);
return v___x_663_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__10(void){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_668_ = lean_box(0);
v___x_669_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__9));
v___x_670_ = l_Lean_mkConst(v___x_669_, v___x_668_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(lean_object* v_c_671_){
_start:
{
uint8_t v_eq_672_; lean_object* v_lhs_673_; lean_object* v_rhs_674_; lean_object* v___x_675_; lean_object* v___y_677_; 
v_eq_672_ = lean_ctor_get_uint8(v_c_671_, sizeof(void*)*2);
v_lhs_673_ = lean_ctor_get(v_c_671_, 0);
lean_inc_ref(v_lhs_673_);
v_rhs_674_ = lean_ctor_get(v_c_671_, 1);
lean_inc_ref(v_rhs_674_);
lean_dec_ref(v_c_671_);
v___x_675_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__3, &l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__3);
if (v_eq_672_ == 0)
{
lean_object* v___x_681_; 
v___x_681_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__7, &l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__7_once, _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__7);
v___y_677_ = v___x_681_;
goto v___jp_676_;
}
else
{
lean_object* v___x_682_; 
v___x_682_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__10, &l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__10_once, _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__10);
v___y_677_ = v___x_682_;
goto v___jp_676_;
}
v___jp_676_:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_678_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v_lhs_673_);
v___x_679_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v_rhs_674_);
lean_inc_ref(v___y_677_);
v___x_680_ = l_Lean_mkApp3(v___x_675_, v___y_677_, v___x_678_, v___x_679_);
return v___x_680_;
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__2(void){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_689_ = lean_box(0);
v___x_690_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1));
v___x_691_ = l_Lean_mkConst(v___x_690_, v___x_689_);
return v___x_691_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__3(void){
_start:
{
lean_object* v___x_692_; lean_object* v___f_693_; lean_object* v___x_694_; 
v___x_692_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__2, &l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__2);
v___f_693_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__0));
v___x_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_694_, 0, v___f_693_);
lean_ctor_set(v___x_694_, 1, v___x_692_);
return v___x_694_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr(void){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__3, &l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__3);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(lean_object* v_ctx_696_, lean_object* v_e_697_){
_start:
{
switch(lean_obj_tag(v_e_697_))
{
case 0:
{
lean_object* v_v_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_707_; 
v_v_699_ = lean_ctor_get(v_e_697_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v_e_697_);
if (v_isSharedCheck_707_ == 0)
{
v___x_701_ = v_e_697_;
v_isShared_702_ = v_isSharedCheck_707_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_v_699_);
lean_dec(v_e_697_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_707_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_703_; lean_object* v___x_705_; 
v___x_703_ = l_Lean_mkNatLit(v_v_699_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 0, v___x_703_);
v___x_705_ = v___x_701_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
case 1:
{
lean_object* v_i_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_717_; 
v_i_708_ = lean_ctor_get(v_e_697_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v_e_697_);
if (v_isSharedCheck_717_ == 0)
{
v___x_710_ = v_e_697_;
v_isShared_711_ = v_isSharedCheck_717_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_i_708_);
lean_dec(v_e_697_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_717_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_715_; 
v___x_712_ = l_Lean_instInhabitedExpr;
v___x_713_ = lean_array_get_borrowed(v___x_712_, v_ctx_696_, v_i_708_);
lean_dec(v_i_708_);
lean_inc(v___x_713_);
if (v_isShared_711_ == 0)
{
lean_ctor_set_tag(v___x_710_, 0);
lean_ctor_set(v___x_710_, 0, v___x_713_);
v___x_715_ = v___x_710_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_713_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
case 2:
{
lean_object* v_a_718_; lean_object* v_b_719_; lean_object* v___x_720_; lean_object* v_a_721_; lean_object* v___x_722_; lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_731_; 
v_a_718_ = lean_ctor_get(v_e_697_, 0);
lean_inc_ref(v_a_718_);
v_b_719_ = lean_ctor_get(v_e_697_, 1);
lean_inc_ref(v_b_719_);
lean_dec_ref_known(v_e_697_, 2);
v___x_720_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_ctx_696_, v_a_718_);
v_a_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_a_721_);
lean_dec_ref(v___x_720_);
v___x_722_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_ctx_696_, v_b_719_);
v_a_723_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_731_ == 0)
{
v___x_725_ = v___x_722_;
v_isShared_726_ = v_isSharedCheck_731_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_722_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_731_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_727_; lean_object* v___x_729_; 
v___x_727_ = l_Lean_mkNatAdd(v_a_721_, v_a_723_);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 0, v___x_727_);
v___x_729_ = v___x_725_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_727_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
case 3:
{
lean_object* v_k_732_; lean_object* v_a_733_; lean_object* v___x_734_; lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_744_; 
v_k_732_ = lean_ctor_get(v_e_697_, 0);
lean_inc(v_k_732_);
v_a_733_ = lean_ctor_get(v_e_697_, 1);
lean_inc_ref(v_a_733_);
lean_dec_ref_known(v_e_697_, 2);
v___x_734_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_ctx_696_, v_a_733_);
v_a_735_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_744_ == 0)
{
v___x_737_ = v___x_734_;
v_isShared_738_ = v_isSharedCheck_744_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_734_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_744_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_742_; 
v___x_739_ = l_Lean_mkNatLit(v_k_732_);
v___x_740_ = l_Lean_mkNatMul(v___x_739_, v_a_735_);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 0, v___x_740_);
v___x_742_ = v___x_737_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
default: 
{
lean_object* v_a_745_; lean_object* v_k_746_; lean_object* v___x_747_; lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_757_; 
v_a_745_ = lean_ctor_get(v_e_697_, 0);
lean_inc_ref(v_a_745_);
v_k_746_ = lean_ctor_get(v_e_697_, 1);
lean_inc(v_k_746_);
lean_dec_ref_known(v_e_697_, 2);
v___x_747_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_ctx_696_, v_a_745_);
v_a_748_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_757_ == 0)
{
v___x_750_ = v___x_747_;
v_isShared_751_ = v_isSharedCheck_757_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_747_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_757_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_755_; 
v___x_752_ = l_Lean_mkNatLit(v_k_746_);
v___x_753_ = l_Lean_mkNatMul(v_a_748_, v___x_752_);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 0, v___x_753_);
v___x_755_ = v___x_750_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_753_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg___boxed(lean_object* v_ctx_758_, lean_object* v_e_759_, lean_object* v_a_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_ctx_758_, v_e_759_);
lean_dec_ref(v_ctx_758_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith(lean_object* v_ctx_762_, lean_object* v_e_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_ctx_762_, v_e_763_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___boxed(lean_object* v_ctx_770_, lean_object* v_e_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith(v_ctx_770_, v_e_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_);
lean_dec(v_a_775_);
lean_dec_ref(v_a_774_);
lean_dec(v_a_773_);
lean_dec_ref(v_a_772_);
lean_dec_ref(v_ctx_770_);
return v_res_777_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg___closed__0(void){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = lean_unsigned_to_nat(0u);
v___x_779_ = l_Lean_Level_ofNat(v___x_778_);
return v___x_779_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg___closed__1(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = lean_unsigned_to_nat(1u);
v___x_781_ = l_Lean_Level_ofNat(v___x_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(lean_object* v_ctx_782_, lean_object* v_c_783_, lean_object* v_a_784_, lean_object* v_a_785_){
_start:
{
uint8_t v_eq_787_; 
v_eq_787_ = lean_ctor_get_uint8(v_c_783_, sizeof(void*)*2);
if (v_eq_787_ == 0)
{
lean_object* v_lhs_788_; lean_object* v_rhs_789_; lean_object* v___x_790_; 
v_lhs_788_ = lean_ctor_get(v_c_783_, 0);
lean_inc_ref(v_lhs_788_);
v_rhs_789_ = lean_ctor_get(v_c_783_, 1);
lean_inc_ref(v_rhs_789_);
lean_dec_ref(v_c_783_);
v___x_790_ = l_Lean_leCarrierIsSort(v_a_784_, v_a_785_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v_a_791_; lean_object* v_____do__lift_793_; uint8_t v___x_806_; 
v_a_791_ = lean_ctor_get(v___x_790_, 0);
lean_inc(v_a_791_);
lean_dec_ref_known(v___x_790_, 1);
v___x_806_ = lean_unbox(v_a_791_);
lean_dec(v_a_791_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; 
v___x_807_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg___closed__0, &l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg___closed__0_once, _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg___closed__0);
v_____do__lift_793_ = v___x_807_;
goto v___jp_792_;
}
else
{
lean_object* v___x_808_; 
v___x_808_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg___closed__1, &l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg___closed__1_once, _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg___closed__1);
v_____do__lift_793_ = v___x_808_;
goto v___jp_792_;
}
v___jp_792_:
{
lean_object* v___x_794_; lean_object* v_a_795_; lean_object* v___x_796_; lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_805_; 
v___x_794_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_ctx_782_, v_lhs_788_);
v_a_795_ = lean_ctor_get(v___x_794_, 0);
lean_inc(v_a_795_);
lean_dec_ref(v___x_794_);
v___x_796_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_ctx_782_, v_rhs_789_);
v_a_797_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_805_ == 0)
{
v___x_799_ = v___x_796_;
v_isShared_800_ = v_isSharedCheck_805_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_796_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_805_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_801_; lean_object* v___x_803_; 
lean_inc(v_____do__lift_793_);
v___x_801_ = l_Lean_mkNatLE(v_____do__lift_793_, v_a_795_, v_a_797_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v___x_801_);
v___x_803_ = v___x_799_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_801_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
else
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_dec_ref(v_rhs_789_);
lean_dec_ref(v_lhs_788_);
v_a_809_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_790_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_790_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_809_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
else
{
lean_object* v_lhs_817_; lean_object* v_rhs_818_; lean_object* v___x_819_; lean_object* v_a_820_; lean_object* v___x_821_; lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_830_; 
v_lhs_817_ = lean_ctor_get(v_c_783_, 0);
lean_inc_ref(v_lhs_817_);
v_rhs_818_ = lean_ctor_get(v_c_783_, 1);
lean_inc_ref(v_rhs_818_);
lean_dec_ref(v_c_783_);
v___x_819_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_ctx_782_, v_lhs_817_);
v_a_820_ = lean_ctor_get(v___x_819_, 0);
lean_inc(v_a_820_);
lean_dec_ref(v___x_819_);
v___x_821_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_ctx_782_, v_rhs_818_);
v_a_822_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_830_ == 0)
{
v___x_824_ = v___x_821_;
v_isShared_825_ = v_isSharedCheck_830_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_821_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_830_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_826_; lean_object* v___x_828_; 
v___x_826_ = l_Lean_mkNatEq(v_a_820_, v_a_822_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v___x_826_);
v___x_828_ = v___x_824_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_826_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg___boxed(lean_object* v_ctx_831_, lean_object* v_c_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(v_ctx_831_, v_c_832_, v_a_833_, v_a_834_);
lean_dec(v_a_834_);
lean_dec_ref(v_a_833_);
lean_dec_ref(v_ctx_831_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith(lean_object* v_ctx_837_, lean_object* v_c_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(v_ctx_837_, v_c_838_, v_a_841_, v_a_842_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___boxed(lean_object* v_ctx_845_, lean_object* v_c_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith(v_ctx_845_, v_c_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_);
lean_dec(v_a_850_);
lean_dec_ref(v_a_849_);
lean_dec(v_a_848_);
lean_dec_ref(v_a_847_);
lean_dec_ref(v_ctx_845_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(lean_object* v_e_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_){
_start:
{
lean_object* v___x_860_; lean_object* v_varMap_861_; lean_object* v___x_862_; 
v___x_860_ = lean_st_ref_get(v_a_854_);
v_varMap_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc_ref(v_varMap_861_);
lean_dec(v___x_860_);
lean_inc_ref(v_e_853_);
v___x_862_ = l_Lean_Meta_KExprMap_find_x3f___redArg(v_varMap_861_, v_e_853_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
lean_dec_ref(v_varMap_861_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_911_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_911_ == 0)
{
v___x_865_ = v___x_862_;
v_isShared_866_ = v_isSharedCheck_911_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_862_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_911_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
if (lean_obj_tag(v_a_863_) == 1)
{
lean_object* v_val_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_877_; 
lean_dec_ref(v_e_853_);
v_val_867_ = lean_ctor_get(v_a_863_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v_a_863_);
if (v_isSharedCheck_877_ == 0)
{
v___x_869_ = v_a_863_;
v_isShared_870_ = v_isSharedCheck_877_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_val_867_);
lean_dec(v_a_863_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_877_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_872_; 
if (v_isShared_870_ == 0)
{
v___x_872_ = v___x_869_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_val_867_);
v___x_872_ = v_reuseFailAlloc_876_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v___x_874_; 
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_872_);
v___x_874_ = v___x_865_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_872_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
else
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v_vars_880_; lean_object* v_varMap_881_; lean_object* v_vars_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_910_; 
lean_del_object(v___x_865_);
lean_dec(v_a_863_);
v___x_878_ = lean_st_ref_get(v_a_854_);
v___x_879_ = lean_st_ref_get(v_a_854_);
v_vars_880_ = lean_ctor_get(v___x_878_, 1);
lean_inc_ref(v_vars_880_);
lean_dec(v___x_878_);
v_varMap_881_ = lean_ctor_get(v___x_879_, 0);
v_vars_882_ = lean_ctor_get(v___x_879_, 1);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_910_ == 0)
{
v___x_884_ = v___x_879_;
v_isShared_885_ = v_isSharedCheck_910_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_vars_882_);
lean_inc(v_varMap_881_);
lean_dec(v___x_879_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_910_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = lean_array_get_size(v_vars_880_);
lean_dec_ref(v_vars_880_);
lean_inc_ref(v_e_853_);
v___x_887_ = l_Lean_Meta_KExprMap_insert___redArg(v_varMap_881_, v_e_853_, v___x_886_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_901_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_901_ == 0)
{
v___x_890_ = v___x_887_;
v_isShared_891_ = v_isSharedCheck_901_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_887_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_901_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_892_; lean_object* v___x_894_; 
v___x_892_ = lean_array_push(v_vars_882_, v_e_853_);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 1, v___x_892_);
lean_ctor_set(v___x_884_, 0, v_a_888_);
v___x_894_ = v___x_884_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_888_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v___x_892_);
v___x_894_ = v_reuseFailAlloc_900_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_898_; 
v___x_895_ = lean_st_ref_set(v_a_854_, v___x_894_);
v___x_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_896_, 0, v___x_886_);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 0, v___x_896_);
v___x_898_ = v___x_890_;
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
else
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
lean_del_object(v___x_884_);
lean_dec_ref(v_vars_882_);
lean_dec_ref(v_e_853_);
v_a_902_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_887_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_887_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
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
}
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_dec_ref(v_e_853_);
v_a_912_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_862_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_862_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar___boxed(lean_object* v_e_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_);
lean_dec(v_a_925_);
lean_dec_ref(v_a_924_);
lean_dec(v_a_923_);
lean_dec_ref(v_a_922_);
lean_dec(v_a_921_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit(lean_object* v_e_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_){
_start:
{
lean_object* v___x_972_; 
lean_inc_ref(v_e_965_);
v___x_972_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_965_, v_a_968_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; lean_object* v___x_974_; uint8_t v___x_975_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
lean_inc(v_a_973_);
lean_dec_ref_known(v___x_972_, 1);
v___x_974_ = l_Lean_Expr_cleanupAnnotations(v_a_973_);
v___x_975_ = l_Lean_Expr_isApp(v___x_974_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; 
lean_dec_ref(v___x_974_);
v___x_976_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
return v___x_976_;
}
else
{
lean_object* v_arg_977_; lean_object* v___x_978_; lean_object* v___x_979_; uint8_t v___x_980_; 
v_arg_977_ = lean_ctor_get(v___x_974_, 1);
lean_inc_ref(v_arg_977_);
v___x_978_ = l_Lean_Expr_appFnCleanup___redArg(v___x_974_);
v___x_979_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__1));
v___x_980_ = l_Lean_Expr_isConstOf(v___x_978_, v___x_979_);
if (v___x_980_ == 0)
{
uint8_t v___x_981_; 
v___x_981_ = l_Lean_Expr_isApp(v___x_978_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; 
lean_dec_ref(v___x_978_);
lean_dec_ref(v_arg_977_);
v___x_982_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
return v___x_982_;
}
else
{
lean_object* v_arg_983_; lean_object* v_b_985_; lean_object* v___y_986_; lean_object* v___y_987_; lean_object* v___y_988_; lean_object* v___y_989_; lean_object* v___y_990_; lean_object* v___x_1034_; lean_object* v___x_1035_; uint8_t v___x_1036_; 
v_arg_983_ = lean_ctor_get(v___x_978_, 1);
lean_inc_ref(v_arg_983_);
v___x_1034_ = l_Lean_Expr_appFnCleanup___redArg(v___x_978_);
v___x_1035_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__3));
v___x_1036_ = l_Lean_Expr_isConstOf(v___x_1034_, v___x_1035_);
if (v___x_1036_ == 0)
{
lean_object* v___x_1037_; uint8_t v___x_1038_; 
v___x_1037_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__4));
v___x_1038_ = l_Lean_Expr_isConstOf(v___x_1034_, v___x_1037_);
if (v___x_1038_ == 0)
{
uint8_t v___x_1039_; 
v___x_1039_ = l_Lean_Expr_isApp(v___x_1034_);
if (v___x_1039_ == 0)
{
lean_object* v___x_1040_; 
lean_dec_ref(v___x_1034_);
lean_dec_ref(v_arg_983_);
lean_dec_ref(v_arg_977_);
v___x_1040_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
return v___x_1040_;
}
else
{
lean_object* v_arg_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; uint8_t v___x_1044_; 
v_arg_1041_ = lean_ctor_get(v___x_1034_, 1);
lean_inc_ref(v_arg_1041_);
v___x_1042_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1034_);
v___x_1043_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__7));
v___x_1044_ = l_Lean_Expr_isConstOf(v___x_1042_, v___x_1043_);
if (v___x_1044_ == 0)
{
uint8_t v___x_1045_; 
v___x_1045_ = l_Lean_Expr_isApp(v___x_1042_);
if (v___x_1045_ == 0)
{
lean_object* v___x_1046_; 
lean_dec_ref(v___x_1042_);
lean_dec_ref(v_arg_1041_);
lean_dec_ref(v_arg_983_);
lean_dec_ref(v_arg_977_);
v___x_1046_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
return v___x_1046_;
}
else
{
lean_object* v___x_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; 
v___x_1047_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1042_);
v___x_1048_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__9));
v___x_1049_ = l_Lean_Expr_isConstOf(v___x_1047_, v___x_1048_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1050_; uint8_t v___x_1051_; 
v___x_1050_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__11));
v___x_1051_ = l_Lean_Expr_isConstOf(v___x_1047_, v___x_1050_);
if (v___x_1051_ == 0)
{
uint8_t v___x_1052_; 
v___x_1052_ = l_Lean_Expr_isApp(v___x_1047_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; 
lean_dec_ref(v___x_1047_);
lean_dec_ref(v_arg_1041_);
lean_dec_ref(v_arg_983_);
lean_dec_ref(v_arg_977_);
v___x_1053_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
return v___x_1053_;
}
else
{
lean_object* v___x_1054_; uint8_t v___x_1055_; 
v___x_1054_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1047_);
v___x_1055_ = l_Lean_Expr_isApp(v___x_1054_);
if (v___x_1055_ == 0)
{
lean_object* v___x_1056_; 
lean_dec_ref(v___x_1054_);
lean_dec_ref(v_arg_1041_);
lean_dec_ref(v_arg_983_);
lean_dec_ref(v_arg_977_);
v___x_1056_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
return v___x_1056_;
}
else
{
lean_object* v___x_1057_; lean_object* v___x_1058_; uint8_t v___x_1059_; 
v___x_1057_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1054_);
v___x_1058_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__14));
v___x_1059_ = l_Lean_Expr_isConstOf(v___x_1057_, v___x_1058_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1060_; uint8_t v___x_1061_; 
v___x_1060_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__17));
v___x_1061_ = l_Lean_Expr_isConstOf(v___x_1057_, v___x_1060_);
lean_dec_ref(v___x_1057_);
if (v___x_1061_ == 0)
{
lean_object* v___x_1062_; 
lean_dec_ref(v_arg_1041_);
lean_dec_ref(v_arg_983_);
lean_dec_ref(v_arg_977_);
v___x_1062_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
return v___x_1062_;
}
else
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Lean_Meta_DefEq_isInstHAddNat(v_arg_1041_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1064_; uint8_t v___x_1065_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
lean_inc(v_a_1064_);
lean_dec_ref_known(v___x_1063_, 1);
v___x_1065_ = lean_unbox(v_a_1064_);
lean_dec(v_a_1064_);
if (v___x_1065_ == 0)
{
lean_object* v___x_1066_; 
lean_dec_ref(v_arg_983_);
lean_dec_ref(v_arg_977_);
v___x_1066_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
return v___x_1066_;
}
else
{
lean_object* v___x_1067_; 
lean_dec_ref(v_e_965_);
v___x_1067_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_983_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v_a_1068_; lean_object* v___x_1069_; 
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_a_1068_);
lean_dec_ref_known(v___x_1067_, 1);
v___x_1069_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_977_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1078_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1072_ = v___x_1069_;
v_isShared_1073_ = v_isSharedCheck_1078_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1069_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1078_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1074_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1074_, 0, v_a_1068_);
lean_ctor_set(v___x_1074_, 1, v_a_1070_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 0, v___x_1074_);
v___x_1076_ = v___x_1072_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1074_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
else
{
lean_dec(v_a_1068_);
return v___x_1069_;
}
}
else
{
lean_dec_ref(v_arg_977_);
return v___x_1067_;
}
}
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
lean_dec_ref(v_arg_983_);
lean_dec_ref(v_arg_977_);
lean_dec_ref(v_e_965_);
v_a_1079_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_1063_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1063_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1079_);
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
}
else
{
lean_object* v___x_1087_; 
lean_dec_ref(v___x_1057_);
v___x_1087_ = l_Lean_Meta_DefEq_isInstHMulNat(v_arg_1041_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v_a_1088_; uint8_t v___x_1089_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_a_1088_);
lean_dec_ref_known(v___x_1087_, 1);
v___x_1089_ = lean_unbox(v_a_1088_);
lean_dec(v_a_1088_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; 
lean_dec_ref(v_arg_983_);
lean_dec_ref(v_arg_977_);
v___x_1090_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
return v___x_1090_;
}
else
{
v_b_985_ = v_arg_977_;
v___y_986_ = v_a_966_;
v___y_987_ = v_a_967_;
v___y_988_ = v_a_968_;
v___y_989_ = v_a_969_;
v___y_990_ = v_a_970_;
goto v___jp_984_;
}
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
lean_dec_ref(v_arg_983_);
lean_dec_ref(v_arg_977_);
lean_dec_ref(v_e_965_);
v_a_1091_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_1087_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1087_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
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
}
}
}
else
{
lean_object* v___x_1099_; 
lean_dec_ref(v___x_1047_);
v___x_1099_ = l_Lean_Meta_DefEq_isInstAddNat(v_arg_1041_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v_a_1100_; uint8_t v___x_1101_; 
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_a_1100_);
lean_dec_ref_known(v___x_1099_, 1);
v___x_1101_ = lean_unbox(v_a_1100_);
lean_dec(v_a_1100_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1102_; 
lean_dec_ref(v_arg_983_);
lean_dec_ref(v_arg_977_);
v___x_1102_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
return v___x_1102_;
}
else
{
lean_object* v___x_1103_; 
lean_dec_ref(v_e_965_);
v___x_1103_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_983_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v_a_1104_; lean_object* v___x_1105_; 
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
lean_inc(v_a_1104_);
lean_dec_ref_known(v___x_1103_, 1);
v___x_1105_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_977_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1114_; 
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1108_ = v___x_1105_;
v_isShared_1109_ = v_isSharedCheck_1114_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1105_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1114_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1110_; lean_object* v___x_1112_; 
v___x_1110_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1110_, 0, v_a_1104_);
lean_ctor_set(v___x_1110_, 1, v_a_1106_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 0, v___x_1110_);
v___x_1112_ = v___x_1108_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1110_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
else
{
lean_dec(v_a_1104_);
return v___x_1105_;
}
}
else
{
lean_dec_ref(v_arg_977_);
return v___x_1103_;
}
}
}
else
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
lean_dec_ref(v_arg_983_);
lean_dec_ref(v_arg_977_);
lean_dec_ref(v_e_965_);
v_a_1115_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1117_ = v___x_1099_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1099_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1115_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
}
else
{
lean_object* v___x_1123_; 
lean_dec_ref(v___x_1047_);
v___x_1123_ = l_Lean_Meta_DefEq_isInstMulNat(v_arg_1041_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v_a_1124_; uint8_t v___x_1125_; 
v_a_1124_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_a_1124_);
lean_dec_ref_known(v___x_1123_, 1);
v___x_1125_ = lean_unbox(v_a_1124_);
lean_dec(v_a_1124_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; 
lean_dec_ref(v_arg_983_);
lean_dec_ref(v_arg_977_);
v___x_1126_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
return v___x_1126_;
}
else
{
v_b_985_ = v_arg_977_;
v___y_986_ = v_a_966_;
v___y_987_ = v_a_967_;
v___y_988_ = v_a_968_;
v___y_989_ = v_a_969_;
v___y_990_ = v_a_970_;
goto v___jp_984_;
}
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
lean_dec_ref(v_arg_983_);
lean_dec_ref(v_arg_977_);
lean_dec_ref(v_e_965_);
v_a_1127_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1123_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1123_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1127_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
}
}
else
{
lean_object* v___x_1135_; 
lean_dec_ref(v___x_1042_);
lean_dec_ref(v_arg_1041_);
lean_inc_ref(v_arg_977_);
v___x_1135_ = l_Lean_Meta_Structural_isInstOfNatNat___redArg(v_arg_977_, v_a_968_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; uint8_t v___x_1137_; 
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_a_1136_);
lean_dec_ref_known(v___x_1135_, 1);
v___x_1137_ = lean_unbox(v_a_1136_);
lean_dec(v_a_1136_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
lean_inc_ref(v_arg_983_);
v___x_1138_ = l_Lean_mkInstOfNatNat(v_arg_983_);
v___x_1139_ = l_Lean_Meta_isDefEqI(v_arg_977_, v___x_1138_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; uint8_t v___x_1141_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_a_1140_);
lean_dec_ref_known(v___x_1139_, 1);
v___x_1141_ = lean_unbox(v_a_1140_);
lean_dec(v_a_1140_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; 
lean_dec_ref(v_arg_983_);
v___x_1142_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
return v___x_1142_;
}
else
{
lean_object* v___x_1143_; 
lean_dec_ref(v_e_965_);
v___x_1143_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_983_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
return v___x_1143_;
}
}
else
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1151_; 
lean_dec_ref(v_arg_983_);
lean_dec_ref(v_e_965_);
v_a_1144_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1146_ = v___x_1139_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1139_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1149_; 
if (v_isShared_1147_ == 0)
{
v___x_1149_ = v___x_1146_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1144_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
else
{
lean_object* v___x_1152_; 
lean_dec_ref(v_arg_977_);
lean_dec_ref(v_e_965_);
v___x_1152_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_983_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
return v___x_1152_;
}
}
else
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
lean_dec_ref(v_arg_983_);
lean_dec_ref(v_arg_977_);
lean_dec_ref(v_e_965_);
v_a_1153_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1135_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1135_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1153_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
}
}
else
{
lean_object* v___x_1161_; 
lean_dec_ref(v___x_1034_);
lean_dec_ref(v_e_965_);
v___x_1161_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_983_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_a_1162_; lean_object* v___x_1163_; 
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_a_1162_);
lean_dec_ref_known(v___x_1161_, 1);
v___x_1163_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_977_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1172_; 
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1166_ = v___x_1163_;
v_isShared_1167_ = v_isSharedCheck_1172_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1163_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1172_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1168_; lean_object* v___x_1170_; 
v___x_1168_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1168_, 0, v_a_1162_);
lean_ctor_set(v___x_1168_, 1, v_a_1164_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 0, v___x_1168_);
v___x_1170_ = v___x_1166_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1168_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
else
{
lean_dec(v_a_1162_);
return v___x_1163_;
}
}
else
{
lean_dec_ref(v_arg_977_);
return v___x_1161_;
}
}
}
else
{
lean_dec_ref(v___x_1034_);
v_b_985_ = v_arg_977_;
v___y_986_ = v_a_966_;
v___y_987_ = v_a_967_;
v___y_988_ = v_a_968_;
v___y_989_ = v_a_969_;
v___y_990_ = v_a_970_;
goto v___jp_984_;
}
v___jp_984_:
{
lean_object* v___x_991_; 
lean_inc_ref(v_arg_983_);
v___x_991_ = l_Lean_Meta_evalNat(v_arg_983_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_a_992_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_a_992_);
lean_dec_ref_known(v___x_991_, 1);
if (lean_obj_tag(v_a_992_) == 0)
{
lean_object* v___x_993_; 
v___x_993_ = l_Lean_Meta_evalNat(v_b_985_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; 
v_a_994_ = lean_ctor_get(v___x_993_, 0);
lean_inc(v_a_994_);
lean_dec_ref_known(v___x_993_, 1);
if (lean_obj_tag(v_a_994_) == 0)
{
lean_object* v___x_995_; 
lean_dec_ref(v_arg_983_);
v___x_995_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_965_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
return v___x_995_;
}
else
{
lean_object* v_val_996_; lean_object* v___x_997_; 
lean_dec_ref(v_e_965_);
v_val_996_ = lean_ctor_get(v_a_994_, 0);
lean_inc(v_val_996_);
lean_dec_ref_known(v_a_994_, 1);
v___x_997_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_983_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1006_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_1000_ = v___x_997_;
v_isShared_1001_ = v_isSharedCheck_1006_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_997_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1006_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1002_; lean_object* v___x_1004_; 
v___x_1002_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1002_, 0, v_a_998_);
lean_ctor_set(v___x_1002_, 1, v_val_996_);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 0, v___x_1002_);
v___x_1004_ = v___x_1000_;
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
}
else
{
lean_dec(v_val_996_);
return v___x_997_;
}
}
}
else
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
lean_dec_ref(v_arg_983_);
lean_dec_ref(v_e_965_);
v_a_1007_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_993_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_993_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1007_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
else
{
lean_object* v_val_1015_; lean_object* v___x_1016_; 
lean_dec_ref(v_arg_983_);
lean_dec_ref(v_e_965_);
v_val_1015_ = lean_ctor_get(v_a_992_, 0);
lean_inc(v_val_1015_);
lean_dec_ref_known(v_a_992_, 1);
v___x_1016_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_b_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1025_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1019_ = v___x_1016_;
v_isShared_1020_ = v_isSharedCheck_1025_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_1016_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1025_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1021_; lean_object* v___x_1023_; 
v___x_1021_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1021_, 0, v_val_1015_);
lean_ctor_set(v___x_1021_, 1, v_a_1017_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 0, v___x_1021_);
v___x_1023_ = v___x_1019_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1021_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
else
{
lean_dec(v_val_1015_);
return v___x_1016_;
}
}
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
lean_dec_ref(v_b_985_);
lean_dec_ref(v_arg_983_);
lean_dec_ref(v_e_965_);
v_a_1026_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_991_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_991_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
}
}
else
{
lean_object* v___x_1173_; 
lean_dec_ref(v___x_978_);
lean_dec_ref(v_e_965_);
v___x_1173_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_977_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1182_; 
v_a_1174_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1176_ = v___x_1173_;
v_isShared_1177_ = v_isSharedCheck_1182_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_dec(v___x_1173_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1182_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1178_; lean_object* v___x_1180_; 
v___x_1178_ = l_Nat_Internal_Linear_Expr_inc(v_a_1174_);
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 0, v___x_1178_);
v___x_1180_ = v___x_1176_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1178_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
else
{
return v___x_1173_;
}
}
}
}
else
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1190_; 
lean_dec_ref(v_e_965_);
v_a_1183_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1185_ = v___x_972_;
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_972_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1183_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(lean_object* v_e_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_){
_start:
{
switch(lean_obj_tag(v_e_1191_))
{
case 9:
{
lean_object* v_a_1198_; 
v_a_1198_ = lean_ctor_get(v_e_1191_, 0);
lean_inc_ref(v_a_1198_);
if (lean_obj_tag(v_a_1198_) == 0)
{
lean_object* v_val_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1207_; 
lean_dec_ref_known(v_e_1191_, 1);
v_val_1199_ = lean_ctor_get(v_a_1198_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v_a_1198_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1201_ = v_a_1198_;
v_isShared_1202_ = v_isSharedCheck_1207_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_val_1199_);
lean_dec(v_a_1198_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1207_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1202_ == 0)
{
v___x_1204_ = v___x_1201_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_val_1199_);
v___x_1204_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
lean_object* v___x_1205_; 
v___x_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1204_);
return v___x_1205_;
}
}
}
else
{
lean_object* v___x_1208_; 
lean_dec_ref(v_a_1198_);
v___x_1208_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_);
return v___x_1208_;
}
}
case 10:
{
lean_object* v_expr_1209_; 
v_expr_1209_ = lean_ctor_get(v_e_1191_, 1);
lean_inc_ref(v_expr_1209_);
lean_dec_ref_known(v_e_1191_, 2);
v_e_1191_ = v_expr_1209_;
goto _start;
}
case 4:
{
lean_object* v_declName_1211_; 
v_declName_1211_ = lean_ctor_get(v_e_1191_, 0);
if (lean_obj_tag(v_declName_1211_) == 1)
{
lean_object* v_pre_1212_; 
v_pre_1212_ = lean_ctor_get(v_declName_1211_, 0);
if (lean_obj_tag(v_pre_1212_) == 1)
{
lean_object* v_pre_1213_; 
v_pre_1213_ = lean_ctor_get(v_pre_1212_, 0);
if (lean_obj_tag(v_pre_1213_) == 0)
{
lean_object* v_str_1214_; lean_object* v_str_1215_; lean_object* v___x_1216_; uint8_t v___x_1217_; 
v_str_1214_ = lean_ctor_get(v_declName_1211_, 1);
v_str_1215_ = lean_ctor_get(v_pre_1212_, 1);
v___x_1216_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0));
v___x_1217_ = lean_string_dec_eq(v_str_1215_, v___x_1216_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1218_; 
v___x_1218_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_);
return v___x_1218_;
}
else
{
lean_object* v___x_1219_; uint8_t v___x_1220_; 
v___x_1219_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__0));
v___x_1220_ = lean_string_dec_eq(v_str_1214_, v___x_1219_);
if (v___x_1220_ == 0)
{
lean_object* v___x_1221_; 
v___x_1221_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_);
return v___x_1221_;
}
else
{
lean_object* v___x_1222_; lean_object* v___x_1223_; 
lean_dec_ref_known(v_e_1191_, 2);
v___x_1222_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__1));
v___x_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1222_);
return v___x_1223_;
}
}
}
else
{
lean_object* v___x_1224_; 
v___x_1224_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_);
return v___x_1224_;
}
}
else
{
lean_object* v___x_1225_; 
v___x_1225_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_);
return v___x_1225_;
}
}
else
{
lean_object* v___x_1226_; 
v___x_1226_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_);
return v___x_1226_;
}
}
case 5:
{
lean_object* v___x_1227_; 
v___x_1227_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit(v_e_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_);
return v___x_1227_;
}
case 2:
{
lean_object* v___x_1228_; 
v___x_1228_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit(v_e_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_);
return v___x_1228_;
}
default: 
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_);
return v___x_1229_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___boxed(lean_object* v_e_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_e_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_);
lean_dec(v_a_1235_);
lean_dec_ref(v_a_1234_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec(v_a_1231_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___boxed(lean_object* v_e_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit(v_e_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_);
lean_dec(v_a_1243_);
lean_dec_ref(v_a_1242_);
lean_dec(v_a_1241_);
lean_dec_ref(v_a_1240_);
lean_dec(v_a_1239_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f(lean_object* v_e_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1277_, v_a_1280_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1624_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1287_ = v___x_1284_;
v_isShared_1288_ = v_isSharedCheck_1624_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1284_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1624_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1294_; uint8_t v___x_1295_; 
v___x_1294_ = l_Lean_Expr_cleanupAnnotations(v_a_1285_);
v___x_1295_ = l_Lean_Expr_isApp(v___x_1294_);
if (v___x_1295_ == 0)
{
lean_dec_ref(v___x_1294_);
goto v___jp_1289_;
}
else
{
lean_object* v_arg_1296_; lean_object* v___x_1297_; uint8_t v___x_1298_; 
v_arg_1296_ = lean_ctor_get(v___x_1294_, 1);
lean_inc_ref(v_arg_1296_);
v___x_1297_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1294_);
v___x_1298_ = l_Lean_Expr_isApp(v___x_1297_);
if (v___x_1298_ == 0)
{
lean_dec_ref(v___x_1297_);
lean_dec_ref(v_arg_1296_);
goto v___jp_1289_;
}
else
{
lean_object* v_arg_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; uint8_t v___x_1302_; 
v_arg_1299_ = lean_ctor_get(v___x_1297_, 1);
lean_inc_ref(v_arg_1299_);
v___x_1300_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1297_);
v___x_1301_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__1));
v___x_1302_ = l_Lean_Expr_isConstOf(v___x_1300_, v___x_1301_);
if (v___x_1302_ == 0)
{
lean_object* v___x_1303_; uint8_t v___x_1304_; 
v___x_1303_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__3));
v___x_1304_ = l_Lean_Expr_isConstOf(v___x_1300_, v___x_1303_);
if (v___x_1304_ == 0)
{
uint8_t v___x_1305_; 
v___x_1305_ = l_Lean_Expr_isApp(v___x_1300_);
if (v___x_1305_ == 0)
{
lean_dec_ref(v___x_1300_);
lean_dec_ref(v_arg_1299_);
lean_dec_ref(v_arg_1296_);
goto v___jp_1289_;
}
else
{
lean_object* v_arg_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; 
v_arg_1306_ = lean_ctor_get(v___x_1300_, 1);
lean_inc_ref(v_arg_1306_);
v___x_1307_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1300_);
v___x_1308_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__5));
v___x_1309_ = l_Lean_Expr_isConstOf(v___x_1307_, v___x_1308_);
if (v___x_1309_ == 0)
{
uint8_t v___x_1310_; 
v___x_1310_ = l_Lean_Expr_isApp(v___x_1307_);
if (v___x_1310_ == 0)
{
lean_dec_ref(v___x_1307_);
lean_dec_ref(v_arg_1306_);
lean_dec_ref(v_arg_1299_);
lean_dec_ref(v_arg_1296_);
goto v___jp_1289_;
}
else
{
lean_object* v___x_1311_; lean_object* v___x_1312_; uint8_t v___x_1313_; 
v___x_1311_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1307_);
v___x_1312_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__8));
v___x_1313_ = l_Lean_Expr_isConstOf(v___x_1311_, v___x_1312_);
if (v___x_1313_ == 0)
{
lean_object* v___x_1314_; uint8_t v___x_1315_; 
v___x_1314_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__11));
v___x_1315_ = l_Lean_Expr_isConstOf(v___x_1311_, v___x_1314_);
if (v___x_1315_ == 0)
{
lean_object* v___x_1316_; uint8_t v___x_1317_; 
v___x_1316_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__13));
v___x_1317_ = l_Lean_Expr_isConstOf(v___x_1311_, v___x_1316_);
if (v___x_1317_ == 0)
{
lean_object* v___x_1318_; uint8_t v___x_1319_; 
v___x_1318_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__15));
v___x_1319_ = l_Lean_Expr_isConstOf(v___x_1311_, v___x_1318_);
lean_dec_ref(v___x_1311_);
if (v___x_1319_ == 0)
{
lean_dec_ref(v_arg_1306_);
lean_dec_ref(v_arg_1299_);
lean_dec_ref(v_arg_1296_);
goto v___jp_1289_;
}
else
{
lean_object* v___x_1320_; 
lean_del_object(v___x_1287_);
v___x_1320_ = l_Lean_Meta_DefEq_isInstLENat(v_arg_1306_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1359_; 
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1323_ = v___x_1320_;
v_isShared_1324_ = v_isSharedCheck_1359_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1320_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1359_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
uint8_t v___x_1325_; 
v___x_1325_ = lean_unbox(v_a_1321_);
lean_dec(v_a_1321_);
if (v___x_1325_ == 0)
{
lean_object* v___x_1326_; lean_object* v___x_1328_; 
lean_dec_ref(v_arg_1299_);
lean_dec_ref(v_arg_1296_);
v___x_1326_ = lean_box(0);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v___x_1326_);
v___x_1328_ = v___x_1323_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v___x_1326_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
else
{
lean_object* v___x_1330_; 
lean_del_object(v___x_1323_);
v___x_1330_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1299_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_a_1331_; lean_object* v___x_1332_; 
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_a_1331_);
lean_dec_ref_known(v___x_1330_, 1);
v___x_1332_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1296_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1342_; 
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1335_ = v___x_1332_;
v_isShared_1336_ = v_isSharedCheck_1342_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1332_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1342_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1340_; 
v___x_1337_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1337_, 0, v_a_1331_);
lean_ctor_set(v___x_1337_, 1, v_a_1333_);
lean_ctor_set_uint8(v___x_1337_, sizeof(void*)*2, v___x_1317_);
v___x_1338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1337_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v___x_1338_);
v___x_1340_ = v___x_1335_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1338_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
lean_dec(v_a_1331_);
v_a_1343_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1345_ = v___x_1332_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1332_);
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
else
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
lean_dec_ref(v_arg_1296_);
v_a_1351_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1353_ = v___x_1330_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1330_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1351_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
}
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
lean_dec_ref(v_arg_1299_);
lean_dec_ref(v_arg_1296_);
v_a_1360_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1320_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1320_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
}
else
{
lean_object* v___x_1368_; 
lean_dec_ref(v___x_1311_);
lean_del_object(v___x_1287_);
v___x_1368_ = l_Lean_Meta_DefEq_isInstLTNat(v_arg_1306_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1408_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1371_ = v___x_1368_;
v_isShared_1372_ = v_isSharedCheck_1408_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1368_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1408_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
uint8_t v___x_1373_; 
v___x_1373_ = lean_unbox(v_a_1369_);
lean_dec(v_a_1369_);
if (v___x_1373_ == 0)
{
lean_object* v___x_1374_; lean_object* v___x_1376_; 
lean_dec_ref(v_arg_1299_);
lean_dec_ref(v_arg_1296_);
v___x_1374_ = lean_box(0);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v___x_1374_);
v___x_1376_ = v___x_1371_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1374_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
else
{
lean_object* v___x_1378_; 
lean_del_object(v___x_1371_);
v___x_1378_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1299_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_a_1379_; lean_object* v___x_1380_; 
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_a_1379_);
lean_dec_ref_known(v___x_1378_, 1);
v___x_1380_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1296_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1391_; 
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1383_ = v___x_1380_;
v_isShared_1384_ = v_isSharedCheck_1391_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1380_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1391_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1389_; 
v___x_1385_ = l_Nat_Internal_Linear_Expr_inc(v_a_1379_);
v___x_1386_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1386_, 0, v___x_1385_);
lean_ctor_set(v___x_1386_, 1, v_a_1381_);
lean_ctor_set_uint8(v___x_1386_, sizeof(void*)*2, v___x_1315_);
v___x_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 0, v___x_1387_);
v___x_1389_ = v___x_1383_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1387_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
else
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1399_; 
lean_dec(v_a_1379_);
v_a_1392_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1394_ = v___x_1380_;
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___x_1380_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1397_; 
if (v_isShared_1395_ == 0)
{
v___x_1397_ = v___x_1394_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_a_1392_);
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
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
lean_dec_ref(v_arg_1296_);
v_a_1400_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v___x_1378_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1378_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_a_1400_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
}
}
else
{
lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1416_; 
lean_dec_ref(v_arg_1299_);
lean_dec_ref(v_arg_1296_);
v_a_1409_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1411_ = v___x_1368_;
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1368_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1414_; 
if (v_isShared_1412_ == 0)
{
v___x_1414_ = v___x_1411_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_a_1409_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
}
else
{
lean_object* v___x_1417_; 
lean_dec_ref(v___x_1311_);
lean_del_object(v___x_1287_);
v___x_1417_ = l_Lean_Meta_DefEq_isInstLENat(v_arg_1306_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1456_; 
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1420_ = v___x_1417_;
v_isShared_1421_ = v_isSharedCheck_1456_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1417_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1456_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
uint8_t v___x_1422_; 
v___x_1422_ = lean_unbox(v_a_1418_);
lean_dec(v_a_1418_);
if (v___x_1422_ == 0)
{
lean_object* v___x_1423_; lean_object* v___x_1425_; 
lean_dec_ref(v_arg_1299_);
lean_dec_ref(v_arg_1296_);
v___x_1423_ = lean_box(0);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 0, v___x_1423_);
v___x_1425_ = v___x_1420_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1423_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
return v___x_1425_;
}
}
else
{
lean_object* v___x_1427_; 
lean_del_object(v___x_1420_);
v___x_1427_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1296_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; lean_object* v___x_1429_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
lean_inc(v_a_1428_);
lean_dec_ref_known(v___x_1427_, 1);
v___x_1429_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1299_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1439_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1432_ = v___x_1429_;
v_isShared_1433_ = v_isSharedCheck_1439_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1429_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1439_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1437_; 
v___x_1434_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1434_, 0, v_a_1428_);
lean_ctor_set(v___x_1434_, 1, v_a_1430_);
lean_ctor_set_uint8(v___x_1434_, sizeof(void*)*2, v___x_1313_);
v___x_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1434_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 0, v___x_1435_);
v___x_1437_ = v___x_1432_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1435_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
lean_dec(v_a_1428_);
v_a_1440_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1429_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1429_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1440_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
}
else
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1455_; 
lean_dec_ref(v_arg_1299_);
v_a_1448_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1450_ = v___x_1427_;
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1427_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1453_; 
if (v_isShared_1451_ == 0)
{
v___x_1453_ = v___x_1450_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_a_1448_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
}
}
}
else
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
lean_dec_ref(v_arg_1299_);
lean_dec_ref(v_arg_1296_);
v_a_1457_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1459_ = v___x_1417_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1417_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1457_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
}
else
{
lean_object* v___x_1465_; 
lean_dec_ref(v___x_1311_);
lean_del_object(v___x_1287_);
v___x_1465_ = l_Lean_Meta_DefEq_isInstLTNat(v_arg_1306_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1505_; 
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1468_ = v___x_1465_;
v_isShared_1469_ = v_isSharedCheck_1505_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1465_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1505_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
uint8_t v___x_1470_; 
v___x_1470_ = lean_unbox(v_a_1466_);
lean_dec(v_a_1466_);
if (v___x_1470_ == 0)
{
lean_object* v___x_1471_; lean_object* v___x_1473_; 
lean_dec_ref(v_arg_1299_);
lean_dec_ref(v_arg_1296_);
v___x_1471_ = lean_box(0);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v___x_1471_);
v___x_1473_ = v___x_1468_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v___x_1471_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
else
{
lean_object* v___x_1475_; 
lean_del_object(v___x_1468_);
v___x_1475_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1296_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v___x_1477_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1476_);
lean_dec_ref_known(v___x_1475_, 1);
v___x_1477_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1299_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1488_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1480_ = v___x_1477_;
v_isShared_1481_ = v_isSharedCheck_1488_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1477_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1488_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1486_; 
v___x_1482_ = l_Nat_Internal_Linear_Expr_inc(v_a_1476_);
v___x_1483_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1483_, 0, v___x_1482_);
lean_ctor_set(v___x_1483_, 1, v_a_1478_);
lean_ctor_set_uint8(v___x_1483_, sizeof(void*)*2, v___x_1309_);
v___x_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1483_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 0, v___x_1484_);
v___x_1486_ = v___x_1480_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1484_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
else
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
lean_dec(v_a_1476_);
v_a_1489_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1491_ = v___x_1477_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1477_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1489_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
else
{
lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1504_; 
lean_dec_ref(v_arg_1299_);
v_a_1497_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1499_ = v___x_1475_;
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1475_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1502_; 
if (v_isShared_1500_ == 0)
{
v___x_1502_ = v___x_1499_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_a_1497_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
}
}
}
else
{
lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1513_; 
lean_dec_ref(v_arg_1299_);
lean_dec_ref(v_arg_1296_);
v_a_1506_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1508_ = v___x_1465_;
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1465_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1511_; 
if (v_isShared_1509_ == 0)
{
v___x_1511_ = v___x_1508_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_a_1506_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
}
}
else
{
lean_object* v___x_1514_; 
lean_dec_ref(v___x_1307_);
lean_del_object(v___x_1287_);
v___x_1514_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1306_, v_a_1280_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1555_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1517_ = v___x_1514_;
v_isShared_1518_ = v_isSharedCheck_1555_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1514_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1555_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; uint8_t v___x_1521_; 
v___x_1519_ = l_Lean_Expr_cleanupAnnotations(v_a_1515_);
v___x_1520_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__16));
v___x_1521_ = l_Lean_Expr_isConstOf(v___x_1519_, v___x_1520_);
lean_dec_ref(v___x_1519_);
if (v___x_1521_ == 0)
{
lean_object* v___x_1522_; lean_object* v___x_1524_; 
lean_dec_ref(v_arg_1299_);
lean_dec_ref(v_arg_1296_);
v___x_1522_ = lean_box(0);
if (v_isShared_1518_ == 0)
{
lean_ctor_set(v___x_1517_, 0, v___x_1522_);
v___x_1524_ = v___x_1517_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1522_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
else
{
lean_object* v___x_1526_; 
lean_del_object(v___x_1517_);
v___x_1526_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1299_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; lean_object* v___x_1528_; 
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_a_1527_);
lean_dec_ref_known(v___x_1526_, 1);
v___x_1528_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1296_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1538_; 
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1531_ = v___x_1528_;
v_isShared_1532_ = v_isSharedCheck_1538_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v___x_1528_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1538_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1536_; 
v___x_1533_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1533_, 0, v_a_1527_);
lean_ctor_set(v___x_1533_, 1, v_a_1529_);
lean_ctor_set_uint8(v___x_1533_, sizeof(void*)*2, v___x_1521_);
v___x_1534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1533_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 0, v___x_1534_);
v___x_1536_ = v___x_1531_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1534_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
else
{
lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1546_; 
lean_dec(v_a_1527_);
v_a_1539_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1541_ = v___x_1528_;
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1528_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1546_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1544_; 
if (v_isShared_1542_ == 0)
{
v___x_1544_ = v___x_1541_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_a_1539_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
}
else
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1554_; 
lean_dec_ref(v_arg_1296_);
v_a_1547_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1549_ = v___x_1526_;
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1526_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1552_; 
if (v_isShared_1550_ == 0)
{
v___x_1552_ = v___x_1549_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_a_1547_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
}
}
else
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
lean_dec_ref(v_arg_1299_);
lean_dec_ref(v_arg_1296_);
v_a_1556_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1514_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1514_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
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
}
}
else
{
lean_object* v___x_1564_; 
lean_dec_ref(v___x_1300_);
lean_del_object(v___x_1287_);
v___x_1564_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1299_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_a_1565_; lean_object* v___x_1566_; 
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_a_1565_);
lean_dec_ref_known(v___x_1564_, 1);
v___x_1566_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1296_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1576_; 
v_a_1567_ = lean_ctor_get(v___x_1566_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1569_ = v___x_1566_;
v_isShared_1570_ = v_isSharedCheck_1576_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v___x_1566_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1576_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1574_; 
v___x_1571_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1571_, 0, v_a_1565_);
lean_ctor_set(v___x_1571_, 1, v_a_1567_);
lean_ctor_set_uint8(v___x_1571_, sizeof(void*)*2, v___x_1302_);
v___x_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 0, v___x_1572_);
v___x_1574_ = v___x_1569_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v___x_1572_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
else
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
lean_dec(v_a_1565_);
v_a_1577_ = lean_ctor_get(v___x_1566_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___x_1566_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1566_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1577_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
else
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
lean_dec_ref(v_arg_1296_);
v_a_1585_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v___x_1564_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1564_);
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
else
{
lean_object* v___x_1593_; 
lean_dec_ref(v___x_1300_);
lean_del_object(v___x_1287_);
v___x_1593_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1299_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_a_1594_; lean_object* v___x_1595_; 
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_a_1594_);
lean_dec_ref_known(v___x_1593_, 1);
v___x_1595_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1296_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1607_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1598_ = v___x_1595_;
v_isShared_1599_ = v_isSharedCheck_1607_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1595_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1607_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
uint8_t v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1605_; 
v___x_1600_ = 0;
v___x_1601_ = l_Nat_Internal_Linear_Expr_inc(v_a_1594_);
v___x_1602_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1602_, 0, v___x_1601_);
lean_ctor_set(v___x_1602_, 1, v_a_1596_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*2, v___x_1600_);
v___x_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1602_);
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 0, v___x_1603_);
v___x_1605_ = v___x_1598_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v___x_1603_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
else
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1615_; 
lean_dec(v_a_1594_);
v_a_1608_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1610_ = v___x_1595_;
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1595_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1613_; 
if (v_isShared_1611_ == 0)
{
v___x_1613_ = v___x_1610_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_a_1608_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
else
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1623_; 
lean_dec_ref(v_arg_1296_);
v_a_1616_ = lean_ctor_get(v___x_1593_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1618_ = v___x_1593_;
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1593_);
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
}
v___jp_1289_:
{
lean_object* v___x_1290_; lean_object* v___x_1292_; 
v___x_1290_ = lean_box(0);
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 0, v___x_1290_);
v___x_1292_ = v___x_1287_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v___x_1290_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
else
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1632_; 
v_a_1625_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1627_ = v___x_1284_;
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1284_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1630_; 
if (v_isShared_1628_ == 0)
{
v___x_1630_ = v___x_1627_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_a_1625_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___boxed(lean_object* v_e_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f(v_e_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_);
lean_dec(v_a_1638_);
lean_dec_ref(v_a_1637_);
lean_dec(v_a_1636_);
lean_dec_ref(v_a_1635_);
lean_dec(v_a_1634_);
return v_res_1640_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1641_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1642_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__0, &l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__0_once, _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__0);
v___x_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
return v___x_1643_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__3(void){
_start:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1646_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__2));
v___x_1647_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__1, &l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__1_once, _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__1);
v___x_1648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1647_);
lean_ctor_set(v___x_1648_, 1, v___x_1646_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(lean_object* v_x_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_){
_start:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1655_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__3, &l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__3);
v___x_1656_ = lean_st_mk_ref(v___x_1655_);
lean_inc(v_a_1653_);
lean_inc_ref(v_a_1652_);
lean_inc(v_a_1651_);
lean_inc_ref(v_a_1650_);
lean_inc(v___x_1656_);
v___x_1657_ = lean_apply_6(v_x_1649_, v___x_1656_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, lean_box(0));
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1675_; 
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1660_ = v___x_1657_;
v_isShared_1661_ = v_isSharedCheck_1675_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1657_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1675_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1662_; lean_object* v_vars_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1673_; 
v___x_1662_ = lean_st_ref_get(v___x_1656_);
lean_dec(v___x_1656_);
v_vars_1663_ = lean_ctor_get(v___x_1662_, 1);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1673_ == 0)
{
lean_object* v_unused_1674_; 
v_unused_1674_ = lean_ctor_get(v___x_1662_, 0);
lean_dec(v_unused_1674_);
v___x_1665_ = v___x_1662_;
v_isShared_1666_ = v_isSharedCheck_1673_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_vars_1663_);
lean_dec(v___x_1662_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1673_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1668_; 
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 0, v_a_1658_);
v___x_1668_ = v___x_1665_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_a_1658_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v_vars_1663_);
v___x_1668_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
lean_object* v___x_1670_; 
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 0, v___x_1668_);
v___x_1670_ = v___x_1660_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1668_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
}
else
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1683_; 
lean_dec(v___x_1656_);
v_a_1676_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1678_ = v___x_1657_;
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1657_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1681_; 
if (v_isShared_1679_ == 0)
{
v___x_1681_ = v___x_1678_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1676_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___boxed(lean_object* v_x_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(v_x_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_);
lean_dec(v_a_1688_);
lean_dec_ref(v_a_1687_);
lean_dec(v_a_1686_);
lean_dec_ref(v_a_1685_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run(lean_object* v_00_u03b1_1691_, lean_object* v_x_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_){
_start:
{
lean_object* v___x_1698_; 
v___x_1698_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(v_x_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___boxed(lean_object* v_00_u03b1_1699_, lean_object* v_x_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run(v_00_u03b1_1699_, v_x_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
lean_dec(v_a_1704_);
lean_dec_ref(v_a_1703_);
lean_dec(v_a_1702_);
lean_dec_ref(v_a_1701_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearExpr(lean_object* v_e_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_){
_start:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1713_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___boxed), 7, 1);
lean_closure_set(v___x_1713_, 0, v_e_1707_);
v___x_1714_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(v___x_1713_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v_a_1715_; lean_object* v_fst_1716_; lean_object* v_snd_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; uint8_t v___x_1720_; 
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
lean_inc(v_a_1715_);
v_fst_1716_ = lean_ctor_get(v_a_1715_, 0);
lean_inc(v_fst_1716_);
v_snd_1717_ = lean_ctor_get(v_a_1715_, 1);
lean_inc(v_snd_1717_);
lean_dec(v_a_1715_);
v___x_1718_ = lean_array_get_size(v_snd_1717_);
v___x_1719_ = lean_unsigned_to_nat(1u);
v___x_1720_ = lean_nat_dec_eq(v___x_1718_, v___x_1719_);
if (v___x_1720_ == 0)
{
lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1739_; 
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1739_ == 0)
{
lean_object* v_unused_1740_; 
v_unused_1740_ = lean_ctor_get(v___x_1714_, 0);
lean_dec(v_unused_1740_);
v___x_1722_ = v___x_1714_;
v_isShared_1723_ = v_isSharedCheck_1739_;
goto v_resetjp_1721_;
}
else
{
lean_dec(v___x_1714_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1739_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
uint8_t v___x_1724_; lean_object* v___x_1725_; lean_object* v_fst_1726_; lean_object* v_snd_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1738_; 
v___x_1724_ = 1;
v___x_1725_ = l_Lean_sortExprs(v_snd_1717_, v___x_1724_);
v_fst_1726_ = lean_ctor_get(v___x_1725_, 0);
v_snd_1727_ = lean_ctor_get(v___x_1725_, 1);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1729_ = v___x_1725_;
v_isShared_1730_ = v_isSharedCheck_1738_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_snd_1727_);
lean_inc(v_fst_1726_);
lean_dec(v___x_1725_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1738_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1731_; lean_object* v___x_1733_; 
v___x_1731_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go(v_snd_1727_, v_fst_1716_);
lean_dec(v_snd_1727_);
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 1, v_fst_1726_);
lean_ctor_set(v___x_1729_, 0, v___x_1731_);
v___x_1733_ = v___x_1729_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v___x_1731_);
lean_ctor_set(v_reuseFailAlloc_1737_, 1, v_fst_1726_);
v___x_1733_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
lean_object* v___x_1735_; 
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 0, v___x_1733_);
v___x_1735_ = v___x_1722_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1733_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
}
}
else
{
lean_dec(v_snd_1717_);
lean_dec(v_fst_1716_);
return v___x_1714_;
}
}
else
{
return v___x_1714_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearExpr___boxed(lean_object* v_e_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Lean_Meta_Simp_Arith_Nat_toLinearExpr(v_e_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_);
lean_dec(v_a_1745_);
lean_dec_ref(v_a_1744_);
lean_dec(v_a_1743_);
lean_dec_ref(v_a_1742_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearCnstr_x3f(lean_object* v_e_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1754_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___boxed), 7, 1);
lean_closure_set(v___x_1754_, 0, v_e_1748_);
v___x_1755_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(v___x_1754_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1806_; 
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1758_ = v___x_1755_;
v_isShared_1759_ = v_isSharedCheck_1806_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1755_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1806_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v_fst_1760_; 
v_fst_1760_ = lean_ctor_get(v_a_1756_, 0);
lean_inc(v_fst_1760_);
if (lean_obj_tag(v_fst_1760_) == 1)
{
lean_object* v_snd_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1800_; 
v_snd_1761_ = lean_ctor_get(v_a_1756_, 1);
v_isSharedCheck_1800_ = !lean_is_exclusive(v_a_1756_);
if (v_isSharedCheck_1800_ == 0)
{
lean_object* v_unused_1801_; 
v_unused_1801_ = lean_ctor_get(v_a_1756_, 0);
lean_dec(v_unused_1801_);
v___x_1763_ = v_a_1756_;
v_isShared_1764_ = v_isSharedCheck_1800_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_snd_1761_);
lean_dec(v_a_1756_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1800_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v_val_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1799_; 
v_val_1765_ = lean_ctor_get(v_fst_1760_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v_fst_1760_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1767_ = v_fst_1760_;
v_isShared_1768_ = v_isSharedCheck_1799_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_val_1765_);
lean_dec(v_fst_1760_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1799_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; uint8_t v___x_1771_; 
v___x_1769_ = lean_array_get_size(v_snd_1761_);
v___x_1770_ = lean_unsigned_to_nat(1u);
v___x_1771_ = lean_nat_dec_le(v___x_1769_, v___x_1770_);
if (v___x_1771_ == 0)
{
uint8_t v___x_1772_; lean_object* v___x_1773_; lean_object* v_fst_1774_; lean_object* v_snd_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1789_; 
lean_del_object(v___x_1763_);
v___x_1772_ = 1;
v___x_1773_ = l_Lean_sortExprs(v_snd_1761_, v___x_1772_);
v_fst_1774_ = lean_ctor_get(v___x_1773_, 0);
v_snd_1775_ = lean_ctor_get(v___x_1773_, 1);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1777_ = v___x_1773_;
v_isShared_1778_ = v_isSharedCheck_1789_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_snd_1775_);
lean_inc(v_fst_1774_);
lean_dec(v___x_1773_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1789_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1779_; lean_object* v___x_1781_; 
v___x_1779_ = l_Nat_Internal_Linear_ExprCnstr_applyPerm(v_snd_1775_, v_val_1765_);
lean_dec(v_snd_1775_);
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 1, v_fst_1774_);
lean_ctor_set(v___x_1777_, 0, v___x_1779_);
v___x_1781_ = v___x_1777_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1779_);
lean_ctor_set(v_reuseFailAlloc_1788_, 1, v_fst_1774_);
v___x_1781_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
lean_object* v___x_1783_; 
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 0, v___x_1781_);
v___x_1783_ = v___x_1767_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1781_);
v___x_1783_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
lean_object* v___x_1785_; 
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 0, v___x_1783_);
v___x_1785_ = v___x_1758_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1783_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
}
else
{
lean_object* v___x_1791_; 
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 0, v_val_1765_);
v___x_1791_ = v___x_1763_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_val_1765_);
lean_ctor_set(v_reuseFailAlloc_1798_, 1, v_snd_1761_);
v___x_1791_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
lean_object* v___x_1793_; 
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 0, v___x_1791_);
v___x_1793_ = v___x_1767_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v___x_1791_);
v___x_1793_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
lean_object* v___x_1795_; 
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 0, v___x_1793_);
v___x_1795_ = v___x_1758_;
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
}
}
}
}
}
else
{
lean_object* v___x_1802_; lean_object* v___x_1804_; 
lean_dec(v_fst_1760_);
lean_dec(v_a_1756_);
v___x_1802_ = lean_box(0);
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 0, v___x_1802_);
v___x_1804_ = v___x_1758_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v___x_1802_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
}
else
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1814_; 
v_a_1807_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1809_ = v___x_1755_;
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1755_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1812_; 
if (v_isShared_1810_ == 0)
{
v___x_1812_ = v___x_1809_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_a_1807_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearCnstr_x3f___boxed(lean_object* v_e_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l_Lean_Meta_Simp_Arith_Nat_toLinearCnstr_x3f(v_e_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_);
lean_dec(v_a_1819_);
lean_dec_ref(v_a_1818_);
lean_dec(v_a_1817_);
lean_dec_ref(v_a_1816_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0(lean_object* v___y_1822_){
_start:
{
lean_inc_ref(v___y_1822_);
return v___y_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0___boxed(lean_object* v___y_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0(v___y_1823_);
lean_dec_ref(v___y_1823_);
return v_res_1824_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1(void){
_start:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1826_ = lean_box(0);
v___x_1827_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__16));
v___x_1828_ = l_Lean_mkConst(v___x_1827_, v___x_1826_);
return v___x_1828_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__2(void){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1829_ = lean_unsigned_to_nat(0u);
v___x_1830_ = l_Lean_mkNatLit(v___x_1829_);
return v___x_1830_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__3(void){
_start:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1831_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__2, &l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__2);
v___x_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1831_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr(lean_object* v_ctx_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_){
_start:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; uint8_t v___x_1841_; 
v___x_1839_ = lean_unsigned_to_nat(0u);
v___x_1840_ = lean_array_get_size(v_ctx_1833_);
v___x_1841_ = lean_nat_dec_lt(v___x_1839_, v___x_1840_);
if (v___x_1841_ == 0)
{
lean_object* v___f_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
lean_dec_ref(v_ctx_1833_);
v___f_1842_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__0));
v___x_1843_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1, &l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1_once, _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1);
v___x_1844_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__3, &l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__3);
v___x_1845_ = l_Lean_RArray_toExpr___redArg(v___x_1843_, v___f_1842_, v___x_1844_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_);
return v___x_1845_;
}
else
{
lean_object* v___f_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___f_1846_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__0));
v___x_1847_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1, &l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1_once, _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1);
v___x_1848_ = l_Lean_RArray_ofArray___redArg(v_ctx_1833_);
v___x_1849_ = l_Lean_RArray_toExpr___redArg(v___x_1847_, v___f_1846_, v___x_1848_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_);
return v___x_1849_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr___boxed(lean_object* v_ctx_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(v_ctx_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
lean_dec(v_a_1854_);
lean_dec_ref(v_a_1853_);
lean_dec(v_a_1852_);
lean_dec_ref(v_a_1851_);
return v_res_1856_;
}
}
lean_object* runtime_initialize_Lean_Util_SortExprs(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_KExprMap(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_RArray(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Offset(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
lean_object* runtime_initialize_Lean_OrderLevel(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Util_SortExprs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_KExprMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_RArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_NatInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Offset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Internal_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_OrderLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr = _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr);
l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr = _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Util_SortExprs(uint8_t builtin);
lean_object* initialize_Lean_Meta_KExprMap(uint8_t builtin);
lean_object* initialize_Lean_Data_RArray(uint8_t builtin);
lean_object* initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
lean_object* initialize_Lean_Meta_Offset(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
lean_object* initialize_Lean_OrderLevel(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_SortExprs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_KExprMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_RArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_NatInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Offset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Internal_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_OrderLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
