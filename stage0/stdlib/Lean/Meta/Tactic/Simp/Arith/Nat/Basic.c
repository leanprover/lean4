// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Arith.Nat.Basic
// Imports: public import Lean.Util.SortExprs public import Lean.Meta.KExprMap import Lean.Data.RArray import Lean.Meta.NatInstTesters import Lean.Meta.Offset public import Init.Data.Nat.Linear
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatAdd(lean_object*, lean_object*);
lean_object* l_Lean_mkNatMul(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLE(lean_object*, lean_object*);
lean_object* l_Lean_mkNatEq(lean_object*, lean_object*);
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
lean_object* lean_array_get_size(lean_object*);
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
lean_object* l_Nat_Linear_Expr_inc(lean_object*);
lean_object* l_Lean_Meta_DefEq_isInstLTNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_sortExprs(lean_object*, uint8_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_RArray_toExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RArray_ofArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_applyPerm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_applyPerm___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_ExprCnstr_applyPerm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_ExprCnstr_applyPerm___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Nat.Linear.Expr.num"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__0_value)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Nat.Linear.Expr.var"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__5 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__5_value)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__6 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__7_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Nat.Linear.Expr.add"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__8 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__8_value)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__9 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__10 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__10_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Nat.Linear.Expr.mulL"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__11 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__11_value)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__12 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__12_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__13 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__13_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Nat.Linear.Expr.mulR"};
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
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linear"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Expr"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2_value;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(54, 114, 89, 174, 224, 251, 5, 100)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(132, 220, 159, 13, 188, 193, 50, 74)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(200, 85, 60, 149, 230, 17, 166, 106)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__5;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "var"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__6 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(54, 114, 89, 174, 224, 251, 5, 100)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(132, 220, 159, 13, 188, 193, 50, 74)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__6_value),LEAN_SCALAR_PTR_LITERAL(61, 234, 80, 121, 124, 63, 59, 252)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__8;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "add"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__9 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(54, 114, 89, 174, 224, 251, 5, 100)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(132, 220, 159, 13, 188, 193, 50, 74)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__9_value),LEAN_SCALAR_PTR_LITERAL(57, 92, 133, 25, 65, 222, 5, 197)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__11;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "mulL"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__12 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(54, 114, 89, 174, 224, 251, 5, 100)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(132, 220, 159, 13, 188, 193, 50, 74)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__12_value),LEAN_SCALAR_PTR_LITERAL(67, 83, 112, 118, 242, 20, 135, 66)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__14;
static const lean_string_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "mulR"};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__15 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__15_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(54, 114, 89, 174, 224, 251, 5, 100)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(132, 220, 159, 13, 188, 193, 50, 74)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__15_value),LEAN_SCALAR_PTR_LITERAL(38, 166, 194, 213, 128, 64, 206, 208)}};
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16_value;
static lean_once_cell_t l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__17;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(lean_object*);
static const lean_closure_object l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(54, 114, 89, 174, 224, 251, 5, 100)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(132, 220, 159, 13, 188, 193, 50, 74)}};
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
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(54, 114, 89, 174, 224, 251, 5, 100)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(57, 237, 130, 75, 136, 172, 225, 105)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(53, 198, 132, 235, 185, 195, 207, 218)}};
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
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(54, 114, 89, 174, 224, 251, 5, 100)}};
static const lean_ctor_object l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(57, 237, 130, 75, 136, 172, 225, 105)}};
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__9_value),LEAN_SCALAR_PTR_LITERAL(210, 189, 86, 121, 130, 22, 242, 236)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__9_value),LEAN_SCALAR_PTR_LITERAL(50, 34, 112, 179, 66, 45, 192, 92)}};
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(lean_object* v_a_1_, lean_object* v_x_2_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg___boxed(lean_object* v_a_10_, lean_object* v_x_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(v_a_10_, v_x_11_);
lean_dec(v_x_11_);
lean_dec(v_a_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0___redArg(lean_object* v_m_13_, lean_object* v_a_14_){
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
v___x_30_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(v_a_14_, v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0___redArg___boxed(lean_object* v_m_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0___redArg(v_m_31_, v_a_32_);
lean_dec(v_a_32_);
lean_dec_ref(v_m_31_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(lean_object* v_perm_34_, lean_object* v_a_35_){
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
v___x_37_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0___redArg(v_perm_34_, v_i_36_);
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
lean_dec_ref(v___x_37_);
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
v___x_52_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(v_perm_34_, v_a_47_);
v___x_53_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(v_perm_34_, v_b_48_);
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
v___x_63_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(v_perm_34_, v_a_59_);
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
v___x_73_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(v_perm_34_, v_a_68_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go___boxed(lean_object* v_perm_78_, lean_object* v_a_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(v_perm_78_, v_a_79_);
lean_dec_ref(v_perm_78_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0(lean_object* v_00_u03b2_81_, lean_object* v_m_82_, lean_object* v_a_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0___redArg(v_m_82_, v_a_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0___boxed(lean_object* v_00_u03b2_85_, lean_object* v_m_86_, lean_object* v_a_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0(v_00_u03b2_85_, v_m_86_, v_a_87_);
lean_dec(v_a_87_);
lean_dec_ref(v_m_86_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0(lean_object* v_00_u03b2_89_, lean_object* v_a_90_, lean_object* v_x_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(v_a_90_, v_x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_93_, lean_object* v_a_94_, lean_object* v_x_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0(v_00_u03b2_93_, v_a_94_, v_x_95_);
lean_dec(v_x_95_);
lean_dec(v_a_94_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_applyPerm(lean_object* v_perm_97_, lean_object* v_e_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(v_perm_97_, v_e_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_applyPerm___boxed(lean_object* v_perm_100_, lean_object* v_e_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Nat_Linear_Expr_applyPerm(v_perm_100_, v_e_101_);
lean_dec_ref(v_perm_100_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_ExprCnstr_applyPerm(lean_object* v_perm_103_, lean_object* v_x_104_){
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
v___x_111_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(v_perm_103_, v_lhs_106_);
v___x_112_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(v_perm_103_, v_rhs_107_);
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
LEAN_EXPORT lean_object* l_Nat_Linear_ExprCnstr_applyPerm___boxed(lean_object* v_perm_117_, lean_object* v_x_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Nat_Linear_ExprCnstr_applyPerm(v_perm_117_, v_x_118_);
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
lean_dec_ref(v_x_380_);
return v_head_384_;
}
else
{
lean_object* v_head_385_; lean_object* v___x_386_; 
lean_inc(v_tail_383_);
v_head_385_ = lean_ctor_get(v_x_380_, 0);
lean_inc(v_head_385_);
lean_dec_ref(v_x_380_);
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
lean_dec_ref(v_x_457_);
v___x_462_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg(v_head_461_);
return v___x_462_;
}
else
{
lean_object* v_head_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
lean_inc(v_tail_460_);
v_head_463_ = lean_ctor_get(v_x_457_, 0);
lean_inc(v_head_463_);
lean_dec_ref(v_x_457_);
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
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__5(void){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_560_ = lean_box(0);
v___x_561_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4));
v___x_562_ = l_Lean_mkConst(v___x_561_, v___x_560_);
return v___x_562_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__8(void){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_569_ = lean_box(0);
v___x_570_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7));
v___x_571_ = l_Lean_mkConst(v___x_570_, v___x_569_);
return v___x_571_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__11(void){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_578_ = lean_box(0);
v___x_579_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10));
v___x_580_ = l_Lean_mkConst(v___x_579_, v___x_578_);
return v___x_580_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__14(void){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_587_ = lean_box(0);
v___x_588_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13));
v___x_589_ = l_Lean_mkConst(v___x_588_, v___x_587_);
return v___x_589_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__17(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_596_ = lean_box(0);
v___x_597_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16));
v___x_598_ = l_Lean_mkConst(v___x_597_, v___x_596_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(lean_object* v_e_599_){
_start:
{
switch(lean_obj_tag(v_e_599_))
{
case 0:
{
lean_object* v_v_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v_v_600_ = lean_ctor_get(v_e_599_, 0);
lean_inc(v_v_600_);
lean_dec_ref(v_e_599_);
v___x_601_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__5, &l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__5);
v___x_602_ = l_Lean_mkNatLit(v_v_600_);
v___x_603_ = l_Lean_Expr_app___override(v___x_601_, v___x_602_);
return v___x_603_;
}
case 1:
{
lean_object* v_i_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v_i_604_ = lean_ctor_get(v_e_599_, 0);
lean_inc(v_i_604_);
lean_dec_ref(v_e_599_);
v___x_605_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__8, &l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__8_once, _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__8);
v___x_606_ = l_Lean_mkNatLit(v_i_604_);
v___x_607_ = l_Lean_Expr_app___override(v___x_605_, v___x_606_);
return v___x_607_;
}
case 2:
{
lean_object* v_a_608_; lean_object* v_b_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v_a_608_ = lean_ctor_get(v_e_599_, 0);
lean_inc_ref(v_a_608_);
v_b_609_ = lean_ctor_get(v_e_599_, 1);
lean_inc_ref(v_b_609_);
lean_dec_ref(v_e_599_);
v___x_610_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__11, &l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__11_once, _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__11);
v___x_611_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v_a_608_);
v___x_612_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v_b_609_);
v___x_613_ = l_Lean_mkAppB(v___x_610_, v___x_611_, v___x_612_);
return v___x_613_;
}
case 3:
{
lean_object* v_k_614_; lean_object* v_a_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v_k_614_ = lean_ctor_get(v_e_599_, 0);
lean_inc(v_k_614_);
v_a_615_ = lean_ctor_get(v_e_599_, 1);
lean_inc_ref(v_a_615_);
lean_dec_ref(v_e_599_);
v___x_616_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__14, &l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__14);
v___x_617_ = l_Lean_mkNatLit(v_k_614_);
v___x_618_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v_a_615_);
v___x_619_ = l_Lean_mkAppB(v___x_616_, v___x_617_, v___x_618_);
return v___x_619_;
}
default: 
{
lean_object* v_a_620_; lean_object* v_k_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v_a_620_ = lean_ctor_get(v_e_599_, 0);
lean_inc_ref(v_a_620_);
v_k_621_ = lean_ctor_get(v_e_599_, 1);
lean_inc(v_k_621_);
lean_dec_ref(v_e_599_);
v___x_622_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__17, &l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__17);
v___x_623_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v_a_620_);
v___x_624_ = l_Lean_mkNatLit(v_k_621_);
v___x_625_ = l_Lean_mkAppB(v___x_622_, v___x_623_, v___x_624_);
return v___x_625_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__2(void){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_631_ = lean_box(0);
v___x_632_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1));
v___x_633_ = l_Lean_mkConst(v___x_632_, v___x_631_);
return v___x_633_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__3(void){
_start:
{
lean_object* v___x_634_; lean_object* v___f_635_; lean_object* v___x_636_; 
v___x_634_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__2, &l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__2);
v___f_635_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__0));
v___x_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_636_, 0, v___f_635_);
lean_ctor_set(v___x_636_, 1, v___x_634_);
return v___x_636_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr(void){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__3, &l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__3);
return v___x_637_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__3(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_645_ = lean_box(0);
v___x_646_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2));
v___x_647_ = l_Lean_mkConst(v___x_646_, v___x_645_);
return v___x_647_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__7(void){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_653_ = lean_box(0);
v___x_654_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__6));
v___x_655_ = l_Lean_mkConst(v___x_654_, v___x_653_);
return v___x_655_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__10(void){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_660_ = lean_box(0);
v___x_661_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__9));
v___x_662_ = l_Lean_mkConst(v___x_661_, v___x_660_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(lean_object* v_c_663_){
_start:
{
uint8_t v_eq_664_; lean_object* v_lhs_665_; lean_object* v_rhs_666_; lean_object* v___x_667_; lean_object* v___y_669_; 
v_eq_664_ = lean_ctor_get_uint8(v_c_663_, sizeof(void*)*2);
v_lhs_665_ = lean_ctor_get(v_c_663_, 0);
lean_inc_ref(v_lhs_665_);
v_rhs_666_ = lean_ctor_get(v_c_663_, 1);
lean_inc_ref(v_rhs_666_);
lean_dec_ref(v_c_663_);
v___x_667_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__3, &l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__3);
if (v_eq_664_ == 0)
{
lean_object* v___x_673_; 
v___x_673_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__7, &l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__7_once, _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__7);
v___y_669_ = v___x_673_;
goto v___jp_668_;
}
else
{
lean_object* v___x_674_; 
v___x_674_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__10, &l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__10_once, _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__10);
v___y_669_ = v___x_674_;
goto v___jp_668_;
}
v___jp_668_:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_670_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v_lhs_665_);
v___x_671_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v_rhs_666_);
v___x_672_ = l_Lean_mkApp3(v___x_667_, v___y_669_, v___x_670_, v___x_671_);
return v___x_672_;
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__2(void){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_680_ = lean_box(0);
v___x_681_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1));
v___x_682_ = l_Lean_mkConst(v___x_681_, v___x_680_);
return v___x_682_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__3(void){
_start:
{
lean_object* v___x_683_; lean_object* v___f_684_; lean_object* v___x_685_; 
v___x_683_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__2, &l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__2);
v___f_684_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__0));
v___x_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_685_, 0, v___f_684_);
lean_ctor_set(v___x_685_, 1, v___x_683_);
return v___x_685_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr(void){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__3, &l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__3);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(lean_object* v_ctx_687_, lean_object* v_e_688_){
_start:
{
switch(lean_obj_tag(v_e_688_))
{
case 0:
{
lean_object* v_v_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_698_; 
v_v_690_ = lean_ctor_get(v_e_688_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v_e_688_);
if (v_isSharedCheck_698_ == 0)
{
v___x_692_ = v_e_688_;
v_isShared_693_ = v_isSharedCheck_698_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_v_690_);
lean_dec(v_e_688_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_698_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_694_; lean_object* v___x_696_; 
v___x_694_ = l_Lean_mkNatLit(v_v_690_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v___x_694_);
v___x_696_ = v___x_692_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v___x_694_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
case 1:
{
lean_object* v_i_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_708_; 
v_i_699_ = lean_ctor_get(v_e_688_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v_e_688_);
if (v_isSharedCheck_708_ == 0)
{
v___x_701_ = v_e_688_;
v_isShared_702_ = v_isSharedCheck_708_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_i_699_);
lean_dec(v_e_688_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_708_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_706_; 
v___x_703_ = l_Lean_instInhabitedExpr;
v___x_704_ = lean_array_get_borrowed(v___x_703_, v_ctx_687_, v_i_699_);
lean_dec(v_i_699_);
lean_inc(v___x_704_);
if (v_isShared_702_ == 0)
{
lean_ctor_set_tag(v___x_701_, 0);
lean_ctor_set(v___x_701_, 0, v___x_704_);
v___x_706_ = v___x_701_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_704_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
case 2:
{
lean_object* v_a_709_; lean_object* v_b_710_; lean_object* v___x_711_; lean_object* v_a_712_; lean_object* v___x_713_; lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_722_; 
v_a_709_ = lean_ctor_get(v_e_688_, 0);
lean_inc_ref(v_a_709_);
v_b_710_ = lean_ctor_get(v_e_688_, 1);
lean_inc_ref(v_b_710_);
lean_dec_ref(v_e_688_);
v___x_711_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_ctx_687_, v_a_709_);
v_a_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_a_712_);
lean_dec_ref(v___x_711_);
v___x_713_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_ctx_687_, v_b_710_);
v_a_714_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_722_ == 0)
{
v___x_716_ = v___x_713_;
v_isShared_717_ = v_isSharedCheck_722_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_713_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_722_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_718_; lean_object* v___x_720_; 
v___x_718_ = l_Lean_mkNatAdd(v_a_712_, v_a_714_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 0, v___x_718_);
v___x_720_ = v___x_716_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_718_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
case 3:
{
lean_object* v_k_723_; lean_object* v_a_724_; lean_object* v___x_725_; lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_735_; 
v_k_723_ = lean_ctor_get(v_e_688_, 0);
lean_inc(v_k_723_);
v_a_724_ = lean_ctor_get(v_e_688_, 1);
lean_inc_ref(v_a_724_);
lean_dec_ref(v_e_688_);
v___x_725_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_ctx_687_, v_a_724_);
v_a_726_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_735_ == 0)
{
v___x_728_ = v___x_725_;
v_isShared_729_ = v_isSharedCheck_735_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_725_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_735_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_733_; 
v___x_730_ = l_Lean_mkNatLit(v_k_723_);
v___x_731_ = l_Lean_mkNatMul(v___x_730_, v_a_726_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 0, v___x_731_);
v___x_733_ = v___x_728_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_731_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
default: 
{
lean_object* v_a_736_; lean_object* v_k_737_; lean_object* v___x_738_; lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_748_; 
v_a_736_ = lean_ctor_get(v_e_688_, 0);
lean_inc_ref(v_a_736_);
v_k_737_ = lean_ctor_get(v_e_688_, 1);
lean_inc(v_k_737_);
lean_dec_ref(v_e_688_);
v___x_738_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_ctx_687_, v_a_736_);
v_a_739_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_748_ == 0)
{
v___x_741_ = v___x_738_;
v_isShared_742_ = v_isSharedCheck_748_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_738_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_748_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_746_; 
v___x_743_ = l_Lean_mkNatLit(v_k_737_);
v___x_744_ = l_Lean_mkNatMul(v_a_739_, v___x_743_);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 0, v___x_744_);
v___x_746_ = v___x_741_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_744_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg___boxed(lean_object* v_ctx_749_, lean_object* v_e_750_, lean_object* v_a_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_ctx_749_, v_e_750_);
lean_dec_ref(v_ctx_749_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith(lean_object* v_ctx_753_, lean_object* v_e_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_ctx_753_, v_e_754_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___boxed(lean_object* v_ctx_761_, lean_object* v_e_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith(v_ctx_761_, v_e_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_);
lean_dec(v_a_766_);
lean_dec_ref(v_a_765_);
lean_dec(v_a_764_);
lean_dec_ref(v_a_763_);
lean_dec_ref(v_ctx_761_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(lean_object* v_ctx_769_, lean_object* v_c_770_){
_start:
{
uint8_t v_eq_772_; 
v_eq_772_ = lean_ctor_get_uint8(v_c_770_, sizeof(void*)*2);
if (v_eq_772_ == 0)
{
lean_object* v_lhs_773_; lean_object* v_rhs_774_; lean_object* v___x_775_; lean_object* v_a_776_; lean_object* v___x_777_; lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_786_; 
v_lhs_773_ = lean_ctor_get(v_c_770_, 0);
lean_inc_ref(v_lhs_773_);
v_rhs_774_ = lean_ctor_get(v_c_770_, 1);
lean_inc_ref(v_rhs_774_);
lean_dec_ref(v_c_770_);
v___x_775_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_ctx_769_, v_lhs_773_);
v_a_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_a_776_);
lean_dec_ref(v___x_775_);
v___x_777_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_ctx_769_, v_rhs_774_);
v_a_778_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_786_ == 0)
{
v___x_780_ = v___x_777_;
v_isShared_781_ = v_isSharedCheck_786_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_777_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_786_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_782_ = l_Lean_mkNatLE(v_a_776_, v_a_778_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 0, v___x_782_);
v___x_784_ = v___x_780_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
else
{
lean_object* v_lhs_787_; lean_object* v_rhs_788_; lean_object* v___x_789_; lean_object* v_a_790_; lean_object* v___x_791_; lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_800_; 
v_lhs_787_ = lean_ctor_get(v_c_770_, 0);
lean_inc_ref(v_lhs_787_);
v_rhs_788_ = lean_ctor_get(v_c_770_, 1);
lean_inc_ref(v_rhs_788_);
lean_dec_ref(v_c_770_);
v___x_789_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_ctx_769_, v_lhs_787_);
v_a_790_ = lean_ctor_get(v___x_789_, 0);
lean_inc(v_a_790_);
lean_dec_ref(v___x_789_);
v___x_791_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_ctx_769_, v_rhs_788_);
v_a_792_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_800_ == 0)
{
v___x_794_ = v___x_791_;
v_isShared_795_ = v_isSharedCheck_800_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_791_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_800_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_796_; lean_object* v___x_798_; 
v___x_796_ = l_Lean_mkNatEq(v_a_790_, v_a_792_);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 0, v___x_796_);
v___x_798_ = v___x_794_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_796_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg___boxed(lean_object* v_ctx_801_, lean_object* v_c_802_, lean_object* v_a_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(v_ctx_801_, v_c_802_);
lean_dec_ref(v_ctx_801_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith(lean_object* v_ctx_805_, lean_object* v_c_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(v_ctx_805_, v_c_806_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___boxed(lean_object* v_ctx_813_, lean_object* v_c_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith(v_ctx_813_, v_c_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_);
lean_dec(v_a_818_);
lean_dec_ref(v_a_817_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
lean_dec_ref(v_ctx_813_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(lean_object* v_e_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_){
_start:
{
lean_object* v___x_828_; lean_object* v_varMap_829_; lean_object* v___x_830_; 
v___x_828_ = lean_st_ref_get(v_a_822_);
v_varMap_829_ = lean_ctor_get(v___x_828_, 0);
lean_inc_ref(v_varMap_829_);
lean_dec(v___x_828_);
lean_inc_ref(v_e_821_);
v___x_830_ = l_Lean_Meta_KExprMap_find_x3f___redArg(v_varMap_829_, v_e_821_, v_a_823_, v_a_824_, v_a_825_, v_a_826_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_879_; 
v_a_831_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_879_ == 0)
{
v___x_833_ = v___x_830_;
v_isShared_834_ = v_isSharedCheck_879_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_830_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_879_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
if (lean_obj_tag(v_a_831_) == 1)
{
lean_object* v_val_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_845_; 
lean_dec_ref(v_e_821_);
v_val_835_ = lean_ctor_get(v_a_831_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v_a_831_);
if (v_isSharedCheck_845_ == 0)
{
v___x_837_ = v_a_831_;
v_isShared_838_ = v_isSharedCheck_845_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_val_835_);
lean_dec(v_a_831_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_845_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_val_835_);
v___x_840_ = v_reuseFailAlloc_844_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
lean_object* v___x_842_; 
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 0, v___x_840_);
v___x_842_ = v___x_833_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_840_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
else
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v_vars_848_; lean_object* v_varMap_849_; lean_object* v_vars_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_878_; 
lean_del_object(v___x_833_);
lean_dec(v_a_831_);
v___x_846_ = lean_st_ref_get(v_a_822_);
v___x_847_ = lean_st_ref_get(v_a_822_);
v_vars_848_ = lean_ctor_get(v___x_846_, 1);
lean_inc_ref(v_vars_848_);
lean_dec(v___x_846_);
v_varMap_849_ = lean_ctor_get(v___x_847_, 0);
v_vars_850_ = lean_ctor_get(v___x_847_, 1);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_878_ == 0)
{
v___x_852_ = v___x_847_;
v_isShared_853_ = v_isSharedCheck_878_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_vars_850_);
lean_inc(v_varMap_849_);
lean_dec(v___x_847_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_878_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = lean_array_get_size(v_vars_848_);
lean_dec_ref(v_vars_848_);
lean_inc_ref(v_e_821_);
v___x_855_ = l_Lean_Meta_KExprMap_insert___redArg(v_varMap_849_, v_e_821_, v___x_854_, v_a_823_, v_a_824_, v_a_825_, v_a_826_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_869_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_869_ == 0)
{
v___x_858_ = v___x_855_;
v_isShared_859_ = v_isSharedCheck_869_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_855_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_869_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_860_; lean_object* v___x_862_; 
v___x_860_ = lean_array_push(v_vars_850_, v_e_821_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 1, v___x_860_);
lean_ctor_set(v___x_852_, 0, v_a_856_);
v___x_862_ = v___x_852_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_856_);
lean_ctor_set(v_reuseFailAlloc_868_, 1, v___x_860_);
v___x_862_ = v_reuseFailAlloc_868_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_866_; 
v___x_863_ = lean_st_ref_set(v_a_822_, v___x_862_);
v___x_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_864_, 0, v___x_854_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v___x_864_);
v___x_866_ = v___x_858_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_864_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
else
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
lean_del_object(v___x_852_);
lean_dec_ref(v_vars_850_);
lean_dec_ref(v_e_821_);
v_a_870_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v___x_855_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_855_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_870_);
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
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
lean_dec_ref(v_e_821_);
v_a_880_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_830_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_830_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar___boxed(lean_object* v_e_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
lean_dec(v_a_891_);
lean_dec_ref(v_a_890_);
lean_dec(v_a_889_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit(lean_object* v_e_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_){
_start:
{
lean_object* v___x_940_; 
lean_inc_ref(v_e_933_);
v___x_940_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_933_, v_a_936_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v_a_941_; lean_object* v___x_942_; uint8_t v___x_943_; 
v_a_941_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_a_941_);
lean_dec_ref(v___x_940_);
v___x_942_ = l_Lean_Expr_cleanupAnnotations(v_a_941_);
v___x_943_ = l_Lean_Expr_isApp(v___x_942_);
if (v___x_943_ == 0)
{
lean_object* v___x_944_; 
lean_dec_ref(v___x_942_);
v___x_944_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
return v___x_944_;
}
else
{
lean_object* v_arg_945_; lean_object* v___x_946_; lean_object* v___x_947_; uint8_t v___x_948_; 
v_arg_945_ = lean_ctor_get(v___x_942_, 1);
lean_inc_ref(v_arg_945_);
v___x_946_ = l_Lean_Expr_appFnCleanup___redArg(v___x_942_);
v___x_947_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__1));
v___x_948_ = l_Lean_Expr_isConstOf(v___x_946_, v___x_947_);
if (v___x_948_ == 0)
{
uint8_t v___x_949_; 
v___x_949_ = l_Lean_Expr_isApp(v___x_946_);
if (v___x_949_ == 0)
{
lean_object* v___x_950_; 
lean_dec_ref(v___x_946_);
lean_dec_ref(v_arg_945_);
v___x_950_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
return v___x_950_;
}
else
{
lean_object* v_arg_951_; lean_object* v_b_953_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v___y_958_; lean_object* v___x_1002_; lean_object* v___x_1003_; uint8_t v___x_1004_; 
v_arg_951_ = lean_ctor_get(v___x_946_, 1);
lean_inc_ref(v_arg_951_);
v___x_1002_ = l_Lean_Expr_appFnCleanup___redArg(v___x_946_);
v___x_1003_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__3));
v___x_1004_ = l_Lean_Expr_isConstOf(v___x_1002_, v___x_1003_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1005_; uint8_t v___x_1006_; 
v___x_1005_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__4));
v___x_1006_ = l_Lean_Expr_isConstOf(v___x_1002_, v___x_1005_);
if (v___x_1006_ == 0)
{
uint8_t v___x_1007_; 
v___x_1007_ = l_Lean_Expr_isApp(v___x_1002_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1008_; 
lean_dec_ref(v___x_1002_);
lean_dec_ref(v_arg_951_);
lean_dec_ref(v_arg_945_);
v___x_1008_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
return v___x_1008_;
}
else
{
lean_object* v_arg_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; uint8_t v___x_1012_; 
v_arg_1009_ = lean_ctor_get(v___x_1002_, 1);
lean_inc_ref(v_arg_1009_);
v___x_1010_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1002_);
v___x_1011_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__7));
v___x_1012_ = l_Lean_Expr_isConstOf(v___x_1010_, v___x_1011_);
if (v___x_1012_ == 0)
{
uint8_t v___x_1013_; 
v___x_1013_ = l_Lean_Expr_isApp(v___x_1010_);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; 
lean_dec_ref(v___x_1010_);
lean_dec_ref(v_arg_1009_);
lean_dec_ref(v_arg_951_);
lean_dec_ref(v_arg_945_);
v___x_1014_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
return v___x_1014_;
}
else
{
lean_object* v___x_1015_; lean_object* v___x_1016_; uint8_t v___x_1017_; 
v___x_1015_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1010_);
v___x_1016_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__9));
v___x_1017_ = l_Lean_Expr_isConstOf(v___x_1015_, v___x_1016_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; uint8_t v___x_1019_; 
v___x_1018_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__11));
v___x_1019_ = l_Lean_Expr_isConstOf(v___x_1015_, v___x_1018_);
if (v___x_1019_ == 0)
{
uint8_t v___x_1020_; 
v___x_1020_ = l_Lean_Expr_isApp(v___x_1015_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; 
lean_dec_ref(v___x_1015_);
lean_dec_ref(v_arg_1009_);
lean_dec_ref(v_arg_951_);
lean_dec_ref(v_arg_945_);
v___x_1021_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
return v___x_1021_;
}
else
{
lean_object* v___x_1022_; uint8_t v___x_1023_; 
v___x_1022_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1015_);
v___x_1023_ = l_Lean_Expr_isApp(v___x_1022_);
if (v___x_1023_ == 0)
{
lean_object* v___x_1024_; 
lean_dec_ref(v___x_1022_);
lean_dec_ref(v_arg_1009_);
lean_dec_ref(v_arg_951_);
lean_dec_ref(v_arg_945_);
v___x_1024_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
return v___x_1024_;
}
else
{
lean_object* v___x_1025_; lean_object* v___x_1026_; uint8_t v___x_1027_; 
v___x_1025_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1022_);
v___x_1026_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__14));
v___x_1027_ = l_Lean_Expr_isConstOf(v___x_1025_, v___x_1026_);
if (v___x_1027_ == 0)
{
lean_object* v___x_1028_; uint8_t v___x_1029_; 
v___x_1028_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__17));
v___x_1029_ = l_Lean_Expr_isConstOf(v___x_1025_, v___x_1028_);
lean_dec_ref(v___x_1025_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1030_; 
lean_dec_ref(v_arg_1009_);
lean_dec_ref(v_arg_951_);
lean_dec_ref(v_arg_945_);
v___x_1030_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
return v___x_1030_;
}
else
{
lean_object* v___x_1031_; 
v___x_1031_ = l_Lean_Meta_DefEq_isInstHAddNat(v_arg_1009_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; uint8_t v___x_1033_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_a_1032_);
lean_dec_ref(v___x_1031_);
v___x_1033_ = lean_unbox(v_a_1032_);
lean_dec(v_a_1032_);
if (v___x_1033_ == 0)
{
lean_object* v___x_1034_; 
lean_dec_ref(v_arg_951_);
lean_dec_ref(v_arg_945_);
v___x_1034_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
return v___x_1034_;
}
else
{
lean_object* v___x_1035_; 
lean_dec_ref(v_e_933_);
v___x_1035_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_951_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; lean_object* v___x_1037_; 
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_a_1036_);
lean_dec_ref(v___x_1035_);
v___x_1037_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_945_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1046_; 
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1040_ = v___x_1037_;
v_isShared_1041_ = v_isSharedCheck_1046_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1037_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1046_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1042_; lean_object* v___x_1044_; 
v___x_1042_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1042_, 0, v_a_1036_);
lean_ctor_set(v___x_1042_, 1, v_a_1038_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 0, v___x_1042_);
v___x_1044_ = v___x_1040_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1042_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
else
{
lean_dec(v_a_1036_);
return v___x_1037_;
}
}
else
{
lean_dec_ref(v_arg_945_);
return v___x_1035_;
}
}
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
lean_dec_ref(v_arg_951_);
lean_dec_ref(v_arg_945_);
lean_dec_ref(v_e_933_);
v_a_1047_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_1031_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1031_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
}
else
{
lean_object* v___x_1055_; 
lean_dec_ref(v___x_1025_);
v___x_1055_ = l_Lean_Meta_DefEq_isInstHMulNat(v_arg_1009_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v_a_1056_; uint8_t v___x_1057_; 
v_a_1056_ = lean_ctor_get(v___x_1055_, 0);
lean_inc(v_a_1056_);
lean_dec_ref(v___x_1055_);
v___x_1057_ = lean_unbox(v_a_1056_);
lean_dec(v_a_1056_);
if (v___x_1057_ == 0)
{
lean_object* v___x_1058_; 
lean_dec_ref(v_arg_951_);
lean_dec_ref(v_arg_945_);
v___x_1058_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
return v___x_1058_;
}
else
{
v_b_953_ = v_arg_945_;
v___y_954_ = v_a_934_;
v___y_955_ = v_a_935_;
v___y_956_ = v_a_936_;
v___y_957_ = v_a_937_;
v___y_958_ = v_a_938_;
goto v___jp_952_;
}
}
else
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
lean_dec_ref(v_arg_951_);
lean_dec_ref(v_arg_945_);
lean_dec_ref(v_e_933_);
v_a_1059_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1061_ = v___x_1055_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1055_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1064_; 
if (v_isShared_1062_ == 0)
{
v___x_1064_ = v___x_1061_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1059_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1067_; 
lean_dec_ref(v___x_1015_);
v___x_1067_ = l_Lean_Meta_DefEq_isInstAddNat(v_arg_1009_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v_a_1068_; uint8_t v___x_1069_; 
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_a_1068_);
lean_dec_ref(v___x_1067_);
v___x_1069_ = lean_unbox(v_a_1068_);
lean_dec(v_a_1068_);
if (v___x_1069_ == 0)
{
lean_object* v___x_1070_; 
lean_dec_ref(v_arg_951_);
lean_dec_ref(v_arg_945_);
v___x_1070_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
return v___x_1070_;
}
else
{
lean_object* v___x_1071_; 
lean_dec_ref(v_e_933_);
v___x_1071_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_951_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v___x_1073_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_a_1072_);
lean_dec_ref(v___x_1071_);
v___x_1073_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_945_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1082_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1076_ = v___x_1073_;
v_isShared_1077_ = v_isSharedCheck_1082_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1073_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1082_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1078_; lean_object* v___x_1080_; 
v___x_1078_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1078_, 0, v_a_1072_);
lean_ctor_set(v___x_1078_, 1, v_a_1074_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 0, v___x_1078_);
v___x_1080_ = v___x_1076_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
else
{
lean_dec(v_a_1072_);
return v___x_1073_;
}
}
else
{
lean_dec_ref(v_arg_945_);
return v___x_1071_;
}
}
}
else
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
lean_dec_ref(v_arg_951_);
lean_dec_ref(v_arg_945_);
lean_dec_ref(v_e_933_);
v_a_1083_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1085_ = v___x_1067_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1067_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1083_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
}
else
{
lean_object* v___x_1091_; 
lean_dec_ref(v___x_1015_);
v___x_1091_ = l_Lean_Meta_DefEq_isInstMulNat(v_arg_1009_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; uint8_t v___x_1093_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc(v_a_1092_);
lean_dec_ref(v___x_1091_);
v___x_1093_ = lean_unbox(v_a_1092_);
lean_dec(v_a_1092_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1094_; 
lean_dec_ref(v_arg_951_);
lean_dec_ref(v_arg_945_);
v___x_1094_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
return v___x_1094_;
}
else
{
v_b_953_ = v_arg_945_;
v___y_954_ = v_a_934_;
v___y_955_ = v_a_935_;
v___y_956_ = v_a_936_;
v___y_957_ = v_a_937_;
v___y_958_ = v_a_938_;
goto v___jp_952_;
}
}
else
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
lean_dec_ref(v_arg_951_);
lean_dec_ref(v_arg_945_);
lean_dec_ref(v_e_933_);
v_a_1095_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1091_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1091_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
}
}
else
{
lean_object* v___x_1103_; 
lean_dec_ref(v___x_1010_);
lean_dec_ref(v_arg_1009_);
lean_inc_ref(v_arg_945_);
v___x_1103_ = l_Lean_Meta_Structural_isInstOfNatNat___redArg(v_arg_945_, v_a_936_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v_a_1104_; uint8_t v___x_1105_; 
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
lean_inc(v_a_1104_);
lean_dec_ref(v___x_1103_);
v___x_1105_ = lean_unbox(v_a_1104_);
lean_dec(v_a_1104_);
if (v___x_1105_ == 0)
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
lean_inc_ref(v_arg_951_);
v___x_1106_ = l_Lean_mkInstOfNatNat(v_arg_951_);
v___x_1107_ = l_Lean_Meta_isDefEqI(v_arg_945_, v___x_1106_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v_a_1108_; uint8_t v___x_1109_; 
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_a_1108_);
lean_dec_ref(v___x_1107_);
v___x_1109_ = lean_unbox(v_a_1108_);
lean_dec(v_a_1108_);
if (v___x_1109_ == 0)
{
lean_object* v___x_1110_; 
lean_dec_ref(v_arg_951_);
v___x_1110_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
return v___x_1110_;
}
else
{
lean_object* v___x_1111_; 
lean_dec_ref(v_e_933_);
v___x_1111_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_951_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
return v___x_1111_;
}
}
else
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
lean_dec_ref(v_arg_951_);
lean_dec_ref(v_e_933_);
v_a_1112_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v___x_1107_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1107_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1112_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
}
else
{
lean_object* v___x_1120_; 
lean_dec_ref(v_arg_945_);
lean_dec_ref(v_e_933_);
v___x_1120_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_951_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
return v___x_1120_;
}
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
lean_dec_ref(v_arg_951_);
lean_dec_ref(v_arg_945_);
lean_dec_ref(v_e_933_);
v_a_1121_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1123_ = v___x_1103_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1103_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1121_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
}
}
else
{
lean_object* v___x_1129_; 
lean_dec_ref(v___x_1002_);
lean_dec_ref(v_e_933_);
v___x_1129_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_951_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_object* v_a_1130_; lean_object* v___x_1131_; 
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_a_1130_);
lean_dec_ref(v___x_1129_);
v___x_1131_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_945_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1140_; 
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1134_ = v___x_1131_;
v_isShared_1135_ = v_isSharedCheck_1140_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1131_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1140_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1136_; lean_object* v___x_1138_; 
v___x_1136_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1136_, 0, v_a_1130_);
lean_ctor_set(v___x_1136_, 1, v_a_1132_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 0, v___x_1136_);
v___x_1138_ = v___x_1134_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1136_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
else
{
lean_dec(v_a_1130_);
return v___x_1131_;
}
}
else
{
lean_dec_ref(v_arg_945_);
return v___x_1129_;
}
}
}
else
{
lean_dec_ref(v___x_1002_);
v_b_953_ = v_arg_945_;
v___y_954_ = v_a_934_;
v___y_955_ = v_a_935_;
v___y_956_ = v_a_936_;
v___y_957_ = v_a_937_;
v___y_958_ = v_a_938_;
goto v___jp_952_;
}
v___jp_952_:
{
lean_object* v___x_959_; 
lean_inc_ref(v_arg_951_);
v___x_959_ = l_Lean_Meta_evalNat(v_arg_951_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_a_960_; 
v_a_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_a_960_);
lean_dec_ref(v___x_959_);
if (lean_obj_tag(v_a_960_) == 0)
{
lean_object* v___x_961_; 
v___x_961_ = l_Lean_Meta_evalNat(v_b_953_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_a_962_; 
v_a_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_a_962_);
lean_dec_ref(v___x_961_);
if (lean_obj_tag(v_a_962_) == 0)
{
lean_object* v___x_963_; 
lean_dec_ref(v_arg_951_);
v___x_963_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_933_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
return v___x_963_;
}
else
{
lean_object* v_val_964_; lean_object* v___x_965_; 
lean_dec_ref(v_e_933_);
v_val_964_ = lean_ctor_get(v_a_962_, 0);
lean_inc(v_val_964_);
lean_dec_ref(v_a_962_);
v___x_965_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_951_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
if (lean_obj_tag(v___x_965_) == 0)
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_974_; 
v_a_966_ = lean_ctor_get(v___x_965_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_965_);
if (v_isSharedCheck_974_ == 0)
{
v___x_968_ = v___x_965_;
v_isShared_969_ = v_isSharedCheck_974_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_965_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_974_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_970_; lean_object* v___x_972_; 
v___x_970_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_970_, 0, v_a_966_);
lean_ctor_set(v___x_970_, 1, v_val_964_);
if (v_isShared_969_ == 0)
{
lean_ctor_set(v___x_968_, 0, v___x_970_);
v___x_972_ = v___x_968_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v___x_970_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
else
{
lean_dec(v_val_964_);
return v___x_965_;
}
}
}
else
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
lean_dec_ref(v_arg_951_);
lean_dec_ref(v_e_933_);
v_a_975_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___x_961_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_961_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_975_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
else
{
lean_object* v_val_983_; lean_object* v___x_984_; 
lean_dec_ref(v_arg_951_);
lean_dec_ref(v_e_933_);
v_val_983_ = lean_ctor_get(v_a_960_, 0);
lean_inc(v_val_983_);
lean_dec_ref(v_a_960_);
v___x_984_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_b_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_993_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_993_ == 0)
{
v___x_987_ = v___x_984_;
v_isShared_988_ = v_isSharedCheck_993_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_984_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_993_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_989_; lean_object* v___x_991_; 
v___x_989_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_989_, 0, v_val_983_);
lean_ctor_set(v___x_989_, 1, v_a_985_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 0, v___x_989_);
v___x_991_ = v___x_987_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_989_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
else
{
lean_dec(v_val_983_);
return v___x_984_;
}
}
}
else
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1001_; 
lean_dec_ref(v_b_953_);
lean_dec_ref(v_arg_951_);
lean_dec_ref(v_e_933_);
v_a_994_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_996_ = v___x_959_;
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_959_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_999_; 
if (v_isShared_997_ == 0)
{
v___x_999_ = v___x_996_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_a_994_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
}
}
else
{
lean_object* v___x_1141_; 
lean_dec_ref(v___x_946_);
lean_dec_ref(v_e_933_);
v___x_1141_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_945_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1150_; 
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1144_ = v___x_1141_;
v_isShared_1145_ = v_isSharedCheck_1150_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1141_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1150_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1146_; lean_object* v___x_1148_; 
v___x_1146_ = l_Nat_Linear_Expr_inc(v_a_1142_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 0, v___x_1146_);
v___x_1148_ = v___x_1144_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1146_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
else
{
return v___x_1141_;
}
}
}
}
else
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1158_; 
lean_dec_ref(v_e_933_);
v_a_1151_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1153_ = v___x_940_;
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_940_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1156_; 
if (v_isShared_1154_ == 0)
{
v___x_1156_ = v___x_1153_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_a_1151_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(lean_object* v_e_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_){
_start:
{
switch(lean_obj_tag(v_e_1159_))
{
case 9:
{
lean_object* v_a_1166_; 
v_a_1166_ = lean_ctor_get(v_e_1159_, 0);
lean_inc_ref(v_a_1166_);
if (lean_obj_tag(v_a_1166_) == 0)
{
lean_object* v_val_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1175_; 
lean_dec_ref(v_e_1159_);
v_val_1167_ = lean_ctor_get(v_a_1166_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v_a_1166_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1169_ = v_a_1166_;
v_isShared_1170_ = v_isSharedCheck_1175_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_val_1167_);
lean_dec(v_a_1166_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1175_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_val_1167_);
v___x_1172_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
lean_object* v___x_1173_; 
v___x_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
return v___x_1173_;
}
}
}
else
{
lean_object* v___x_1176_; 
lean_dec_ref(v_a_1166_);
v___x_1176_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
return v___x_1176_;
}
}
case 10:
{
lean_object* v_expr_1177_; 
v_expr_1177_ = lean_ctor_get(v_e_1159_, 1);
lean_inc_ref(v_expr_1177_);
lean_dec_ref(v_e_1159_);
v_e_1159_ = v_expr_1177_;
goto _start;
}
case 4:
{
lean_object* v_declName_1179_; 
v_declName_1179_ = lean_ctor_get(v_e_1159_, 0);
if (lean_obj_tag(v_declName_1179_) == 1)
{
lean_object* v_pre_1180_; 
v_pre_1180_ = lean_ctor_get(v_declName_1179_, 0);
if (lean_obj_tag(v_pre_1180_) == 1)
{
lean_object* v_pre_1181_; 
v_pre_1181_ = lean_ctor_get(v_pre_1180_, 0);
if (lean_obj_tag(v_pre_1181_) == 0)
{
lean_object* v_str_1182_; lean_object* v_str_1183_; lean_object* v___x_1184_; uint8_t v___x_1185_; 
v_str_1182_ = lean_ctor_get(v_declName_1179_, 1);
v_str_1183_ = lean_ctor_get(v_pre_1180_, 1);
v___x_1184_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0));
v___x_1185_ = lean_string_dec_eq(v_str_1183_, v___x_1184_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; 
v___x_1186_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
return v___x_1186_;
}
else
{
lean_object* v___x_1187_; uint8_t v___x_1188_; 
v___x_1187_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__0));
v___x_1188_ = lean_string_dec_eq(v_str_1182_, v___x_1187_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; 
v___x_1189_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
return v___x_1189_;
}
else
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
lean_dec_ref(v_e_1159_);
v___x_1190_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__1));
v___x_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1190_);
return v___x_1191_;
}
}
}
else
{
lean_object* v___x_1192_; 
v___x_1192_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
return v___x_1192_;
}
}
else
{
lean_object* v___x_1193_; 
v___x_1193_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
return v___x_1193_;
}
}
else
{
lean_object* v___x_1194_; 
v___x_1194_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
return v___x_1194_;
}
}
case 5:
{
lean_object* v___x_1195_; 
v___x_1195_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit(v_e_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
return v___x_1195_;
}
case 2:
{
lean_object* v___x_1196_; 
v___x_1196_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit(v_e_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
return v___x_1196_;
}
default: 
{
lean_object* v___x_1197_; 
v___x_1197_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
return v___x_1197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___boxed(lean_object* v_e_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_e_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_);
lean_dec(v_a_1203_);
lean_dec_ref(v_a_1202_);
lean_dec(v_a_1201_);
lean_dec_ref(v_a_1200_);
lean_dec(v_a_1199_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___boxed(lean_object* v_e_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit(v_e_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
lean_dec(v_a_1211_);
lean_dec_ref(v_a_1210_);
lean_dec(v_a_1209_);
lean_dec_ref(v_a_1208_);
lean_dec(v_a_1207_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f(lean_object* v_e_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_){
_start:
{
lean_object* v___x_1252_; 
v___x_1252_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1245_, v_a_1248_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1592_; 
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1255_ = v___x_1252_;
v_isShared_1256_ = v_isSharedCheck_1592_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_dec(v___x_1252_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1592_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1262_; uint8_t v___x_1263_; 
v___x_1262_ = l_Lean_Expr_cleanupAnnotations(v_a_1253_);
v___x_1263_ = l_Lean_Expr_isApp(v___x_1262_);
if (v___x_1263_ == 0)
{
lean_dec_ref(v___x_1262_);
goto v___jp_1257_;
}
else
{
lean_object* v_arg_1264_; lean_object* v___x_1265_; uint8_t v___x_1266_; 
v_arg_1264_ = lean_ctor_get(v___x_1262_, 1);
lean_inc_ref(v_arg_1264_);
v___x_1265_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1262_);
v___x_1266_ = l_Lean_Expr_isApp(v___x_1265_);
if (v___x_1266_ == 0)
{
lean_dec_ref(v___x_1265_);
lean_dec_ref(v_arg_1264_);
goto v___jp_1257_;
}
else
{
lean_object* v_arg_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; 
v_arg_1267_ = lean_ctor_get(v___x_1265_, 1);
lean_inc_ref(v_arg_1267_);
v___x_1268_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1265_);
v___x_1269_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__1));
v___x_1270_ = l_Lean_Expr_isConstOf(v___x_1268_, v___x_1269_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1271_; uint8_t v___x_1272_; 
v___x_1271_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__3));
v___x_1272_ = l_Lean_Expr_isConstOf(v___x_1268_, v___x_1271_);
if (v___x_1272_ == 0)
{
uint8_t v___x_1273_; 
v___x_1273_ = l_Lean_Expr_isApp(v___x_1268_);
if (v___x_1273_ == 0)
{
lean_dec_ref(v___x_1268_);
lean_dec_ref(v_arg_1267_);
lean_dec_ref(v_arg_1264_);
goto v___jp_1257_;
}
else
{
lean_object* v_arg_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; uint8_t v___x_1277_; 
v_arg_1274_ = lean_ctor_get(v___x_1268_, 1);
lean_inc_ref(v_arg_1274_);
v___x_1275_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1268_);
v___x_1276_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__5));
v___x_1277_ = l_Lean_Expr_isConstOf(v___x_1275_, v___x_1276_);
if (v___x_1277_ == 0)
{
uint8_t v___x_1278_; 
v___x_1278_ = l_Lean_Expr_isApp(v___x_1275_);
if (v___x_1278_ == 0)
{
lean_dec_ref(v___x_1275_);
lean_dec_ref(v_arg_1274_);
lean_dec_ref(v_arg_1267_);
lean_dec_ref(v_arg_1264_);
goto v___jp_1257_;
}
else
{
lean_object* v___x_1279_; lean_object* v___x_1280_; uint8_t v___x_1281_; 
v___x_1279_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1275_);
v___x_1280_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__8));
v___x_1281_ = l_Lean_Expr_isConstOf(v___x_1279_, v___x_1280_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; uint8_t v___x_1283_; 
v___x_1282_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__11));
v___x_1283_ = l_Lean_Expr_isConstOf(v___x_1279_, v___x_1282_);
if (v___x_1283_ == 0)
{
lean_object* v___x_1284_; uint8_t v___x_1285_; 
v___x_1284_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__13));
v___x_1285_ = l_Lean_Expr_isConstOf(v___x_1279_, v___x_1284_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1286_; uint8_t v___x_1287_; 
v___x_1286_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__15));
v___x_1287_ = l_Lean_Expr_isConstOf(v___x_1279_, v___x_1286_);
lean_dec_ref(v___x_1279_);
if (v___x_1287_ == 0)
{
lean_dec_ref(v_arg_1274_);
lean_dec_ref(v_arg_1267_);
lean_dec_ref(v_arg_1264_);
goto v___jp_1257_;
}
else
{
lean_object* v___x_1288_; 
lean_del_object(v___x_1255_);
v___x_1288_ = l_Lean_Meta_DefEq_isInstLENat(v_arg_1274_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1327_; 
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1291_ = v___x_1288_;
v_isShared_1292_ = v_isSharedCheck_1327_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1288_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1327_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
uint8_t v___x_1293_; 
v___x_1293_ = lean_unbox(v_a_1289_);
lean_dec(v_a_1289_);
if (v___x_1293_ == 0)
{
lean_object* v___x_1294_; lean_object* v___x_1296_; 
lean_dec_ref(v_arg_1267_);
lean_dec_ref(v_arg_1264_);
v___x_1294_ = lean_box(0);
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 0, v___x_1294_);
v___x_1296_ = v___x_1291_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v___x_1294_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
else
{
lean_object* v___x_1298_; 
lean_del_object(v___x_1291_);
v___x_1298_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1267_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v_a_1299_; lean_object* v___x_1300_; 
v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
lean_inc(v_a_1299_);
lean_dec_ref(v___x_1298_);
v___x_1300_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1264_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1310_; 
v_a_1301_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1303_ = v___x_1300_;
v_isShared_1304_ = v_isSharedCheck_1310_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_dec(v___x_1300_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1310_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1308_; 
v___x_1305_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1305_, 0, v_a_1299_);
lean_ctor_set(v___x_1305_, 1, v_a_1301_);
lean_ctor_set_uint8(v___x_1305_, sizeof(void*)*2, v___x_1285_);
v___x_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1305_);
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 0, v___x_1306_);
v___x_1308_ = v___x_1303_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1306_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
else
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
lean_dec(v_a_1299_);
v_a_1311_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v___x_1300_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1300_);
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
lean_dec_ref(v_arg_1264_);
v_a_1319_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1298_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1298_);
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
}
}
else
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
lean_dec_ref(v_arg_1267_);
lean_dec_ref(v_arg_1264_);
v_a_1328_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1288_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1288_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
}
else
{
lean_object* v___x_1336_; 
lean_dec_ref(v___x_1279_);
lean_del_object(v___x_1255_);
v___x_1336_ = l_Lean_Meta_DefEq_isInstLTNat(v_arg_1274_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1376_; 
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1339_ = v___x_1336_;
v_isShared_1340_ = v_isSharedCheck_1376_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1336_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1376_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
uint8_t v___x_1341_; 
v___x_1341_ = lean_unbox(v_a_1337_);
lean_dec(v_a_1337_);
if (v___x_1341_ == 0)
{
lean_object* v___x_1342_; lean_object* v___x_1344_; 
lean_dec_ref(v_arg_1267_);
lean_dec_ref(v_arg_1264_);
v___x_1342_ = lean_box(0);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 0, v___x_1342_);
v___x_1344_ = v___x_1339_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1342_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
else
{
lean_object* v___x_1346_; 
lean_del_object(v___x_1339_);
v___x_1346_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1267_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v_a_1347_; lean_object* v___x_1348_; 
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
lean_inc(v_a_1347_);
lean_dec_ref(v___x_1346_);
v___x_1348_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1264_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1359_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1351_ = v___x_1348_;
v_isShared_1352_ = v_isSharedCheck_1359_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1348_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1359_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1357_; 
v___x_1353_ = l_Nat_Linear_Expr_inc(v_a_1347_);
v___x_1354_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1354_, 0, v___x_1353_);
lean_ctor_set(v___x_1354_, 1, v_a_1349_);
lean_ctor_set_uint8(v___x_1354_, sizeof(void*)*2, v___x_1283_);
v___x_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1354_);
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 0, v___x_1355_);
v___x_1357_ = v___x_1351_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v___x_1355_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
lean_dec(v_a_1347_);
v_a_1360_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1348_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1348_);
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
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
lean_dec_ref(v_arg_1264_);
v_a_1368_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1346_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1346_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
}
}
else
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
lean_dec_ref(v_arg_1267_);
lean_dec_ref(v_arg_1264_);
v_a_1377_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1379_ = v___x_1336_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1336_);
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
else
{
lean_object* v___x_1385_; 
lean_dec_ref(v___x_1279_);
lean_del_object(v___x_1255_);
v___x_1385_ = l_Lean_Meta_DefEq_isInstLENat(v_arg_1274_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1424_; 
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1388_ = v___x_1385_;
v_isShared_1389_ = v_isSharedCheck_1424_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1385_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1424_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
uint8_t v___x_1390_; 
v___x_1390_ = lean_unbox(v_a_1386_);
lean_dec(v_a_1386_);
if (v___x_1390_ == 0)
{
lean_object* v___x_1391_; lean_object* v___x_1393_; 
lean_dec_ref(v_arg_1267_);
lean_dec_ref(v_arg_1264_);
v___x_1391_ = lean_box(0);
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 0, v___x_1391_);
v___x_1393_ = v___x_1388_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1391_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
else
{
lean_object* v___x_1395_; 
lean_del_object(v___x_1388_);
v___x_1395_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1264_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_a_1396_; lean_object* v___x_1397_; 
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_a_1396_);
lean_dec_ref(v___x_1395_);
v___x_1397_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1267_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1407_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1400_ = v___x_1397_;
v_isShared_1401_ = v_isSharedCheck_1407_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1397_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1407_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1405_; 
v___x_1402_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1402_, 0, v_a_1396_);
lean_ctor_set(v___x_1402_, 1, v_a_1398_);
lean_ctor_set_uint8(v___x_1402_, sizeof(void*)*2, v___x_1281_);
v___x_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1402_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 0, v___x_1403_);
v___x_1405_ = v___x_1400_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1403_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
else
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
lean_dec(v_a_1396_);
v_a_1408_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1410_ = v___x_1397_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1397_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1408_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
else
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
lean_dec_ref(v_arg_1267_);
v_a_1416_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1418_ = v___x_1395_;
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1395_);
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
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
lean_dec_ref(v_arg_1267_);
lean_dec_ref(v_arg_1264_);
v_a_1425_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1385_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1385_);
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
else
{
lean_object* v___x_1433_; 
lean_dec_ref(v___x_1279_);
lean_del_object(v___x_1255_);
v___x_1433_ = l_Lean_Meta_DefEq_isInstLTNat(v_arg_1274_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1473_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1436_ = v___x_1433_;
v_isShared_1437_ = v_isSharedCheck_1473_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1433_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1473_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
uint8_t v___x_1438_; 
v___x_1438_ = lean_unbox(v_a_1434_);
lean_dec(v_a_1434_);
if (v___x_1438_ == 0)
{
lean_object* v___x_1439_; lean_object* v___x_1441_; 
lean_dec_ref(v_arg_1267_);
lean_dec_ref(v_arg_1264_);
v___x_1439_ = lean_box(0);
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 0, v___x_1439_);
v___x_1441_ = v___x_1436_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1439_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
else
{
lean_object* v___x_1443_; 
lean_del_object(v___x_1436_);
v___x_1443_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1264_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1443_) == 0)
{
lean_object* v_a_1444_; lean_object* v___x_1445_; 
v_a_1444_ = lean_ctor_get(v___x_1443_, 0);
lean_inc(v_a_1444_);
lean_dec_ref(v___x_1443_);
v___x_1445_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1267_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1456_; 
v_a_1446_ = lean_ctor_get(v___x_1445_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1448_ = v___x_1445_;
v_isShared_1449_ = v_isSharedCheck_1456_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1445_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1456_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1454_; 
v___x_1450_ = l_Nat_Linear_Expr_inc(v_a_1444_);
v___x_1451_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1451_, 0, v___x_1450_);
lean_ctor_set(v___x_1451_, 1, v_a_1446_);
lean_ctor_set_uint8(v___x_1451_, sizeof(void*)*2, v___x_1277_);
v___x_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1451_);
if (v_isShared_1449_ == 0)
{
lean_ctor_set(v___x_1448_, 0, v___x_1452_);
v___x_1454_ = v___x_1448_;
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
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
lean_dec(v_a_1444_);
v_a_1457_ = lean_ctor_get(v___x_1445_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1459_ = v___x_1445_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1445_);
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
else
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1472_; 
lean_dec_ref(v_arg_1267_);
v_a_1465_ = lean_ctor_get(v___x_1443_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1467_ = v___x_1443_;
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1443_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1468_ == 0)
{
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1465_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
}
}
else
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1481_; 
lean_dec_ref(v_arg_1267_);
lean_dec_ref(v_arg_1264_);
v_a_1474_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1476_ = v___x_1433_;
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1433_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1479_; 
if (v_isShared_1477_ == 0)
{
v___x_1479_ = v___x_1476_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_a_1474_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
}
}
}
else
{
lean_object* v___x_1482_; 
lean_dec_ref(v___x_1275_);
lean_del_object(v___x_1255_);
v___x_1482_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1274_, v_a_1248_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1523_; 
v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1523_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1523_ == 0)
{
v___x_1485_ = v___x_1482_;
v_isShared_1486_ = v_isSharedCheck_1523_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1482_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1523_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; uint8_t v___x_1489_; 
v___x_1487_ = l_Lean_Expr_cleanupAnnotations(v_a_1483_);
v___x_1488_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__16));
v___x_1489_ = l_Lean_Expr_isConstOf(v___x_1487_, v___x_1488_);
lean_dec_ref(v___x_1487_);
if (v___x_1489_ == 0)
{
lean_object* v___x_1490_; lean_object* v___x_1492_; 
lean_dec_ref(v_arg_1267_);
lean_dec_ref(v_arg_1264_);
v___x_1490_ = lean_box(0);
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 0, v___x_1490_);
v___x_1492_ = v___x_1485_;
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
else
{
lean_object* v___x_1494_; 
lean_del_object(v___x_1485_);
v___x_1494_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1267_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v_a_1495_; lean_object* v___x_1496_; 
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_a_1495_);
lean_dec_ref(v___x_1494_);
v___x_1496_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1264_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1506_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1499_ = v___x_1496_;
v_isShared_1500_ = v_isSharedCheck_1506_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1496_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1506_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1504_; 
v___x_1501_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1501_, 0, v_a_1495_);
lean_ctor_set(v___x_1501_, 1, v_a_1497_);
lean_ctor_set_uint8(v___x_1501_, sizeof(void*)*2, v___x_1489_);
v___x_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1502_, 0, v___x_1501_);
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 0, v___x_1502_);
v___x_1504_ = v___x_1499_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1502_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
else
{
lean_object* v_a_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1514_; 
lean_dec(v_a_1495_);
v_a_1507_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1509_ = v___x_1496_;
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_a_1507_);
lean_dec(v___x_1496_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1512_; 
if (v_isShared_1510_ == 0)
{
v___x_1512_ = v___x_1509_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_a_1507_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
}
else
{
lean_object* v_a_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1522_; 
lean_dec_ref(v_arg_1264_);
v_a_1515_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1517_ = v___x_1494_;
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_a_1515_);
lean_dec(v___x_1494_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1522_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v___x_1520_; 
if (v_isShared_1518_ == 0)
{
v___x_1520_ = v___x_1517_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_a_1515_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
}
}
}
else
{
lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1531_; 
lean_dec_ref(v_arg_1267_);
lean_dec_ref(v_arg_1264_);
v_a_1524_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1526_ = v___x_1482_;
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_dec(v___x_1482_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1529_; 
if (v_isShared_1527_ == 0)
{
v___x_1529_ = v___x_1526_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_a_1524_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
}
}
}
else
{
lean_object* v___x_1532_; 
lean_dec_ref(v___x_1268_);
lean_del_object(v___x_1255_);
v___x_1532_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1267_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v_a_1533_; lean_object* v___x_1534_; 
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_a_1533_);
lean_dec_ref(v___x_1532_);
v___x_1534_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1264_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1544_; 
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1537_ = v___x_1534_;
v_isShared_1538_ = v_isSharedCheck_1544_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v___x_1534_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1544_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1542_; 
v___x_1539_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1539_, 0, v_a_1533_);
lean_ctor_set(v___x_1539_, 1, v_a_1535_);
lean_ctor_set_uint8(v___x_1539_, sizeof(void*)*2, v___x_1270_);
v___x_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1539_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 0, v___x_1540_);
v___x_1542_ = v___x_1537_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1540_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
else
{
lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1552_; 
lean_dec(v_a_1533_);
v_a_1545_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1547_ = v___x_1534_;
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1534_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1550_; 
if (v_isShared_1548_ == 0)
{
v___x_1550_ = v___x_1547_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_a_1545_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
}
else
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
lean_dec_ref(v_arg_1264_);
v_a_1553_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1555_ = v___x_1532_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1532_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1556_ == 0)
{
v___x_1558_ = v___x_1555_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1553_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
}
else
{
lean_object* v___x_1561_; 
lean_dec_ref(v___x_1268_);
lean_del_object(v___x_1255_);
v___x_1561_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1267_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; lean_object* v___x_1563_; 
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
lean_inc(v_a_1562_);
lean_dec_ref(v___x_1561_);
v___x_1563_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1264_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1575_; 
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1566_ = v___x_1563_;
v_isShared_1567_ = v_isSharedCheck_1575_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1563_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1575_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
uint8_t v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1573_; 
v___x_1568_ = 0;
v___x_1569_ = l_Nat_Linear_Expr_inc(v_a_1562_);
v___x_1570_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1570_, 0, v___x_1569_);
lean_ctor_set(v___x_1570_, 1, v_a_1564_);
lean_ctor_set_uint8(v___x_1570_, sizeof(void*)*2, v___x_1568_);
v___x_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 0, v___x_1571_);
v___x_1573_ = v___x_1566_;
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
}
else
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
lean_dec(v_a_1562_);
v_a_1576_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1578_ = v___x_1563_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1563_);
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
else
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1591_; 
lean_dec_ref(v_arg_1264_);
v_a_1584_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1586_ = v___x_1561_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1561_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1584_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
}
}
v___jp_1257_:
{
lean_object* v___x_1258_; lean_object* v___x_1260_; 
v___x_1258_ = lean_box(0);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 0, v___x_1258_);
v___x_1260_ = v___x_1255_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1258_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
}
else
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
v_a_1593_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1252_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1252_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___boxed(lean_object* v_e_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f(v_e_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
lean_dec(v_a_1606_);
lean_dec_ref(v_a_1605_);
lean_dec(v_a_1604_);
lean_dec_ref(v_a_1603_);
lean_dec(v_a_1602_);
return v_res_1608_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1609_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1610_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__0, &l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__0_once, _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__0);
v___x_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1610_);
return v___x_1611_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__3(void){
_start:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1614_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__2));
v___x_1615_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__1, &l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__1_once, _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__1);
v___x_1616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1615_);
lean_ctor_set(v___x_1616_, 1, v___x_1614_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(lean_object* v_x_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_){
_start:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1623_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__3, &l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__3);
v___x_1624_ = lean_st_mk_ref(v___x_1623_);
lean_inc(v_a_1621_);
lean_inc_ref(v_a_1620_);
lean_inc(v_a_1619_);
lean_inc_ref(v_a_1618_);
lean_inc(v___x_1624_);
v___x_1625_ = lean_apply_6(v_x_1617_, v___x_1624_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_, lean_box(0));
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1643_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1628_ = v___x_1625_;
v_isShared_1629_ = v_isSharedCheck_1643_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1625_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1643_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1630_; lean_object* v_vars_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1641_; 
v___x_1630_ = lean_st_ref_get(v___x_1624_);
lean_dec(v___x_1624_);
v_vars_1631_ = lean_ctor_get(v___x_1630_, 1);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1641_ == 0)
{
lean_object* v_unused_1642_; 
v_unused_1642_ = lean_ctor_get(v___x_1630_, 0);
lean_dec(v_unused_1642_);
v___x_1633_ = v___x_1630_;
v_isShared_1634_ = v_isSharedCheck_1641_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_vars_1631_);
lean_dec(v___x_1630_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1641_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 0, v_a_1626_);
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_a_1626_);
lean_ctor_set(v_reuseFailAlloc_1640_, 1, v_vars_1631_);
v___x_1636_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
lean_object* v___x_1638_; 
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 0, v___x_1636_);
v___x_1638_ = v___x_1628_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1636_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
}
else
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1651_; 
lean_dec(v___x_1624_);
v_a_1644_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1651_ == 0)
{
v___x_1646_ = v___x_1625_;
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1625_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1651_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
if (v_isShared_1647_ == 0)
{
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1644_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___boxed(lean_object* v_x_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(v_x_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_);
lean_dec(v_a_1656_);
lean_dec_ref(v_a_1655_);
lean_dec(v_a_1654_);
lean_dec_ref(v_a_1653_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run(lean_object* v_00_u03b1_1659_, lean_object* v_x_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(v_x_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___boxed(lean_object* v_00_u03b1_1667_, lean_object* v_x_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run(v_00_u03b1_1667_, v_x_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_);
lean_dec(v_a_1672_);
lean_dec_ref(v_a_1671_);
lean_dec(v_a_1670_);
lean_dec_ref(v_a_1669_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearExpr(lean_object* v_e_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1681_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___boxed), 7, 1);
lean_closure_set(v___x_1681_, 0, v_e_1675_);
v___x_1682_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(v___x_1681_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_);
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_object* v_a_1683_; lean_object* v_fst_1684_; lean_object* v_snd_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; uint8_t v___x_1688_; 
v_a_1683_ = lean_ctor_get(v___x_1682_, 0);
lean_inc(v_a_1683_);
v_fst_1684_ = lean_ctor_get(v_a_1683_, 0);
lean_inc(v_fst_1684_);
v_snd_1685_ = lean_ctor_get(v_a_1683_, 1);
lean_inc(v_snd_1685_);
lean_dec(v_a_1683_);
v___x_1686_ = lean_array_get_size(v_snd_1685_);
v___x_1687_ = lean_unsigned_to_nat(1u);
v___x_1688_ = lean_nat_dec_eq(v___x_1686_, v___x_1687_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1707_; 
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1707_ == 0)
{
lean_object* v_unused_1708_; 
v_unused_1708_ = lean_ctor_get(v___x_1682_, 0);
lean_dec(v_unused_1708_);
v___x_1690_ = v___x_1682_;
v_isShared_1691_ = v_isSharedCheck_1707_;
goto v_resetjp_1689_;
}
else
{
lean_dec(v___x_1682_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1707_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
uint8_t v___x_1692_; lean_object* v___x_1693_; lean_object* v_fst_1694_; lean_object* v_snd_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1706_; 
v___x_1692_ = 1;
v___x_1693_ = l_Lean_sortExprs(v_snd_1685_, v___x_1692_);
lean_dec(v_snd_1685_);
v_fst_1694_ = lean_ctor_get(v___x_1693_, 0);
v_snd_1695_ = lean_ctor_get(v___x_1693_, 1);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1697_ = v___x_1693_;
v_isShared_1698_ = v_isSharedCheck_1706_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_snd_1695_);
lean_inc(v_fst_1694_);
lean_dec(v___x_1693_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1706_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1699_; lean_object* v___x_1701_; 
v___x_1699_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(v_snd_1695_, v_fst_1684_);
lean_dec(v_snd_1695_);
if (v_isShared_1698_ == 0)
{
lean_ctor_set(v___x_1697_, 1, v_fst_1694_);
lean_ctor_set(v___x_1697_, 0, v___x_1699_);
v___x_1701_ = v___x_1697_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1699_);
lean_ctor_set(v_reuseFailAlloc_1705_, 1, v_fst_1694_);
v___x_1701_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
lean_object* v___x_1703_; 
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 0, v___x_1701_);
v___x_1703_ = v___x_1690_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1701_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
}
}
else
{
lean_dec(v_snd_1685_);
lean_dec(v_fst_1684_);
return v___x_1682_;
}
}
else
{
return v___x_1682_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearExpr___boxed(lean_object* v_e_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_Lean_Meta_Simp_Arith_Nat_toLinearExpr(v_e_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_);
lean_dec(v_a_1713_);
lean_dec_ref(v_a_1712_);
lean_dec(v_a_1711_);
lean_dec_ref(v_a_1710_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearCnstr_x3f(lean_object* v_e_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_){
_start:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1722_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___boxed), 7, 1);
lean_closure_set(v___x_1722_, 0, v_e_1716_);
v___x_1723_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(v___x_1722_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1774_; 
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1726_ = v___x_1723_;
v_isShared_1727_ = v_isSharedCheck_1774_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1723_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1774_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v_fst_1728_; 
v_fst_1728_ = lean_ctor_get(v_a_1724_, 0);
lean_inc(v_fst_1728_);
if (lean_obj_tag(v_fst_1728_) == 1)
{
lean_object* v_snd_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1768_; 
v_snd_1729_ = lean_ctor_get(v_a_1724_, 1);
v_isSharedCheck_1768_ = !lean_is_exclusive(v_a_1724_);
if (v_isSharedCheck_1768_ == 0)
{
lean_object* v_unused_1769_; 
v_unused_1769_ = lean_ctor_get(v_a_1724_, 0);
lean_dec(v_unused_1769_);
v___x_1731_ = v_a_1724_;
v_isShared_1732_ = v_isSharedCheck_1768_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_snd_1729_);
lean_dec(v_a_1724_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1768_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v_val_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1767_; 
v_val_1733_ = lean_ctor_get(v_fst_1728_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v_fst_1728_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1735_ = v_fst_1728_;
v_isShared_1736_ = v_isSharedCheck_1767_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_val_1733_);
lean_dec(v_fst_1728_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1767_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; uint8_t v___x_1739_; 
v___x_1737_ = lean_array_get_size(v_snd_1729_);
v___x_1738_ = lean_unsigned_to_nat(1u);
v___x_1739_ = lean_nat_dec_le(v___x_1737_, v___x_1738_);
if (v___x_1739_ == 0)
{
uint8_t v___x_1740_; lean_object* v___x_1741_; lean_object* v_fst_1742_; lean_object* v_snd_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1757_; 
lean_del_object(v___x_1731_);
v___x_1740_ = 1;
v___x_1741_ = l_Lean_sortExprs(v_snd_1729_, v___x_1740_);
lean_dec(v_snd_1729_);
v_fst_1742_ = lean_ctor_get(v___x_1741_, 0);
v_snd_1743_ = lean_ctor_get(v___x_1741_, 1);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1745_ = v___x_1741_;
v_isShared_1746_ = v_isSharedCheck_1757_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_snd_1743_);
lean_inc(v_fst_1742_);
lean_dec(v___x_1741_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1757_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1747_; lean_object* v___x_1749_; 
v___x_1747_ = l_Nat_Linear_ExprCnstr_applyPerm(v_snd_1743_, v_val_1733_);
lean_dec(v_snd_1743_);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 1, v_fst_1742_);
lean_ctor_set(v___x_1745_, 0, v___x_1747_);
v___x_1749_ = v___x_1745_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v___x_1747_);
lean_ctor_set(v_reuseFailAlloc_1756_, 1, v_fst_1742_);
v___x_1749_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
lean_object* v___x_1751_; 
if (v_isShared_1736_ == 0)
{
lean_ctor_set(v___x_1735_, 0, v___x_1749_);
v___x_1751_ = v___x_1735_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v___x_1749_);
v___x_1751_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
lean_object* v___x_1753_; 
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 0, v___x_1751_);
v___x_1753_ = v___x_1726_;
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
}
}
}
else
{
lean_object* v___x_1759_; 
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 0, v_val_1733_);
v___x_1759_ = v___x_1731_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_val_1733_);
lean_ctor_set(v_reuseFailAlloc_1766_, 1, v_snd_1729_);
v___x_1759_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
lean_object* v___x_1761_; 
if (v_isShared_1736_ == 0)
{
lean_ctor_set(v___x_1735_, 0, v___x_1759_);
v___x_1761_ = v___x_1735_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1759_);
v___x_1761_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
lean_object* v___x_1763_; 
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 0, v___x_1761_);
v___x_1763_ = v___x_1726_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1761_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1770_; lean_object* v___x_1772_; 
lean_dec(v_fst_1728_);
lean_dec(v_a_1724_);
v___x_1770_ = lean_box(0);
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 0, v___x_1770_);
v___x_1772_ = v___x_1726_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v___x_1770_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
else
{
lean_object* v_a_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1782_; 
v_a_1775_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1777_ = v___x_1723_;
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_a_1775_);
lean_dec(v___x_1723_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1780_; 
if (v_isShared_1778_ == 0)
{
v___x_1780_ = v___x_1777_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_a_1775_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearCnstr_x3f___boxed(lean_object* v_e_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l_Lean_Meta_Simp_Arith_Nat_toLinearCnstr_x3f(v_e_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
lean_dec(v_a_1787_);
lean_dec_ref(v_a_1786_);
lean_dec(v_a_1785_);
lean_dec_ref(v_a_1784_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0(lean_object* v___y_1790_){
_start:
{
lean_inc_ref(v___y_1790_);
return v___y_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0___boxed(lean_object* v___y_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0(v___y_1791_);
lean_dec_ref(v___y_1791_);
return v_res_1792_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1(void){
_start:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1794_ = lean_box(0);
v___x_1795_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__16));
v___x_1796_ = l_Lean_mkConst(v___x_1795_, v___x_1794_);
return v___x_1796_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__2(void){
_start:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1797_ = lean_unsigned_to_nat(0u);
v___x_1798_ = l_Lean_mkNatLit(v___x_1797_);
return v___x_1798_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__3(void){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1799_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__2, &l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__2);
v___x_1800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1799_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr(lean_object* v_ctx_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_){
_start:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; uint8_t v___x_1809_; 
v___x_1807_ = lean_unsigned_to_nat(0u);
v___x_1808_ = lean_array_get_size(v_ctx_1801_);
v___x_1809_ = lean_nat_dec_lt(v___x_1807_, v___x_1808_);
if (v___x_1809_ == 0)
{
lean_object* v___f_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
lean_dec_ref(v_ctx_1801_);
v___f_1810_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__0));
v___x_1811_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1, &l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1_once, _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1);
v___x_1812_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__3, &l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__3);
v___x_1813_ = l_Lean_RArray_toExpr___redArg(v___x_1811_, v___f_1810_, v___x_1812_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_);
return v___x_1813_;
}
else
{
lean_object* v___f_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___f_1814_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__0));
v___x_1815_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1, &l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1_once, _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1);
v___x_1816_ = l_Lean_RArray_ofArray___redArg(v_ctx_1801_);
v___x_1817_ = l_Lean_RArray_toExpr___redArg(v___x_1815_, v___f_1814_, v___x_1816_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_);
return v___x_1817_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr___boxed(lean_object* v_ctx_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(v_ctx_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_);
lean_dec(v_a_1822_);
lean_dec_ref(v_a_1821_);
lean_dec(v_a_1820_);
lean_dec_ref(v_a_1819_);
return v_res_1824_;
}
}
lean_object* runtime_initialize_Lean_Util_SortExprs(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_KExprMap(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_RArray(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Offset(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
res = runtime_initialize_Init_Data_Nat_Linear(builtin);
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
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
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
res = initialize_Init_Data_Nat_Linear(builtin);
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
