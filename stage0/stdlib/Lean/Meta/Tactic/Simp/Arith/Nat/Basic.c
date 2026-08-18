// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Arith.Nat.Basic
// Imports: public import Lean.Util.SortExprs public import Lean.Meta.KExprMap import Lean.Data.RArray import Lean.Meta.NatInstTesters import Lean.Meta.Offset public import Init.Data.Nat.Internal.Linear
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
lean_object* l_Lean_mkNatLit(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatAdd(lean_object*, lean_object*);
lean_object* l_Lean_mkNatMul(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLE(lean_object*, lean_object*);
lean_object* l_Lean_mkNatEq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
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
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
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
lean_object* l_Lean_RArray_toExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RArray_ofArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_m_1_, lean_object* v_query_2_, lean_object* v_x_3_, lean_object* v_x_4_, lean_object* v_x_5_){
_start:
{
lean_object* v_zero_6_; uint8_t v_isZero_7_; 
v_zero_6_ = lean_unsigned_to_nat(0u);
v_isZero_7_ = lean_nat_dec_eq(v_x_4_, v_zero_6_);
if (v_isZero_7_ == 1)
{
lean_dec(v_x_5_);
lean_dec(v_x_4_);
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_8_; 
v___x_8_ = lean_box(2);
return v___x_8_;
}
else
{
lean_object* v_val_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_16_; 
v_val_9_ = lean_ctor_get(v_x_3_, 0);
v_isSharedCheck_16_ = !lean_is_exclusive(v_x_3_);
if (v_isSharedCheck_16_ == 0)
{
v___x_11_ = v_x_3_;
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_val_9_);
lean_dec(v_x_3_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
v_resetjp_10_:
{
lean_object* v___x_14_; 
if (v_isShared_12_ == 0)
{
v___x_14_ = v___x_11_;
goto v_reusejp_13_;
}
else
{
lean_object* v_reuseFailAlloc_15_; 
v_reuseFailAlloc_15_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_15_, 0, v_val_9_);
v___x_14_ = v_reuseFailAlloc_15_;
goto v_reusejp_13_;
}
v_reusejp_13_:
{
return v___x_14_;
}
}
}
}
else
{
lean_object* v_keyArray_17_; lean_object* v_valueArray_18_; lean_object* v___x_19_; uint8_t v_isSome_20_; 
v_keyArray_17_ = lean_ctor_get(v_m_1_, 1);
v_valueArray_18_ = lean_ctor_get(v_m_1_, 2);
v___x_19_ = lean_array_fget_borrowed(v_keyArray_17_, v_x_5_);
v_isSome_20_ = lean_noption_is_some(v___x_19_);
if (v_isSome_20_ == 0)
{
lean_dec(v_x_4_);
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_21_; 
v___x_21_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_21_, 0, v_x_5_);
return v___x_21_;
}
else
{
lean_object* v_val_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_29_; 
lean_dec(v_x_5_);
v_val_22_ = lean_ctor_get(v_x_3_, 0);
v_isSharedCheck_29_ = !lean_is_exclusive(v_x_3_);
if (v_isSharedCheck_29_ == 0)
{
v___x_24_ = v_x_3_;
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_val_22_);
lean_dec(v_x_3_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_27_; 
if (v_isShared_25_ == 0)
{
v___x_27_ = v___x_24_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_val_22_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
}
}
else
{
lean_object* v_one_30_; lean_object* v_n_31_; lean_object* v___y_33_; 
v_one_30_ = lean_unsigned_to_nat(1u);
v_n_31_ = lean_nat_sub(v_x_4_, v_one_30_);
lean_dec(v_x_4_);
if (v_isSome_20_ == 0)
{
goto v___jp_39_;
}
else
{
lean_object* v___x_41_; uint8_t v_isSome_42_; 
v___x_41_ = lean_array_fget_borrowed(v_valueArray_18_, v_x_5_);
v_isSome_42_ = lean_noption_is_some(v___x_41_);
if (v_isSome_42_ == 0)
{
goto v___jp_39_;
}
else
{
lean_object* v_val_43_; uint8_t v___x_44_; 
lean_inc(v___x_19_);
v_val_43_ = lean_noption_get(v___x_19_);
v___x_44_ = lean_nat_dec_eq(v_val_43_, v_query_2_);
if (v___x_44_ == 0)
{
lean_object* v___x_45_; lean_object* v___x_46_; uint8_t v___x_47_; 
lean_dec(v_val_43_);
v___x_45_ = lean_array_get_size(v_keyArray_17_);
v___x_46_ = lean_nat_add(v_x_5_, v_one_30_);
lean_dec(v_x_5_);
v___x_47_ = lean_nat_dec_lt(v___x_46_, v___x_45_);
if (v___x_47_ == 0)
{
lean_dec(v___x_46_);
v_x_4_ = v_n_31_;
v_x_5_ = v_zero_6_;
goto _start;
}
else
{
v_x_4_ = v_n_31_;
v_x_5_ = v___x_46_;
goto _start;
}
}
else
{
lean_object* v_val_50_; lean_object* v___x_51_; 
lean_dec(v_n_31_);
lean_dec(v_x_3_);
lean_inc(v___x_41_);
v_val_50_ = lean_noption_get(v___x_41_);
v___x_51_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_51_, 0, v_x_5_);
lean_ctor_set(v___x_51_, 1, v_val_43_);
lean_ctor_set(v___x_51_, 2, v_val_50_);
return v___x_51_;
}
}
}
v___jp_32_:
{
lean_object* v___x_34_; lean_object* v___x_35_; uint8_t v___x_36_; 
v___x_34_ = lean_array_get_size(v_keyArray_17_);
v___x_35_ = lean_nat_add(v_x_5_, v_one_30_);
lean_dec(v_x_5_);
v___x_36_ = lean_nat_dec_lt(v___x_35_, v___x_34_);
if (v___x_36_ == 0)
{
lean_dec(v___x_35_);
v_x_3_ = v___y_33_;
v_x_4_ = v_n_31_;
v_x_5_ = v_zero_6_;
goto _start;
}
else
{
v_x_3_ = v___y_33_;
v_x_4_ = v_n_31_;
v_x_5_ = v___x_35_;
goto _start;
}
}
v___jp_39_:
{
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_40_; 
lean_inc(v_x_5_);
v___x_40_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_40_, 0, v_x_5_);
v___y_33_ = v___x_40_;
goto v___jp_32_;
}
else
{
v___y_33_ = v_x_3_;
goto v___jp_32_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_m_52_, lean_object* v_query_53_, lean_object* v_x_54_, lean_object* v_x_55_, lean_object* v_x_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1_spec__2___redArg(v_m_52_, v_query_53_, v_x_54_, v_x_55_, v_x_56_);
lean_dec(v_query_53_);
lean_dec_ref(v_m_52_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1___redArg(lean_object* v_m_58_, lean_object* v_query_59_){
_start:
{
lean_object* v_keyArray_60_; lean_object* v___x_61_; uint64_t v___x_62_; uint64_t v___x_63_; uint64_t v___x_64_; uint64_t v_fold_65_; uint64_t v___x_66_; uint64_t v___x_67_; uint64_t v___x_68_; size_t v___x_69_; size_t v___x_70_; size_t v___x_71_; size_t v___x_72_; size_t v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v_keyArray_60_ = lean_ctor_get(v_m_58_, 1);
v___x_61_ = lean_array_get_size(v_keyArray_60_);
v___x_62_ = lean_uint64_of_nat(v_query_59_);
v___x_63_ = 32ULL;
v___x_64_ = lean_uint64_shift_right(v___x_62_, v___x_63_);
v_fold_65_ = lean_uint64_xor(v___x_62_, v___x_64_);
v___x_66_ = 16ULL;
v___x_67_ = lean_uint64_shift_right(v_fold_65_, v___x_66_);
v___x_68_ = lean_uint64_xor(v_fold_65_, v___x_67_);
v___x_69_ = lean_uint64_to_usize(v___x_68_);
v___x_70_ = lean_usize_of_nat(v___x_61_);
v___x_71_ = ((size_t)1ULL);
v___x_72_ = lean_usize_sub(v___x_70_, v___x_71_);
v___x_73_ = lean_usize_land(v___x_69_, v___x_72_);
v___x_74_ = lean_usize_to_nat(v___x_73_);
v___x_75_ = lean_box(0);
v___x_76_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1_spec__2___redArg(v_m_58_, v_query_59_, v___x_75_, v___x_61_, v___x_74_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_m_77_, lean_object* v_query_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1___redArg(v_m_77_, v_query_78_);
lean_dec(v_query_78_);
lean_dec_ref(v_m_77_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(lean_object* v_m_80_, lean_object* v_query_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1___redArg(v_m_80_, v_query_81_);
if (lean_obj_tag(v___x_82_) == 0)
{
lean_object* v_index_83_; lean_object* v_key_84_; lean_object* v_value_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_92_; 
v_index_83_ = lean_ctor_get(v___x_82_, 0);
v_key_84_ = lean_ctor_get(v___x_82_, 1);
v_value_85_ = lean_ctor_get(v___x_82_, 2);
v_isSharedCheck_92_ = !lean_is_exclusive(v___x_82_);
if (v_isSharedCheck_92_ == 0)
{
v___x_87_ = v___x_82_;
v_isShared_88_ = v_isSharedCheck_92_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_value_85_);
lean_inc(v_key_84_);
lean_inc(v_index_83_);
lean_dec(v___x_82_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_92_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_90_; 
if (v_isShared_88_ == 0)
{
v___x_90_ = v___x_87_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v_index_83_);
lean_ctor_set(v_reuseFailAlloc_91_, 1, v_key_84_);
lean_ctor_set(v_reuseFailAlloc_91_, 2, v_value_85_);
v___x_90_ = v_reuseFailAlloc_91_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
return v___x_90_;
}
}
}
else
{
lean_object* v___x_93_; 
lean_dec(v___x_82_);
v___x_93_ = lean_box(1);
return v___x_93_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg___boxed(lean_object* v_m_94_, lean_object* v_query_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(v_m_94_, v_query_95_);
lean_dec(v_query_95_);
lean_dec_ref(v_m_94_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0___redArg(lean_object* v_m_97_, lean_object* v_a_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(v_m_97_, v_a_98_);
if (lean_obj_tag(v___x_99_) == 0)
{
lean_object* v_value_100_; lean_object* v___x_101_; 
v_value_100_ = lean_ctor_get(v___x_99_, 2);
lean_inc(v_value_100_);
lean_dec_ref_known(v___x_99_, 3);
v___x_101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_101_, 0, v_value_100_);
return v___x_101_;
}
else
{
lean_object* v___x_102_; 
v___x_102_ = lean_box(0);
return v___x_102_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0___redArg___boxed(lean_object* v_m_103_, lean_object* v_a_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0___redArg(v_m_103_, v_a_104_);
lean_dec(v_a_104_);
lean_dec_ref(v_m_103_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go(lean_object* v_perm_106_, lean_object* v_a_107_){
_start:
{
switch(lean_obj_tag(v_a_107_))
{
case 0:
{
return v_a_107_;
}
case 1:
{
lean_object* v_i_108_; lean_object* v___x_109_; 
v_i_108_ = lean_ctor_get(v_a_107_, 0);
v___x_109_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0___redArg(v_perm_106_, v_i_108_);
if (lean_obj_tag(v___x_109_) == 0)
{
return v_a_107_;
}
else
{
lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_117_; 
v_isSharedCheck_117_ = !lean_is_exclusive(v_a_107_);
if (v_isSharedCheck_117_ == 0)
{
lean_object* v_unused_118_; 
v_unused_118_ = lean_ctor_get(v_a_107_, 0);
lean_dec(v_unused_118_);
v___x_111_ = v_a_107_;
v_isShared_112_ = v_isSharedCheck_117_;
goto v_resetjp_110_;
}
else
{
lean_dec(v_a_107_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_117_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v_val_113_; lean_object* v___x_115_; 
v_val_113_ = lean_ctor_get(v___x_109_, 0);
lean_inc(v_val_113_);
lean_dec_ref_known(v___x_109_, 1);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v_val_113_);
v___x_115_ = v___x_111_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_val_113_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
case 2:
{
lean_object* v_a_119_; lean_object* v_b_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_129_; 
v_a_119_ = lean_ctor_get(v_a_107_, 0);
v_b_120_ = lean_ctor_get(v_a_107_, 1);
v_isSharedCheck_129_ = !lean_is_exclusive(v_a_107_);
if (v_isSharedCheck_129_ == 0)
{
v___x_122_ = v_a_107_;
v_isShared_123_ = v_isSharedCheck_129_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_b_120_);
lean_inc(v_a_119_);
lean_dec(v_a_107_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_129_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_127_; 
v___x_124_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go(v_perm_106_, v_a_119_);
v___x_125_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go(v_perm_106_, v_b_120_);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 1, v___x_125_);
lean_ctor_set(v___x_122_, 0, v___x_124_);
v___x_127_ = v___x_122_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_124_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v___x_125_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
case 3:
{
lean_object* v_k_130_; lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_139_; 
v_k_130_ = lean_ctor_get(v_a_107_, 0);
v_a_131_ = lean_ctor_get(v_a_107_, 1);
v_isSharedCheck_139_ = !lean_is_exclusive(v_a_107_);
if (v_isSharedCheck_139_ == 0)
{
v___x_133_ = v_a_107_;
v_isShared_134_ = v_isSharedCheck_139_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_inc(v_k_130_);
lean_dec(v_a_107_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_139_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_135_; lean_object* v___x_137_; 
v___x_135_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go(v_perm_106_, v_a_131_);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 1, v___x_135_);
v___x_137_ = v___x_133_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_k_130_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v___x_135_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
default: 
{
lean_object* v_a_140_; lean_object* v_k_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_149_; 
v_a_140_ = lean_ctor_get(v_a_107_, 0);
v_k_141_ = lean_ctor_get(v_a_107_, 1);
v_isSharedCheck_149_ = !lean_is_exclusive(v_a_107_);
if (v_isSharedCheck_149_ == 0)
{
v___x_143_ = v_a_107_;
v_isShared_144_ = v_isSharedCheck_149_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_k_141_);
lean_inc(v_a_140_);
lean_dec(v_a_107_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_149_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_145_; lean_object* v___x_147_; 
v___x_145_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go(v_perm_106_, v_a_140_);
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 0, v___x_145_);
v___x_147_ = v___x_143_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_145_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v_k_141_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go___boxed(lean_object* v_perm_150_, lean_object* v_a_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go(v_perm_150_, v_a_151_);
lean_dec_ref(v_perm_150_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0(lean_object* v_00_u03b2_153_, lean_object* v_m_154_, lean_object* v_a_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0___redArg(v_m_154_, v_a_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0___boxed(lean_object* v_00_u03b2_157_, lean_object* v_m_158_, lean_object* v_a_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0(v_00_u03b2_157_, v_m_158_, v_a_159_);
lean_dec(v_a_159_);
lean_dec_ref(v_m_158_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0(lean_object* v_00_u03b2_161_, lean_object* v_m_162_, lean_object* v_query_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(v_m_162_, v_query_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_165_, lean_object* v_m_166_, lean_object* v_query_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0(v_00_u03b2_165_, v_m_166_, v_query_167_);
lean_dec(v_query_167_);
lean_dec_ref(v_m_166_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_169_, lean_object* v_m_170_, lean_object* v_query_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1___redArg(v_m_170_, v_query_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_173_, lean_object* v_m_174_, lean_object* v_query_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1(v_00_u03b2_173_, v_m_174_, v_query_175_);
lean_dec(v_query_175_);
lean_dec_ref(v_m_174_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_177_, lean_object* v_m_178_, lean_object* v_query_179_, lean_object* v_x_180_, lean_object* v_x_181_, lean_object* v_x_182_, lean_object* v_x_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1_spec__2___redArg(v_m_178_, v_query_179_, v_x_180_, v_x_181_, v_x_182_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_185_, lean_object* v_m_186_, lean_object* v_query_187_, lean_object* v_x_188_, lean_object* v_x_189_, lean_object* v_x_190_, lean_object* v_x_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_185_, v_m_186_, v_query_187_, v_x_188_, v_x_189_, v_x_190_, v_x_191_);
lean_dec(v_query_187_);
lean_dec_ref(v_m_186_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_applyPerm(lean_object* v_perm_193_, lean_object* v_e_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go(v_perm_193_, v_e_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_Expr_applyPerm___boxed(lean_object* v_perm_196_, lean_object* v_e_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Nat_Internal_Linear_Expr_applyPerm(v_perm_196_, v_e_197_);
lean_dec_ref(v_perm_196_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_ExprCnstr_applyPerm(lean_object* v_perm_199_, lean_object* v_x_200_){
_start:
{
uint8_t v_eq_201_; lean_object* v_lhs_202_; lean_object* v_rhs_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_212_; 
v_eq_201_ = lean_ctor_get_uint8(v_x_200_, sizeof(void*)*2);
v_lhs_202_ = lean_ctor_get(v_x_200_, 0);
v_rhs_203_ = lean_ctor_get(v_x_200_, 1);
v_isSharedCheck_212_ = !lean_is_exclusive(v_x_200_);
if (v_isSharedCheck_212_ == 0)
{
v___x_205_ = v_x_200_;
v_isShared_206_ = v_isSharedCheck_212_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_rhs_203_);
lean_inc(v_lhs_202_);
lean_dec(v_x_200_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_212_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_210_; 
v___x_207_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go(v_perm_199_, v_lhs_202_);
v___x_208_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go(v_perm_199_, v_rhs_203_);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 1, v___x_208_);
lean_ctor_set(v___x_205_, 0, v___x_207_);
v___x_210_ = v___x_205_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_207_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v___x_208_);
lean_ctor_set_uint8(v_reuseFailAlloc_211_, sizeof(void*)*2, v_eq_201_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_Internal_Linear_ExprCnstr_applyPerm___boxed(lean_object* v_perm_213_, lean_object* v_x_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Nat_Internal_Linear_ExprCnstr_applyPerm(v_perm_213_, v_x_214_);
lean_dec_ref(v_perm_213_);
return v_res_215_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = lean_unsigned_to_nat(2u);
v___x_223_ = lean_nat_to_int(v___x_222_);
return v___x_223_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = lean_unsigned_to_nat(1u);
v___x_225_ = lean_nat_to_int(v___x_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(lean_object* v_x_250_, lean_object* v_prec_251_){
_start:
{
switch(lean_obj_tag(v_x_250_))
{
case 0:
{
lean_object* v_v_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_272_; 
v_v_252_ = lean_ctor_get(v_x_250_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v_x_250_);
if (v_isSharedCheck_272_ == 0)
{
v___x_254_ = v_x_250_;
v_isShared_255_ = v_isSharedCheck_272_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_v_252_);
lean_dec(v_x_250_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_272_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___y_257_; lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_268_ = lean_unsigned_to_nat(1024u);
v___x_269_ = lean_nat_dec_le(v___x_268_, v_prec_251_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; 
v___x_270_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3, &l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3);
v___y_257_ = v___x_270_;
goto v___jp_256_;
}
else
{
lean_object* v___x_271_; 
v___x_271_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4, &l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4_once, _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4);
v___y_257_ = v___x_271_;
goto v___jp_256_;
}
v___jp_256_:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_261_; 
v___x_258_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__2));
v___x_259_ = l_Nat_reprFast(v_v_252_);
if (v_isShared_255_ == 0)
{
lean_ctor_set_tag(v___x_254_, 3);
lean_ctor_set(v___x_254_, 0, v___x_259_);
v___x_261_ = v___x_254_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_259_);
v___x_261_ = v_reuseFailAlloc_267_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_262_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_258_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
lean_inc(v___y_257_);
v___x_263_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_263_, 0, v___y_257_);
lean_ctor_set(v___x_263_, 1, v___x_262_);
v___x_264_ = 0;
v___x_265_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_265_, 0, v___x_263_);
lean_ctor_set_uint8(v___x_265_, sizeof(void*)*1, v___x_264_);
v___x_266_ = l_Repr_addAppParen(v___x_265_, v_prec_251_);
return v___x_266_;
}
}
}
}
case 1:
{
lean_object* v_i_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_293_; 
v_i_273_ = lean_ctor_get(v_x_250_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v_x_250_);
if (v_isSharedCheck_293_ == 0)
{
v___x_275_ = v_x_250_;
v_isShared_276_ = v_isSharedCheck_293_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_i_273_);
lean_dec(v_x_250_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_293_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___y_278_; lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_289_ = lean_unsigned_to_nat(1024u);
v___x_290_ = lean_nat_dec_le(v___x_289_, v_prec_251_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; 
v___x_291_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3, &l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3);
v___y_278_ = v___x_291_;
goto v___jp_277_;
}
else
{
lean_object* v___x_292_; 
v___x_292_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4, &l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4_once, _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4);
v___y_278_ = v___x_292_;
goto v___jp_277_;
}
v___jp_277_:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_279_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__7));
v___x_280_ = l_Nat_reprFast(v_i_273_);
if (v_isShared_276_ == 0)
{
lean_ctor_set_tag(v___x_275_, 3);
lean_ctor_set(v___x_275_, 0, v___x_280_);
v___x_282_ = v___x_275_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_280_);
v___x_282_ = v_reuseFailAlloc_288_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_283_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_279_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
lean_inc(v___y_278_);
v___x_284_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_284_, 0, v___y_278_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
v___x_285_ = 0;
v___x_286_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_286_, 0, v___x_284_);
lean_ctor_set_uint8(v___x_286_, sizeof(void*)*1, v___x_285_);
v___x_287_ = l_Repr_addAppParen(v___x_286_, v_prec_251_);
return v___x_287_;
}
}
}
}
case 2:
{
lean_object* v_a_294_; lean_object* v_b_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_318_; 
v_a_294_ = lean_ctor_get(v_x_250_, 0);
v_b_295_ = lean_ctor_get(v_x_250_, 1);
v_isSharedCheck_318_ = !lean_is_exclusive(v_x_250_);
if (v_isSharedCheck_318_ == 0)
{
v___x_297_ = v_x_250_;
v_isShared_298_ = v_isSharedCheck_318_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_b_295_);
lean_inc(v_a_294_);
lean_dec(v_x_250_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_318_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_299_; lean_object* v___y_301_; uint8_t v___x_315_; 
v___x_299_ = lean_unsigned_to_nat(1024u);
v___x_315_ = lean_nat_dec_le(v___x_299_, v_prec_251_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; 
v___x_316_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3, &l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3);
v___y_301_ = v___x_316_;
goto v___jp_300_;
}
else
{
lean_object* v___x_317_; 
v___x_317_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4, &l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4_once, _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4);
v___y_301_ = v___x_317_;
goto v___jp_300_;
}
v___jp_300_:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_306_; 
v___x_302_ = lean_box(1);
v___x_303_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__10));
v___x_304_ = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(v_a_294_, v___x_299_);
if (v_isShared_298_ == 0)
{
lean_ctor_set_tag(v___x_297_, 5);
lean_ctor_set(v___x_297_, 1, v___x_304_);
lean_ctor_set(v___x_297_, 0, v___x_303_);
v___x_306_ = v___x_297_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_303_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v___x_304_);
v___x_306_ = v_reuseFailAlloc_314_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; uint8_t v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_307_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
lean_ctor_set(v___x_307_, 1, v___x_302_);
v___x_308_ = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(v_b_295_, v___x_299_);
v___x_309_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_307_);
lean_ctor_set(v___x_309_, 1, v___x_308_);
lean_inc(v___y_301_);
v___x_310_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_310_, 0, v___y_301_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
v___x_311_ = 0;
v___x_312_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_312_, 0, v___x_310_);
lean_ctor_set_uint8(v___x_312_, sizeof(void*)*1, v___x_311_);
v___x_313_ = l_Repr_addAppParen(v___x_312_, v_prec_251_);
return v___x_313_;
}
}
}
}
case 3:
{
lean_object* v_k_319_; lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_344_; 
v_k_319_ = lean_ctor_get(v_x_250_, 0);
v_a_320_ = lean_ctor_get(v_x_250_, 1);
v_isSharedCheck_344_ = !lean_is_exclusive(v_x_250_);
if (v_isSharedCheck_344_ == 0)
{
v___x_322_ = v_x_250_;
v_isShared_323_ = v_isSharedCheck_344_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_inc(v_k_319_);
lean_dec(v_x_250_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_344_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_324_; lean_object* v___y_326_; uint8_t v___x_341_; 
v___x_324_ = lean_unsigned_to_nat(1024u);
v___x_341_ = lean_nat_dec_le(v___x_324_, v_prec_251_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; 
v___x_342_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3, &l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3);
v___y_326_ = v___x_342_;
goto v___jp_325_;
}
else
{
lean_object* v___x_343_; 
v___x_343_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4, &l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4_once, _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4);
v___y_326_ = v___x_343_;
goto v___jp_325_;
}
v___jp_325_:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_332_; 
v___x_327_ = lean_box(1);
v___x_328_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__13));
v___x_329_ = l_Nat_reprFast(v_k_319_);
v___x_330_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
if (v_isShared_323_ == 0)
{
lean_ctor_set_tag(v___x_322_, 5);
lean_ctor_set(v___x_322_, 1, v___x_330_);
lean_ctor_set(v___x_322_, 0, v___x_328_);
v___x_332_ = v___x_322_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_328_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v___x_330_);
v___x_332_ = v_reuseFailAlloc_340_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_333_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v___x_327_);
v___x_334_ = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(v_a_320_, v___x_324_);
v___x_335_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_333_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
lean_inc(v___y_326_);
v___x_336_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_336_, 0, v___y_326_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
v___x_337_ = 0;
v___x_338_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_338_, 0, v___x_336_);
lean_ctor_set_uint8(v___x_338_, sizeof(void*)*1, v___x_337_);
v___x_339_ = l_Repr_addAppParen(v___x_338_, v_prec_251_);
return v___x_339_;
}
}
}
}
default: 
{
lean_object* v_a_345_; lean_object* v_k_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_370_; 
v_a_345_ = lean_ctor_get(v_x_250_, 0);
v_k_346_ = lean_ctor_get(v_x_250_, 1);
v_isSharedCheck_370_ = !lean_is_exclusive(v_x_250_);
if (v_isSharedCheck_370_ == 0)
{
v___x_348_ = v_x_250_;
v_isShared_349_ = v_isSharedCheck_370_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_k_346_);
lean_inc(v_a_345_);
lean_dec(v_x_250_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_370_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_350_; lean_object* v___y_352_; uint8_t v___x_367_; 
v___x_350_ = lean_unsigned_to_nat(1024u);
v___x_367_ = lean_nat_dec_le(v___x_350_, v_prec_251_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; 
v___x_368_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3, &l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3);
v___y_352_ = v___x_368_;
goto v___jp_351_;
}
else
{
lean_object* v___x_369_; 
v___x_369_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4, &l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4_once, _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4);
v___y_352_ = v___x_369_;
goto v___jp_351_;
}
v___jp_351_:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_357_; 
v___x_353_ = lean_box(1);
v___x_354_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__16));
v___x_355_ = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(v_a_345_, v___x_350_);
if (v_isShared_349_ == 0)
{
lean_ctor_set_tag(v___x_348_, 5);
lean_ctor_set(v___x_348_, 1, v___x_355_);
lean_ctor_set(v___x_348_, 0, v___x_354_);
v___x_357_ = v___x_348_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_354_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v___x_355_);
v___x_357_ = v_reuseFailAlloc_366_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; uint8_t v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_358_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
lean_ctor_set(v___x_358_, 1, v___x_353_);
v___x_359_ = l_Nat_reprFast(v_k_346_);
v___x_360_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
v___x_361_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_358_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
lean_inc(v___y_352_);
v___x_362_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_362_, 0, v___y_352_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
v___x_363_ = 0;
v___x_364_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_364_, 0, v___x_362_);
lean_ctor_set_uint8(v___x_364_, sizeof(void*)*1, v___x_363_);
v___x_365_ = l_Repr_addAppParen(v___x_364_, v_prec_251_);
return v___x_365_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___boxed(lean_object* v_x_371_, lean_object* v_prec_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(v_x_371_, v_prec_372_);
lean_dec(v_prec_372_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr_spec__0(lean_object* v_a_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = lean_nat_to_int(v_a_376_);
return v___x_377_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = lean_unsigned_to_nat(6u);
v___x_392_ = lean_nat_to_int(v___x_391_);
return v___x_392_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = lean_unsigned_to_nat(7u);
v___x_400_ = lean_nat_to_int(v___x_399_);
return v___x_400_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__0));
v___x_406_ = lean_string_length(v___x_405_);
return v___x_406_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__16, &l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__16_once, _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__16);
v___x_408_ = lean_nat_to_int(v___x_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg(lean_object* v_x_413_){
_start:
{
uint8_t v_eq_414_; lean_object* v_lhs_415_; lean_object* v_rhs_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; uint8_t v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v_eq_414_ = lean_ctor_get_uint8(v_x_413_, sizeof(void*)*2);
v_lhs_415_ = lean_ctor_get(v_x_413_, 0);
lean_inc_ref(v_lhs_415_);
v_rhs_416_ = lean_ctor_get(v_x_413_, 1);
lean_inc_ref(v_rhs_416_);
lean_dec_ref(v_x_413_);
v___x_417_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__5));
v___x_418_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__6));
v___x_419_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7, &l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7_once, _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7);
v___x_420_ = lean_unsigned_to_nat(0u);
v___x_421_ = l_Bool_repr___redArg(v_eq_414_);
v___x_422_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_419_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
v___x_423_ = 0;
v___x_424_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_424_, 0, v___x_422_);
lean_ctor_set_uint8(v___x_424_, sizeof(void*)*1, v___x_423_);
v___x_425_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_418_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
v___x_426_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__9));
v___x_427_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_425_);
lean_ctor_set(v___x_427_, 1, v___x_426_);
v___x_428_ = lean_box(1);
v___x_429_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_427_);
lean_ctor_set(v___x_429_, 1, v___x_428_);
v___x_430_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__11));
v___x_431_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_429_);
lean_ctor_set(v___x_431_, 1, v___x_430_);
v___x_432_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
lean_ctor_set(v___x_432_, 1, v___x_417_);
v___x_433_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12, &l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12);
v___x_434_ = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(v_lhs_415_, v___x_420_);
v___x_435_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_435_, 0, v___x_433_);
lean_ctor_set(v___x_435_, 1, v___x_434_);
v___x_436_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_436_, 0, v___x_435_);
lean_ctor_set_uint8(v___x_436_, sizeof(void*)*1, v___x_423_);
v___x_437_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_437_, 0, v___x_432_);
lean_ctor_set(v___x_437_, 1, v___x_436_);
v___x_438_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
lean_ctor_set(v___x_438_, 1, v___x_426_);
v___x_439_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
lean_ctor_set(v___x_439_, 1, v___x_428_);
v___x_440_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__14));
v___x_441_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_439_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
v___x_442_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
lean_ctor_set(v___x_442_, 1, v___x_417_);
v___x_443_ = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(v_rhs_416_, v___x_420_);
v___x_444_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_433_);
lean_ctor_set(v___x_444_, 1, v___x_443_);
v___x_445_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_445_, 0, v___x_444_);
lean_ctor_set_uint8(v___x_445_, sizeof(void*)*1, v___x_423_);
v___x_446_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_446_, 0, v___x_442_);
lean_ctor_set(v___x_446_, 1, v___x_445_);
v___x_447_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17, &l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17);
v___x_448_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__18));
v___x_449_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
lean_ctor_set(v___x_449_, 1, v___x_446_);
v___x_450_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__19));
v___x_451_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_451_, 0, v___x_449_);
lean_ctor_set(v___x_451_, 1, v___x_450_);
v___x_452_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_452_, 0, v___x_447_);
lean_ctor_set(v___x_452_, 1, v___x_451_);
v___x_453_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_453_, 0, v___x_452_);
lean_ctor_set_uint8(v___x_453_, sizeof(void*)*1, v___x_423_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr(lean_object* v_x_454_, lean_object* v_prec_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg(v_x_454_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___boxed(lean_object* v_x_457_, lean_object* v_prec_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr(v_x_457_, v_prec_458_);
lean_dec(v_prec_458_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_462_, lean_object* v_x_463_, lean_object* v_x_464_){
_start:
{
if (lean_obj_tag(v_x_464_) == 0)
{
lean_dec(v_x_462_);
return v_x_463_;
}
else
{
lean_object* v_head_465_; lean_object* v_tail_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_475_; 
v_head_465_ = lean_ctor_get(v_x_464_, 0);
v_tail_466_ = lean_ctor_get(v_x_464_, 1);
v_isSharedCheck_475_ = !lean_is_exclusive(v_x_464_);
if (v_isSharedCheck_475_ == 0)
{
v___x_468_ = v_x_464_;
v_isShared_469_ = v_isSharedCheck_475_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_tail_466_);
lean_inc(v_head_465_);
lean_dec(v_x_464_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_475_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_471_; 
lean_inc(v_x_462_);
if (v_isShared_469_ == 0)
{
lean_ctor_set_tag(v___x_468_, 5);
lean_ctor_set(v___x_468_, 1, v_x_462_);
lean_ctor_set(v___x_468_, 0, v_x_463_);
v___x_471_ = v___x_468_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_x_463_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v_x_462_);
v___x_471_ = v_reuseFailAlloc_474_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_472_; 
v___x_472_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
lean_ctor_set(v___x_472_, 1, v_head_465_);
v_x_463_ = v___x_472_;
v_x_464_ = v_tail_466_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0_spec__1(lean_object* v_x_476_, lean_object* v_x_477_){
_start:
{
if (lean_obj_tag(v_x_476_) == 0)
{
lean_object* v___x_478_; 
lean_dec(v_x_477_);
v___x_478_ = lean_box(0);
return v___x_478_;
}
else
{
lean_object* v_tail_479_; 
v_tail_479_ = lean_ctor_get(v_x_476_, 1);
if (lean_obj_tag(v_tail_479_) == 0)
{
lean_object* v_head_480_; 
lean_dec(v_x_477_);
v_head_480_ = lean_ctor_get(v_x_476_, 0);
lean_inc(v_head_480_);
lean_dec_ref_known(v_x_476_, 2);
return v_head_480_;
}
else
{
lean_object* v_head_481_; lean_object* v___x_482_; 
lean_inc(v_tail_479_);
v_head_481_ = lean_ctor_get(v_x_476_, 0);
lean_inc(v_head_481_);
lean_dec_ref_known(v_x_476_, 2);
v___x_482_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0_spec__1_spec__2(v_x_477_, v_head_481_, v_tail_479_);
return v___x_482_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__0));
v___x_489_ = lean_string_length(v___x_488_);
return v___x_489_;
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__3, &l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__3_once, _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__3);
v___x_491_ = lean_nat_to_int(v___x_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg(lean_object* v_x_496_){
_start:
{
lean_object* v_fst_497_; lean_object* v_snd_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_522_; 
v_fst_497_ = lean_ctor_get(v_x_496_, 0);
v_snd_498_ = lean_ctor_get(v_x_496_, 1);
v_isSharedCheck_522_ = !lean_is_exclusive(v_x_496_);
if (v_isSharedCheck_522_ == 0)
{
v___x_500_ = v_x_496_;
v_isShared_501_ = v_isSharedCheck_522_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_snd_498_);
lean_inc(v_fst_497_);
lean_dec(v_x_496_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_522_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_502_ = l_Nat_reprFast(v_fst_497_);
v___x_503_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
v___x_504_ = lean_box(0);
if (v_isShared_501_ == 0)
{
lean_ctor_set_tag(v___x_500_, 1);
lean_ctor_set(v___x_500_, 1, v___x_504_);
lean_ctor_set(v___x_500_, 0, v___x_503_);
v___x_506_ = v___x_500_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_503_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v___x_504_);
v___x_506_ = v_reuseFailAlloc_521_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; uint8_t v___x_519_; lean_object* v___x_520_; 
v___x_507_ = l_Nat_reprFast(v_snd_498_);
v___x_508_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
v___x_509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
lean_ctor_set(v___x_509_, 1, v___x_506_);
v___x_510_ = l_List_reverse___redArg(v___x_509_);
v___x_511_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__1));
v___x_512_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0_spec__1(v___x_510_, v___x_511_);
v___x_513_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__4, &l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__4_once, _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__4);
v___x_514_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__5));
v___x_515_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
lean_ctor_set(v___x_515_, 1, v___x_512_);
v___x_516_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__6));
v___x_517_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_517_, 0, v___x_515_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
v___x_518_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_513_);
lean_ctor_set(v___x_518_, 1, v___x_517_);
v___x_519_ = 0;
v___x_520_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_520_, 0, v___x_518_);
lean_ctor_set_uint8(v___x_520_, sizeof(void*)*1, v___x_519_);
return v___x_520_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__1_spec__3_spec__5(lean_object* v_x_523_, lean_object* v_x_524_, lean_object* v_x_525_){
_start:
{
if (lean_obj_tag(v_x_525_) == 0)
{
lean_dec(v_x_523_);
return v_x_524_;
}
else
{
lean_object* v_head_526_; lean_object* v_tail_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_537_; 
v_head_526_ = lean_ctor_get(v_x_525_, 0);
v_tail_527_ = lean_ctor_get(v_x_525_, 1);
v_isSharedCheck_537_ = !lean_is_exclusive(v_x_525_);
if (v_isSharedCheck_537_ == 0)
{
v___x_529_ = v_x_525_;
v_isShared_530_ = v_isSharedCheck_537_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_tail_527_);
lean_inc(v_head_526_);
lean_dec(v_x_525_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_537_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
lean_inc(v_x_523_);
if (v_isShared_530_ == 0)
{
lean_ctor_set_tag(v___x_529_, 5);
lean_ctor_set(v___x_529_, 1, v_x_523_);
lean_ctor_set(v___x_529_, 0, v_x_524_);
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_x_524_);
lean_ctor_set(v_reuseFailAlloc_536_, 1, v_x_523_);
v___x_532_ = v_reuseFailAlloc_536_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg(v_head_526_);
v___x_534_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_532_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v_x_524_ = v___x_534_;
v_x_525_ = v_tail_527_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__1_spec__3(lean_object* v_x_538_, lean_object* v_x_539_, lean_object* v_x_540_){
_start:
{
if (lean_obj_tag(v_x_540_) == 0)
{
lean_dec(v_x_538_);
return v_x_539_;
}
else
{
lean_object* v_head_541_; lean_object* v_tail_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_552_; 
v_head_541_ = lean_ctor_get(v_x_540_, 0);
v_tail_542_ = lean_ctor_get(v_x_540_, 1);
v_isSharedCheck_552_ = !lean_is_exclusive(v_x_540_);
if (v_isSharedCheck_552_ == 0)
{
v___x_544_ = v_x_540_;
v_isShared_545_ = v_isSharedCheck_552_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_tail_542_);
lean_inc(v_head_541_);
lean_dec(v_x_540_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_552_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
lean_inc(v_x_538_);
if (v_isShared_545_ == 0)
{
lean_ctor_set_tag(v___x_544_, 5);
lean_ctor_set(v___x_544_, 1, v_x_538_);
lean_ctor_set(v___x_544_, 0, v_x_539_);
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_x_539_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v_x_538_);
v___x_547_ = v_reuseFailAlloc_551_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_548_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg(v_head_541_);
v___x_549_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_549_, 0, v___x_547_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
v___x_550_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__1_spec__3_spec__5(v_x_538_, v___x_549_, v_tail_542_);
return v___x_550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__1(lean_object* v_x_553_, lean_object* v_x_554_){
_start:
{
if (lean_obj_tag(v_x_553_) == 0)
{
lean_object* v___x_555_; 
lean_dec(v_x_554_);
v___x_555_ = lean_box(0);
return v___x_555_;
}
else
{
lean_object* v_tail_556_; 
v_tail_556_ = lean_ctor_get(v_x_553_, 1);
if (lean_obj_tag(v_tail_556_) == 0)
{
lean_object* v_head_557_; lean_object* v___x_558_; 
lean_dec(v_x_554_);
v_head_557_ = lean_ctor_get(v_x_553_, 0);
lean_inc(v_head_557_);
lean_dec_ref_known(v_x_553_, 2);
v___x_558_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg(v_head_557_);
return v___x_558_;
}
else
{
lean_object* v_head_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
lean_inc(v_tail_556_);
v_head_559_ = lean_ctor_get(v_x_553_, 0);
lean_inc(v_head_559_);
lean_dec_ref_known(v_x_553_, 2);
v___x_560_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg(v_head_559_);
v___x_561_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__1_spec__3(v_x_554_, v___x_560_, v_tail_556_);
return v___x_561_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = ((lean_object*)(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__2));
v___x_568_ = lean_string_length(v___x_567_);
return v___x_568_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = lean_obj_once(&l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__4, &l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__4_once, _init_l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__4);
v___x_570_ = lean_nat_to_int(v___x_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg(lean_object* v_a_575_){
_start:
{
if (lean_obj_tag(v_a_575_) == 0)
{
lean_object* v___x_576_; 
v___x_576_ = ((lean_object*)(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__1));
return v___x_576_;
}
else
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; uint8_t v___x_585_; lean_object* v___x_586_; 
v___x_577_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__1));
v___x_578_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__1(v_a_575_, v___x_577_);
v___x_579_ = lean_obj_once(&l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__5, &l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__5_once, _init_l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__5);
v___x_580_ = ((lean_object*)(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__6));
v___x_581_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
lean_ctor_set(v___x_581_, 1, v___x_578_);
v___x_582_ = ((lean_object*)(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__7));
v___x_583_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_581_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
v___x_584_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_579_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
v___x_585_ = 0;
v___x_586_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_586_, 0, v___x_584_);
lean_ctor_set_uint8(v___x_586_, sizeof(void*)*1, v___x_585_);
return v___x_586_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr___redArg(lean_object* v_x_587_){
_start:
{
uint8_t v_eq_588_; lean_object* v_lhs_589_; lean_object* v_rhs_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; uint8_t v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v_eq_588_ = lean_ctor_get_uint8(v_x_587_, sizeof(void*)*2);
v_lhs_589_ = lean_ctor_get(v_x_587_, 0);
lean_inc(v_lhs_589_);
v_rhs_590_ = lean_ctor_get(v_x_587_, 1);
lean_inc(v_rhs_590_);
lean_dec_ref(v_x_587_);
v___x_591_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__5));
v___x_592_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__6));
v___x_593_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7, &l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7_once, _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7);
v___x_594_ = l_Bool_repr___redArg(v_eq_588_);
v___x_595_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_593_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
v___x_596_ = 0;
v___x_597_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_597_, 0, v___x_595_);
lean_ctor_set_uint8(v___x_597_, sizeof(void*)*1, v___x_596_);
v___x_598_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_592_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
v___x_599_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__9));
v___x_600_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_598_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = lean_box(1);
v___x_602_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_600_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
v___x_603_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__11));
v___x_604_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_602_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
v___x_605_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
lean_ctor_set(v___x_605_, 1, v___x_591_);
v___x_606_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12, &l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12);
v___x_607_ = l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg(v_lhs_589_);
v___x_608_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_606_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
v___x_609_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_609_, 0, v___x_608_);
lean_ctor_set_uint8(v___x_609_, sizeof(void*)*1, v___x_596_);
v___x_610_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_605_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
v___x_611_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
lean_ctor_set(v___x_611_, 1, v___x_599_);
v___x_612_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
lean_ctor_set(v___x_612_, 1, v___x_601_);
v___x_613_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__14));
v___x_614_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_612_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
v___x_615_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
lean_ctor_set(v___x_615_, 1, v___x_591_);
v___x_616_ = l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg(v_rhs_590_);
v___x_617_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_606_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
v___x_618_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_618_, 0, v___x_617_);
lean_ctor_set_uint8(v___x_618_, sizeof(void*)*1, v___x_596_);
v___x_619_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_615_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
v___x_620_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17, &l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17);
v___x_621_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__18));
v___x_622_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
lean_ctor_set(v___x_622_, 1, v___x_619_);
v___x_623_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__19));
v___x_624_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_622_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
v___x_625_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_620_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
v___x_626_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_626_, 0, v___x_625_);
lean_ctor_set_uint8(v___x_626_, sizeof(void*)*1, v___x_596_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr(lean_object* v_x_627_, lean_object* v_prec_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr___redArg(v_x_627_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr___boxed(lean_object* v_x_630_, lean_object* v_prec_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr(v_x_630_, v_prec_631_);
lean_dec(v_prec_631_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0(lean_object* v_a_633_, lean_object* v_n_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg(v_a_633_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___boxed(lean_object* v_a_636_, lean_object* v_n_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0(v_a_636_, v_n_637_);
lean_dec(v_n_637_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0(lean_object* v_x_639_, lean_object* v_x_640_){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg(v_x_639_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___boxed(lean_object* v_x_642_, lean_object* v_x_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0(v_x_642_, v_x_643_);
lean_dec(v_x_643_);
return v_res_644_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__6(void){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_658_ = lean_box(0);
v___x_659_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__5));
v___x_660_ = l_Lean_mkConst(v___x_659_, v___x_658_);
return v___x_660_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__9(void){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_668_ = lean_box(0);
v___x_669_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__8));
v___x_670_ = l_Lean_mkConst(v___x_669_, v___x_668_);
return v___x_670_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__12(void){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_678_ = lean_box(0);
v___x_679_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__11));
v___x_680_ = l_Lean_mkConst(v___x_679_, v___x_678_);
return v___x_680_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__15(void){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_688_ = lean_box(0);
v___x_689_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__14));
v___x_690_ = l_Lean_mkConst(v___x_689_, v___x_688_);
return v___x_690_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__18(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_698_ = lean_box(0);
v___x_699_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__17));
v___x_700_ = l_Lean_mkConst(v___x_699_, v___x_698_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(lean_object* v_e_701_){
_start:
{
switch(lean_obj_tag(v_e_701_))
{
case 0:
{
lean_object* v_v_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v_v_702_ = lean_ctor_get(v_e_701_, 0);
lean_inc(v_v_702_);
lean_dec_ref_known(v_e_701_, 1);
v___x_703_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__6, &l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__6_once, _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__6);
v___x_704_ = l_Lean_mkNatLit(v_v_702_);
v___x_705_ = l_Lean_Expr_app___override(v___x_703_, v___x_704_);
return v___x_705_;
}
case 1:
{
lean_object* v_i_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v_i_706_ = lean_ctor_get(v_e_701_, 0);
lean_inc(v_i_706_);
lean_dec_ref_known(v_e_701_, 1);
v___x_707_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__9, &l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__9_once, _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__9);
v___x_708_ = l_Lean_mkNatLit(v_i_706_);
v___x_709_ = l_Lean_Expr_app___override(v___x_707_, v___x_708_);
return v___x_709_;
}
case 2:
{
lean_object* v_a_710_; lean_object* v_b_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v_a_710_ = lean_ctor_get(v_e_701_, 0);
lean_inc_ref(v_a_710_);
v_b_711_ = lean_ctor_get(v_e_701_, 1);
lean_inc_ref(v_b_711_);
lean_dec_ref_known(v_e_701_, 2);
v___x_712_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__12, &l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__12);
v___x_713_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v_a_710_);
v___x_714_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v_b_711_);
v___x_715_ = l_Lean_mkAppB(v___x_712_, v___x_713_, v___x_714_);
return v___x_715_;
}
case 3:
{
lean_object* v_k_716_; lean_object* v_a_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v_k_716_ = lean_ctor_get(v_e_701_, 0);
lean_inc(v_k_716_);
v_a_717_ = lean_ctor_get(v_e_701_, 1);
lean_inc_ref(v_a_717_);
lean_dec_ref_known(v_e_701_, 2);
v___x_718_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__15, &l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__15_once, _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__15);
v___x_719_ = l_Lean_mkNatLit(v_k_716_);
v___x_720_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v_a_717_);
v___x_721_ = l_Lean_mkAppB(v___x_718_, v___x_719_, v___x_720_);
return v___x_721_;
}
default: 
{
lean_object* v_a_722_; lean_object* v_k_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v_a_722_ = lean_ctor_get(v_e_701_, 0);
lean_inc_ref(v_a_722_);
v_k_723_ = lean_ctor_get(v_e_701_, 1);
lean_inc(v_k_723_);
lean_dec_ref_known(v_e_701_, 2);
v___x_724_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__18, &l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__18_once, _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__18);
v___x_725_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v_a_722_);
v___x_726_ = l_Lean_mkNatLit(v_k_723_);
v___x_727_ = l_Lean_mkAppB(v___x_724_, v___x_725_, v___x_726_);
return v___x_727_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__2(void){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_734_ = lean_box(0);
v___x_735_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1));
v___x_736_ = l_Lean_mkConst(v___x_735_, v___x_734_);
return v___x_736_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__3(void){
_start:
{
lean_object* v___x_737_; lean_object* v___f_738_; lean_object* v___x_739_; 
v___x_737_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__2, &l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__2);
v___f_738_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__0));
v___x_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_739_, 0, v___f_738_);
lean_ctor_set(v___x_739_, 1, v___x_737_);
return v___x_739_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr(void){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__3, &l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__3);
return v___x_740_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__3(void){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_749_ = lean_box(0);
v___x_750_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2));
v___x_751_ = l_Lean_mkConst(v___x_750_, v___x_749_);
return v___x_751_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__7(void){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_757_ = lean_box(0);
v___x_758_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__6));
v___x_759_ = l_Lean_mkConst(v___x_758_, v___x_757_);
return v___x_759_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__10(void){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_764_ = lean_box(0);
v___x_765_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__9));
v___x_766_ = l_Lean_mkConst(v___x_765_, v___x_764_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(lean_object* v_c_767_){
_start:
{
uint8_t v_eq_768_; lean_object* v_lhs_769_; lean_object* v_rhs_770_; lean_object* v___x_771_; lean_object* v___y_773_; 
v_eq_768_ = lean_ctor_get_uint8(v_c_767_, sizeof(void*)*2);
v_lhs_769_ = lean_ctor_get(v_c_767_, 0);
lean_inc_ref(v_lhs_769_);
v_rhs_770_ = lean_ctor_get(v_c_767_, 1);
lean_inc_ref(v_rhs_770_);
lean_dec_ref(v_c_767_);
v___x_771_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__3, &l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__3);
if (v_eq_768_ == 0)
{
lean_object* v___x_777_; 
v___x_777_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__7, &l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__7_once, _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__7);
v___y_773_ = v___x_777_;
goto v___jp_772_;
}
else
{
lean_object* v___x_778_; 
v___x_778_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__10, &l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__10_once, _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__10);
v___y_773_ = v___x_778_;
goto v___jp_772_;
}
v___jp_772_:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_774_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v_lhs_769_);
v___x_775_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v_rhs_770_);
lean_inc_ref(v___y_773_);
v___x_776_ = l_Lean_mkApp3(v___x_771_, v___y_773_, v___x_774_, v___x_775_);
return v___x_776_;
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__2(void){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_785_ = lean_box(0);
v___x_786_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1));
v___x_787_ = l_Lean_mkConst(v___x_786_, v___x_785_);
return v___x_787_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__3(void){
_start:
{
lean_object* v___x_788_; lean_object* v___f_789_; lean_object* v___x_790_; 
v___x_788_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__2, &l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__2);
v___f_789_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__0));
v___x_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_790_, 0, v___f_789_);
lean_ctor_set(v___x_790_, 1, v___x_788_);
return v___x_790_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr(void){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__3, &l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__3);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(lean_object* v_ctx_792_, lean_object* v_e_793_){
_start:
{
switch(lean_obj_tag(v_e_793_))
{
case 0:
{
lean_object* v_v_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_803_; 
v_v_795_ = lean_ctor_get(v_e_793_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v_e_793_);
if (v_isSharedCheck_803_ == 0)
{
v___x_797_ = v_e_793_;
v_isShared_798_ = v_isSharedCheck_803_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_v_795_);
lean_dec(v_e_793_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_803_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_799_; lean_object* v___x_801_; 
v___x_799_ = l_Lean_mkNatLit(v_v_795_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v___x_799_);
v___x_801_ = v___x_797_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v___x_799_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
case 1:
{
lean_object* v_i_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_813_; 
v_i_804_ = lean_ctor_get(v_e_793_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v_e_793_);
if (v_isSharedCheck_813_ == 0)
{
v___x_806_ = v_e_793_;
v_isShared_807_ = v_isSharedCheck_813_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_i_804_);
lean_dec(v_e_793_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_813_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_811_; 
v___x_808_ = l_Lean_instInhabitedExpr;
v___x_809_ = lean_array_get_borrowed(v___x_808_, v_ctx_792_, v_i_804_);
lean_dec(v_i_804_);
lean_inc(v___x_809_);
if (v_isShared_807_ == 0)
{
lean_ctor_set_tag(v___x_806_, 0);
lean_ctor_set(v___x_806_, 0, v___x_809_);
v___x_811_ = v___x_806_;
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
case 2:
{
lean_object* v_a_814_; lean_object* v_b_815_; lean_object* v___x_816_; lean_object* v_a_817_; lean_object* v___x_818_; lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_827_; 
v_a_814_ = lean_ctor_get(v_e_793_, 0);
lean_inc_ref(v_a_814_);
v_b_815_ = lean_ctor_get(v_e_793_, 1);
lean_inc_ref(v_b_815_);
lean_dec_ref_known(v_e_793_, 2);
v___x_816_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_ctx_792_, v_a_814_);
v_a_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_a_817_);
lean_dec_ref(v___x_816_);
v___x_818_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_ctx_792_, v_b_815_);
v_a_819_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_827_ == 0)
{
v___x_821_ = v___x_818_;
v_isShared_822_ = v_isSharedCheck_827_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_818_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_827_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_823_; lean_object* v___x_825_; 
v___x_823_ = l_Lean_mkNatAdd(v_a_817_, v_a_819_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v___x_823_);
v___x_825_ = v___x_821_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_823_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
case 3:
{
lean_object* v_k_828_; lean_object* v_a_829_; lean_object* v___x_830_; lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_840_; 
v_k_828_ = lean_ctor_get(v_e_793_, 0);
lean_inc(v_k_828_);
v_a_829_ = lean_ctor_get(v_e_793_, 1);
lean_inc_ref(v_a_829_);
lean_dec_ref_known(v_e_793_, 2);
v___x_830_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_ctx_792_, v_a_829_);
v_a_831_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_840_ == 0)
{
v___x_833_ = v___x_830_;
v_isShared_834_ = v_isSharedCheck_840_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_830_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_840_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_838_; 
v___x_835_ = l_Lean_mkNatLit(v_k_828_);
v___x_836_ = l_Lean_mkNatMul(v___x_835_, v_a_831_);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 0, v___x_836_);
v___x_838_ = v___x_833_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_836_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
default: 
{
lean_object* v_a_841_; lean_object* v_k_842_; lean_object* v___x_843_; lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_853_; 
v_a_841_ = lean_ctor_get(v_e_793_, 0);
lean_inc_ref(v_a_841_);
v_k_842_ = lean_ctor_get(v_e_793_, 1);
lean_inc(v_k_842_);
lean_dec_ref_known(v_e_793_, 2);
v___x_843_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_ctx_792_, v_a_841_);
v_a_844_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_853_ == 0)
{
v___x_846_ = v___x_843_;
v_isShared_847_ = v_isSharedCheck_853_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_843_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_853_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_851_; 
v___x_848_ = l_Lean_mkNatLit(v_k_842_);
v___x_849_ = l_Lean_mkNatMul(v_a_844_, v___x_848_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 0, v___x_849_);
v___x_851_ = v___x_846_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_849_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg___boxed(lean_object* v_ctx_854_, lean_object* v_e_855_, lean_object* v_a_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_ctx_854_, v_e_855_);
lean_dec_ref(v_ctx_854_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith(lean_object* v_ctx_858_, lean_object* v_e_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_ctx_858_, v_e_859_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___boxed(lean_object* v_ctx_866_, lean_object* v_e_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith(v_ctx_866_, v_e_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
lean_dec(v_a_871_);
lean_dec_ref(v_a_870_);
lean_dec(v_a_869_);
lean_dec_ref(v_a_868_);
lean_dec_ref(v_ctx_866_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(lean_object* v_ctx_874_, lean_object* v_c_875_){
_start:
{
uint8_t v_eq_877_; 
v_eq_877_ = lean_ctor_get_uint8(v_c_875_, sizeof(void*)*2);
if (v_eq_877_ == 0)
{
lean_object* v_lhs_878_; lean_object* v_rhs_879_; lean_object* v___x_880_; lean_object* v_a_881_; lean_object* v___x_882_; lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_891_; 
v_lhs_878_ = lean_ctor_get(v_c_875_, 0);
lean_inc_ref(v_lhs_878_);
v_rhs_879_ = lean_ctor_get(v_c_875_, 1);
lean_inc_ref(v_rhs_879_);
lean_dec_ref(v_c_875_);
v___x_880_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_ctx_874_, v_lhs_878_);
v_a_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_a_881_);
lean_dec_ref(v___x_880_);
v___x_882_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_ctx_874_, v_rhs_879_);
v_a_883_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_891_ == 0)
{
v___x_885_ = v___x_882_;
v_isShared_886_ = v_isSharedCheck_891_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_882_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_891_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_887_; lean_object* v___x_889_; 
v___x_887_ = l_Lean_mkNatLE(v_a_881_, v_a_883_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v___x_887_);
v___x_889_ = v___x_885_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_887_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
else
{
lean_object* v_lhs_892_; lean_object* v_rhs_893_; lean_object* v___x_894_; lean_object* v_a_895_; lean_object* v___x_896_; lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_905_; 
v_lhs_892_ = lean_ctor_get(v_c_875_, 0);
lean_inc_ref(v_lhs_892_);
v_rhs_893_ = lean_ctor_get(v_c_875_, 1);
lean_inc_ref(v_rhs_893_);
lean_dec_ref(v_c_875_);
v___x_894_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_ctx_874_, v_lhs_892_);
v_a_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_a_895_);
lean_dec_ref(v___x_894_);
v___x_896_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(v_ctx_874_, v_rhs_893_);
v_a_897_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_905_ == 0)
{
v___x_899_ = v___x_896_;
v_isShared_900_ = v_isSharedCheck_905_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_896_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_905_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_901_; lean_object* v___x_903_; 
v___x_901_ = l_Lean_mkNatEq(v_a_895_, v_a_897_);
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 0, v___x_901_);
v___x_903_ = v___x_899_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_901_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg___boxed(lean_object* v_ctx_906_, lean_object* v_c_907_, lean_object* v_a_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(v_ctx_906_, v_c_907_);
lean_dec_ref(v_ctx_906_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith(lean_object* v_ctx_910_, lean_object* v_c_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(v_ctx_910_, v_c_911_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___boxed(lean_object* v_ctx_918_, lean_object* v_c_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith(v_ctx_918_, v_c_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_);
lean_dec(v_a_923_);
lean_dec_ref(v_a_922_);
lean_dec(v_a_921_);
lean_dec_ref(v_a_920_);
lean_dec_ref(v_ctx_918_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(lean_object* v_e_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_){
_start:
{
lean_object* v___x_933_; lean_object* v_varMap_934_; lean_object* v___x_935_; 
v___x_933_ = lean_st_ref_get(v_a_927_);
v_varMap_934_ = lean_ctor_get(v___x_933_, 0);
lean_inc_ref(v_varMap_934_);
lean_dec(v___x_933_);
lean_inc_ref(v_e_926_);
v___x_935_ = l_Lean_Meta_KExprMap_find_x3f___redArg(v_varMap_934_, v_e_926_, v_a_928_, v_a_929_, v_a_930_, v_a_931_);
lean_dec_ref(v_varMap_934_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_984_; 
v_a_936_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_984_ == 0)
{
v___x_938_ = v___x_935_;
v_isShared_939_ = v_isSharedCheck_984_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_935_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_984_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
if (lean_obj_tag(v_a_936_) == 1)
{
lean_object* v_val_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_950_; 
lean_dec_ref(v_e_926_);
v_val_940_ = lean_ctor_get(v_a_936_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v_a_936_);
if (v_isSharedCheck_950_ == 0)
{
v___x_942_ = v_a_936_;
v_isShared_943_ = v_isSharedCheck_950_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_val_940_);
lean_dec(v_a_936_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_950_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_val_940_);
v___x_945_ = v_reuseFailAlloc_949_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
lean_object* v___x_947_; 
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 0, v___x_945_);
v___x_947_ = v___x_938_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_945_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
else
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v_vars_953_; lean_object* v_varMap_954_; lean_object* v_vars_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_983_; 
lean_del_object(v___x_938_);
lean_dec(v_a_936_);
v___x_951_ = lean_st_ref_get(v_a_927_);
v___x_952_ = lean_st_ref_get(v_a_927_);
v_vars_953_ = lean_ctor_get(v___x_951_, 1);
lean_inc_ref(v_vars_953_);
lean_dec(v___x_951_);
v_varMap_954_ = lean_ctor_get(v___x_952_, 0);
v_vars_955_ = lean_ctor_get(v___x_952_, 1);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_983_ == 0)
{
v___x_957_ = v___x_952_;
v_isShared_958_ = v_isSharedCheck_983_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_vars_955_);
lean_inc(v_varMap_954_);
lean_dec(v___x_952_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_983_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = lean_array_get_size(v_vars_953_);
lean_dec_ref(v_vars_953_);
lean_inc_ref(v_e_926_);
v___x_960_ = l_Lean_Meta_KExprMap_insert___redArg(v_varMap_954_, v_e_926_, v___x_959_, v_a_928_, v_a_929_, v_a_930_, v_a_931_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_974_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_974_ == 0)
{
v___x_963_ = v___x_960_;
v_isShared_964_ = v_isSharedCheck_974_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_960_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_974_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_965_; lean_object* v___x_967_; 
v___x_965_ = lean_array_push(v_vars_955_, v_e_926_);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 1, v___x_965_);
lean_ctor_set(v___x_957_, 0, v_a_961_);
v___x_967_ = v___x_957_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_961_);
lean_ctor_set(v_reuseFailAlloc_973_, 1, v___x_965_);
v___x_967_ = v_reuseFailAlloc_973_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_971_; 
v___x_968_ = lean_st_ref_swap(v_a_927_, v___x_967_);
lean_dec(v___x_968_);
v___x_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_969_, 0, v___x_959_);
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 0, v___x_969_);
v___x_971_ = v___x_963_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_969_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
else
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
lean_del_object(v___x_957_);
lean_dec_ref(v_vars_955_);
lean_dec_ref(v_e_926_);
v_a_975_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___x_960_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_960_);
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
}
}
}
else
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_992_; 
lean_dec_ref(v_e_926_);
v_a_985_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_992_ == 0)
{
v___x_987_ = v___x_935_;
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_935_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_985_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar___boxed(lean_object* v_e_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
lean_dec(v_a_998_);
lean_dec_ref(v_a_997_);
lean_dec(v_a_996_);
lean_dec_ref(v_a_995_);
lean_dec(v_a_994_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit(lean_object* v_e_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v___x_1045_; 
lean_inc_ref(v_e_1038_);
v___x_1045_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1038_, v_a_1041_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; lean_object* v___x_1047_; uint8_t v___x_1048_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_a_1046_);
lean_dec_ref_known(v___x_1045_, 1);
v___x_1047_ = l_Lean_Expr_cleanupAnnotations(v_a_1046_);
v___x_1048_ = l_Lean_Expr_isApp(v___x_1047_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; 
lean_dec_ref(v___x_1047_);
v___x_1049_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
return v___x_1049_;
}
else
{
lean_object* v_arg_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; uint8_t v___x_1053_; 
v_arg_1050_ = lean_ctor_get(v___x_1047_, 1);
lean_inc_ref(v_arg_1050_);
v___x_1051_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1047_);
v___x_1052_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__1));
v___x_1053_ = l_Lean_Expr_isConstOf(v___x_1051_, v___x_1052_);
if (v___x_1053_ == 0)
{
uint8_t v___x_1054_; 
v___x_1054_ = l_Lean_Expr_isApp(v___x_1051_);
if (v___x_1054_ == 0)
{
lean_object* v___x_1055_; 
lean_dec_ref(v___x_1051_);
lean_dec_ref(v_arg_1050_);
v___x_1055_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
return v___x_1055_;
}
else
{
lean_object* v_arg_1056_; lean_object* v_b_1058_; lean_object* v___y_1059_; lean_object* v___y_1060_; lean_object* v___y_1061_; lean_object* v___y_1062_; lean_object* v___y_1063_; lean_object* v___x_1107_; lean_object* v___x_1108_; uint8_t v___x_1109_; 
v_arg_1056_ = lean_ctor_get(v___x_1051_, 1);
lean_inc_ref(v_arg_1056_);
v___x_1107_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1051_);
v___x_1108_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__3));
v___x_1109_ = l_Lean_Expr_isConstOf(v___x_1107_, v___x_1108_);
if (v___x_1109_ == 0)
{
lean_object* v___x_1110_; uint8_t v___x_1111_; 
v___x_1110_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__4));
v___x_1111_ = l_Lean_Expr_isConstOf(v___x_1107_, v___x_1110_);
if (v___x_1111_ == 0)
{
uint8_t v___x_1112_; 
v___x_1112_ = l_Lean_Expr_isApp(v___x_1107_);
if (v___x_1112_ == 0)
{
lean_object* v___x_1113_; 
lean_dec_ref(v___x_1107_);
lean_dec_ref(v_arg_1056_);
lean_dec_ref(v_arg_1050_);
v___x_1113_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
return v___x_1113_;
}
else
{
lean_object* v_arg_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; uint8_t v___x_1117_; 
v_arg_1114_ = lean_ctor_get(v___x_1107_, 1);
lean_inc_ref(v_arg_1114_);
v___x_1115_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1107_);
v___x_1116_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__7));
v___x_1117_ = l_Lean_Expr_isConstOf(v___x_1115_, v___x_1116_);
if (v___x_1117_ == 0)
{
uint8_t v___x_1118_; 
v___x_1118_ = l_Lean_Expr_isApp(v___x_1115_);
if (v___x_1118_ == 0)
{
lean_object* v___x_1119_; 
lean_dec_ref(v___x_1115_);
lean_dec_ref(v_arg_1114_);
lean_dec_ref(v_arg_1056_);
lean_dec_ref(v_arg_1050_);
v___x_1119_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
return v___x_1119_;
}
else
{
lean_object* v___x_1120_; lean_object* v___x_1121_; uint8_t v___x_1122_; 
v___x_1120_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1115_);
v___x_1121_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__9));
v___x_1122_ = l_Lean_Expr_isConstOf(v___x_1120_, v___x_1121_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1123_; uint8_t v___x_1124_; 
v___x_1123_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__11));
v___x_1124_ = l_Lean_Expr_isConstOf(v___x_1120_, v___x_1123_);
if (v___x_1124_ == 0)
{
uint8_t v___x_1125_; 
v___x_1125_ = l_Lean_Expr_isApp(v___x_1120_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; 
lean_dec_ref(v___x_1120_);
lean_dec_ref(v_arg_1114_);
lean_dec_ref(v_arg_1056_);
lean_dec_ref(v_arg_1050_);
v___x_1126_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
return v___x_1126_;
}
else
{
lean_object* v___x_1127_; uint8_t v___x_1128_; 
v___x_1127_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1120_);
v___x_1128_ = l_Lean_Expr_isApp(v___x_1127_);
if (v___x_1128_ == 0)
{
lean_object* v___x_1129_; 
lean_dec_ref(v___x_1127_);
lean_dec_ref(v_arg_1114_);
lean_dec_ref(v_arg_1056_);
lean_dec_ref(v_arg_1050_);
v___x_1129_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
return v___x_1129_;
}
else
{
lean_object* v___x_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; 
v___x_1130_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1127_);
v___x_1131_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__14));
v___x_1132_ = l_Lean_Expr_isConstOf(v___x_1130_, v___x_1131_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1133_; uint8_t v___x_1134_; 
v___x_1133_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__17));
v___x_1134_ = l_Lean_Expr_isConstOf(v___x_1130_, v___x_1133_);
lean_dec_ref(v___x_1130_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; 
lean_dec_ref(v_arg_1114_);
lean_dec_ref(v_arg_1056_);
lean_dec_ref(v_arg_1050_);
v___x_1135_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
return v___x_1135_;
}
else
{
lean_object* v___x_1136_; 
v___x_1136_ = l_Lean_Meta_DefEq_isInstHAddNat(v_arg_1114_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v_a_1137_; uint8_t v___x_1138_; 
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
lean_inc(v_a_1137_);
lean_dec_ref_known(v___x_1136_, 1);
v___x_1138_ = lean_unbox(v_a_1137_);
lean_dec(v_a_1137_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1139_; 
lean_dec_ref(v_arg_1056_);
lean_dec_ref(v_arg_1050_);
v___x_1139_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
return v___x_1139_;
}
else
{
lean_object* v___x_1140_; 
lean_dec_ref(v_e_1038_);
v___x_1140_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1056_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v_a_1141_; lean_object* v___x_1142_; 
v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
lean_inc(v_a_1141_);
lean_dec_ref_known(v___x_1140_, 1);
v___x_1142_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1050_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1151_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1145_ = v___x_1142_;
v_isShared_1146_ = v_isSharedCheck_1151_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1142_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1151_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; lean_object* v___x_1149_; 
v___x_1147_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1147_, 0, v_a_1141_);
lean_ctor_set(v___x_1147_, 1, v_a_1143_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v___x_1147_);
v___x_1149_ = v___x_1145_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v___x_1147_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
else
{
lean_dec(v_a_1141_);
return v___x_1142_;
}
}
else
{
lean_dec_ref(v_arg_1050_);
return v___x_1140_;
}
}
}
else
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
lean_dec_ref(v_arg_1056_);
lean_dec_ref(v_arg_1050_);
lean_dec_ref(v_e_1038_);
v_a_1152_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_1136_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1136_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1152_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
}
else
{
lean_object* v___x_1160_; 
lean_dec_ref(v___x_1130_);
v___x_1160_ = l_Lean_Meta_DefEq_isInstHMulNat(v_arg_1114_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v_a_1161_; uint8_t v___x_1162_; 
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
lean_inc(v_a_1161_);
lean_dec_ref_known(v___x_1160_, 1);
v___x_1162_ = lean_unbox(v_a_1161_);
lean_dec(v_a_1161_);
if (v___x_1162_ == 0)
{
lean_object* v___x_1163_; 
lean_dec_ref(v_arg_1056_);
lean_dec_ref(v_arg_1050_);
v___x_1163_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
return v___x_1163_;
}
else
{
v_b_1058_ = v_arg_1050_;
v___y_1059_ = v_a_1039_;
v___y_1060_ = v_a_1040_;
v___y_1061_ = v_a_1041_;
v___y_1062_ = v_a_1042_;
v___y_1063_ = v_a_1043_;
goto v___jp_1057_;
}
}
else
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1171_; 
lean_dec_ref(v_arg_1056_);
lean_dec_ref(v_arg_1050_);
lean_dec_ref(v_e_1038_);
v_a_1164_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1166_ = v___x_1160_;
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1160_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1169_; 
if (v_isShared_1167_ == 0)
{
v___x_1169_ = v___x_1166_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1164_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1172_; 
lean_dec_ref(v___x_1120_);
v___x_1172_ = l_Lean_Meta_DefEq_isInstAddNat(v_arg_1114_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; uint8_t v___x_1174_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_a_1173_);
lean_dec_ref_known(v___x_1172_, 1);
v___x_1174_ = lean_unbox(v_a_1173_);
lean_dec(v_a_1173_);
if (v___x_1174_ == 0)
{
lean_object* v___x_1175_; 
lean_dec_ref(v_arg_1056_);
lean_dec_ref(v_arg_1050_);
v___x_1175_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
return v___x_1175_;
}
else
{
lean_object* v___x_1176_; 
lean_dec_ref(v_e_1038_);
v___x_1176_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1056_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1177_; lean_object* v___x_1178_; 
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_a_1177_);
lean_dec_ref_known(v___x_1176_, 1);
v___x_1178_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1050_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1187_; 
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1181_ = v___x_1178_;
v_isShared_1182_ = v_isSharedCheck_1187_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1178_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1187_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1183_; lean_object* v___x_1185_; 
v___x_1183_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1183_, 0, v_a_1177_);
lean_ctor_set(v___x_1183_, 1, v_a_1179_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 0, v___x_1183_);
v___x_1185_ = v___x_1181_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1183_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
else
{
lean_dec(v_a_1177_);
return v___x_1178_;
}
}
else
{
lean_dec_ref(v_arg_1050_);
return v___x_1176_;
}
}
}
else
{
lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1195_; 
lean_dec_ref(v_arg_1056_);
lean_dec_ref(v_arg_1050_);
lean_dec_ref(v_e_1038_);
v_a_1188_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1190_ = v___x_1172_;
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___x_1172_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1193_; 
if (v_isShared_1191_ == 0)
{
v___x_1193_ = v___x_1190_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1188_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
}
else
{
lean_object* v___x_1196_; 
lean_dec_ref(v___x_1120_);
v___x_1196_ = l_Lean_Meta_DefEq_isInstMulNat(v_arg_1114_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v_a_1197_; uint8_t v___x_1198_; 
v_a_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc(v_a_1197_);
lean_dec_ref_known(v___x_1196_, 1);
v___x_1198_ = lean_unbox(v_a_1197_);
lean_dec(v_a_1197_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; 
lean_dec_ref(v_arg_1056_);
lean_dec_ref(v_arg_1050_);
v___x_1199_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
return v___x_1199_;
}
else
{
v_b_1058_ = v_arg_1050_;
v___y_1059_ = v_a_1039_;
v___y_1060_ = v_a_1040_;
v___y_1061_ = v_a_1041_;
v___y_1062_ = v_a_1042_;
v___y_1063_ = v_a_1043_;
goto v___jp_1057_;
}
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
lean_dec_ref(v_arg_1056_);
lean_dec_ref(v_arg_1050_);
lean_dec_ref(v_e_1038_);
v_a_1200_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1196_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1196_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1200_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
}
}
else
{
lean_object* v___x_1208_; 
lean_dec_ref(v___x_1115_);
lean_dec_ref(v_arg_1114_);
lean_inc_ref(v_arg_1050_);
v___x_1208_ = l_Lean_Meta_Structural_isInstOfNatNat___redArg(v_arg_1050_, v_a_1041_);
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_object* v_a_1209_; uint8_t v___x_1210_; 
v_a_1209_ = lean_ctor_get(v___x_1208_, 0);
lean_inc(v_a_1209_);
lean_dec_ref_known(v___x_1208_, 1);
v___x_1210_ = lean_unbox(v_a_1209_);
lean_dec(v_a_1209_);
if (v___x_1210_ == 0)
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
lean_inc_ref(v_arg_1056_);
v___x_1211_ = l_Lean_mkInstOfNatNat(v_arg_1056_);
v___x_1212_ = l_Lean_Meta_isDefEqI(v_arg_1050_, v___x_1211_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v_a_1213_; uint8_t v___x_1214_; 
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_a_1213_);
lean_dec_ref_known(v___x_1212_, 1);
v___x_1214_ = lean_unbox(v_a_1213_);
lean_dec(v_a_1213_);
if (v___x_1214_ == 0)
{
lean_object* v___x_1215_; 
lean_dec_ref(v_arg_1056_);
v___x_1215_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
return v___x_1215_;
}
else
{
lean_object* v___x_1216_; 
lean_dec_ref(v_e_1038_);
v___x_1216_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1056_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
return v___x_1216_;
}
}
else
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1224_; 
lean_dec_ref(v_arg_1056_);
lean_dec_ref(v_e_1038_);
v_a_1217_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1219_ = v___x_1212_;
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1212_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1220_ == 0)
{
v___x_1222_ = v___x_1219_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1217_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
else
{
lean_object* v___x_1225_; 
lean_dec_ref(v_arg_1050_);
lean_dec_ref(v_e_1038_);
v___x_1225_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1056_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
return v___x_1225_;
}
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
lean_dec_ref(v_arg_1056_);
lean_dec_ref(v_arg_1050_);
lean_dec_ref(v_e_1038_);
v_a_1226_ = lean_ctor_get(v___x_1208_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_1208_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1208_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
}
}
else
{
lean_object* v___x_1234_; 
lean_dec_ref(v___x_1107_);
lean_dec_ref(v_e_1038_);
v___x_1234_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1056_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_a_1235_; lean_object* v___x_1236_; 
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_a_1235_);
lean_dec_ref_known(v___x_1234_, 1);
v___x_1236_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1050_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1245_; 
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1239_ = v___x_1236_;
v_isShared_1240_ = v_isSharedCheck_1245_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1236_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1245_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1241_; lean_object* v___x_1243_; 
v___x_1241_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1241_, 0, v_a_1235_);
lean_ctor_set(v___x_1241_, 1, v_a_1237_);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 0, v___x_1241_);
v___x_1243_ = v___x_1239_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1241_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
else
{
lean_dec(v_a_1235_);
return v___x_1236_;
}
}
else
{
lean_dec_ref(v_arg_1050_);
return v___x_1234_;
}
}
}
else
{
lean_dec_ref(v___x_1107_);
v_b_1058_ = v_arg_1050_;
v___y_1059_ = v_a_1039_;
v___y_1060_ = v_a_1040_;
v___y_1061_ = v_a_1041_;
v___y_1062_ = v_a_1042_;
v___y_1063_ = v_a_1043_;
goto v___jp_1057_;
}
v___jp_1057_:
{
lean_object* v___x_1064_; 
lean_inc_ref(v_arg_1056_);
v___x_1064_ = l_Lean_Meta_evalNat(v_arg_1056_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc(v_a_1065_);
lean_dec_ref_known(v___x_1064_, 1);
if (lean_obj_tag(v_a_1065_) == 0)
{
lean_object* v___x_1066_; 
v___x_1066_ = l_Lean_Meta_evalNat(v_b_1058_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_a_1067_);
lean_dec_ref_known(v___x_1066_, 1);
if (lean_obj_tag(v_a_1067_) == 0)
{
lean_object* v___x_1068_; 
lean_dec_ref(v_arg_1056_);
v___x_1068_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_1038_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
return v___x_1068_;
}
else
{
lean_object* v_val_1069_; lean_object* v___x_1070_; 
lean_dec_ref(v_e_1038_);
v_val_1069_ = lean_ctor_get(v_a_1067_, 0);
lean_inc(v_val_1069_);
lean_dec_ref_known(v_a_1067_, 1);
v___x_1070_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1056_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1079_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1073_ = v___x_1070_;
v_isShared_1074_ = v_isSharedCheck_1079_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1070_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1079_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1075_; lean_object* v___x_1077_; 
v___x_1075_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1075_, 0, v_a_1071_);
lean_ctor_set(v___x_1075_, 1, v_val_1069_);
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 0, v___x_1075_);
v___x_1077_ = v___x_1073_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1075_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
else
{
lean_dec(v_val_1069_);
return v___x_1070_;
}
}
}
else
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
lean_dec_ref(v_arg_1056_);
lean_dec_ref(v_e_1038_);
v_a_1080_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_1066_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1066_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
else
{
lean_object* v_val_1088_; lean_object* v___x_1089_; 
lean_dec_ref(v_arg_1056_);
lean_dec_ref(v_e_1038_);
v_val_1088_ = lean_ctor_get(v_a_1065_, 0);
lean_inc(v_val_1088_);
lean_dec_ref_known(v_a_1065_, 1);
v___x_1089_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_b_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1098_; 
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1092_ = v___x_1089_;
v_isShared_1093_ = v_isSharedCheck_1098_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1089_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1098_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1094_; lean_object* v___x_1096_; 
v___x_1094_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1094_, 0, v_val_1088_);
lean_ctor_set(v___x_1094_, 1, v_a_1090_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v___x_1094_);
v___x_1096_ = v___x_1092_;
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
else
{
lean_dec(v_val_1088_);
return v___x_1089_;
}
}
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
lean_dec_ref(v_b_1058_);
lean_dec_ref(v_arg_1056_);
lean_dec_ref(v_e_1038_);
v_a_1099_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_1064_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1064_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
}
}
else
{
lean_object* v___x_1246_; 
lean_dec_ref(v___x_1051_);
lean_dec_ref(v_e_1038_);
v___x_1246_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1050_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1255_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1249_ = v___x_1246_;
v_isShared_1250_ = v_isSharedCheck_1255_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1246_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1255_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1251_; lean_object* v___x_1253_; 
v___x_1251_ = l_Nat_Internal_Linear_Expr_inc(v_a_1247_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 0, v___x_1251_);
v___x_1253_ = v___x_1249_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1251_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
else
{
return v___x_1246_;
}
}
}
}
else
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
lean_dec_ref(v_e_1038_);
v_a_1256_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1045_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1045_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1256_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(lean_object* v_e_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_){
_start:
{
switch(lean_obj_tag(v_e_1264_))
{
case 9:
{
lean_object* v_a_1271_; 
v_a_1271_ = lean_ctor_get(v_e_1264_, 0);
lean_inc_ref(v_a_1271_);
if (lean_obj_tag(v_a_1271_) == 0)
{
lean_object* v_val_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1280_; 
lean_dec_ref_known(v_e_1264_, 1);
v_val_1272_ = lean_ctor_get(v_a_1271_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v_a_1271_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1274_ = v_a_1271_;
v_isShared_1275_ = v_isSharedCheck_1280_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_val_1272_);
lean_dec(v_a_1271_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1280_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_val_1272_);
v___x_1277_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
lean_object* v___x_1278_; 
v___x_1278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
return v___x_1278_;
}
}
}
else
{
lean_object* v___x_1281_; 
lean_dec_ref(v_a_1271_);
v___x_1281_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
return v___x_1281_;
}
}
case 10:
{
lean_object* v_expr_1282_; 
v_expr_1282_ = lean_ctor_get(v_e_1264_, 1);
lean_inc_ref(v_expr_1282_);
lean_dec_ref_known(v_e_1264_, 2);
v_e_1264_ = v_expr_1282_;
goto _start;
}
case 4:
{
lean_object* v_declName_1284_; 
v_declName_1284_ = lean_ctor_get(v_e_1264_, 0);
if (lean_obj_tag(v_declName_1284_) == 1)
{
lean_object* v_pre_1285_; 
v_pre_1285_ = lean_ctor_get(v_declName_1284_, 0);
if (lean_obj_tag(v_pre_1285_) == 1)
{
lean_object* v_pre_1286_; 
v_pre_1286_ = lean_ctor_get(v_pre_1285_, 0);
if (lean_obj_tag(v_pre_1286_) == 0)
{
lean_object* v_str_1287_; lean_object* v_str_1288_; lean_object* v___x_1289_; uint8_t v___x_1290_; 
v_str_1287_ = lean_ctor_get(v_declName_1284_, 1);
v_str_1288_ = lean_ctor_get(v_pre_1285_, 1);
v___x_1289_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0));
v___x_1290_ = lean_string_dec_eq(v_str_1288_, v___x_1289_);
if (v___x_1290_ == 0)
{
lean_object* v___x_1291_; 
v___x_1291_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
return v___x_1291_;
}
else
{
lean_object* v___x_1292_; uint8_t v___x_1293_; 
v___x_1292_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__0));
v___x_1293_ = lean_string_dec_eq(v_str_1287_, v___x_1292_);
if (v___x_1293_ == 0)
{
lean_object* v___x_1294_; 
v___x_1294_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
return v___x_1294_;
}
else
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
lean_dec_ref_known(v_e_1264_, 2);
v___x_1295_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__1));
v___x_1296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1295_);
return v___x_1296_;
}
}
}
else
{
lean_object* v___x_1297_; 
v___x_1297_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
return v___x_1297_;
}
}
else
{
lean_object* v___x_1298_; 
v___x_1298_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
return v___x_1298_;
}
}
else
{
lean_object* v___x_1299_; 
v___x_1299_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
return v___x_1299_;
}
}
case 5:
{
lean_object* v___x_1300_; 
v___x_1300_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit(v_e_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
return v___x_1300_;
}
case 2:
{
lean_object* v___x_1301_; 
v___x_1301_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit(v_e_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
return v___x_1301_;
}
default: 
{
lean_object* v___x_1302_; 
v___x_1302_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(v_e_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
return v___x_1302_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___boxed(lean_object* v_e_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_e_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_);
lean_dec(v_a_1308_);
lean_dec_ref(v_a_1307_);
lean_dec(v_a_1306_);
lean_dec_ref(v_a_1305_);
lean_dec(v_a_1304_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___boxed(lean_object* v_e_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit(v_e_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
lean_dec(v_a_1316_);
lean_dec_ref(v_a_1315_);
lean_dec(v_a_1314_);
lean_dec_ref(v_a_1313_);
lean_dec(v_a_1312_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f(lean_object* v_e_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_){
_start:
{
lean_object* v___x_1357_; 
v___x_1357_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1350_, v_a_1353_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1697_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1360_ = v___x_1357_;
v_isShared_1361_ = v_isSharedCheck_1697_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1357_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1697_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1367_; uint8_t v___x_1368_; 
v___x_1367_ = l_Lean_Expr_cleanupAnnotations(v_a_1358_);
v___x_1368_ = l_Lean_Expr_isApp(v___x_1367_);
if (v___x_1368_ == 0)
{
lean_dec_ref(v___x_1367_);
goto v___jp_1362_;
}
else
{
lean_object* v_arg_1369_; lean_object* v___x_1370_; uint8_t v___x_1371_; 
v_arg_1369_ = lean_ctor_get(v___x_1367_, 1);
lean_inc_ref(v_arg_1369_);
v___x_1370_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1367_);
v___x_1371_ = l_Lean_Expr_isApp(v___x_1370_);
if (v___x_1371_ == 0)
{
lean_dec_ref(v___x_1370_);
lean_dec_ref(v_arg_1369_);
goto v___jp_1362_;
}
else
{
lean_object* v_arg_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; uint8_t v___x_1375_; 
v_arg_1372_ = lean_ctor_get(v___x_1370_, 1);
lean_inc_ref(v_arg_1372_);
v___x_1373_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1370_);
v___x_1374_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__1));
v___x_1375_ = l_Lean_Expr_isConstOf(v___x_1373_, v___x_1374_);
if (v___x_1375_ == 0)
{
lean_object* v___x_1376_; uint8_t v___x_1377_; 
v___x_1376_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__3));
v___x_1377_ = l_Lean_Expr_isConstOf(v___x_1373_, v___x_1376_);
if (v___x_1377_ == 0)
{
uint8_t v___x_1378_; 
v___x_1378_ = l_Lean_Expr_isApp(v___x_1373_);
if (v___x_1378_ == 0)
{
lean_dec_ref(v___x_1373_);
lean_dec_ref(v_arg_1372_);
lean_dec_ref(v_arg_1369_);
goto v___jp_1362_;
}
else
{
lean_object* v_arg_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; uint8_t v___x_1382_; 
v_arg_1379_ = lean_ctor_get(v___x_1373_, 1);
lean_inc_ref(v_arg_1379_);
v___x_1380_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1373_);
v___x_1381_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__5));
v___x_1382_ = l_Lean_Expr_isConstOf(v___x_1380_, v___x_1381_);
if (v___x_1382_ == 0)
{
uint8_t v___x_1383_; 
v___x_1383_ = l_Lean_Expr_isApp(v___x_1380_);
if (v___x_1383_ == 0)
{
lean_dec_ref(v___x_1380_);
lean_dec_ref(v_arg_1379_);
lean_dec_ref(v_arg_1372_);
lean_dec_ref(v_arg_1369_);
goto v___jp_1362_;
}
else
{
lean_object* v___x_1384_; lean_object* v___x_1385_; uint8_t v___x_1386_; 
v___x_1384_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1380_);
v___x_1385_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__8));
v___x_1386_ = l_Lean_Expr_isConstOf(v___x_1384_, v___x_1385_);
if (v___x_1386_ == 0)
{
lean_object* v___x_1387_; uint8_t v___x_1388_; 
v___x_1387_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__11));
v___x_1388_ = l_Lean_Expr_isConstOf(v___x_1384_, v___x_1387_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1389_; uint8_t v___x_1390_; 
v___x_1389_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__13));
v___x_1390_ = l_Lean_Expr_isConstOf(v___x_1384_, v___x_1389_);
if (v___x_1390_ == 0)
{
lean_object* v___x_1391_; uint8_t v___x_1392_; 
v___x_1391_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__15));
v___x_1392_ = l_Lean_Expr_isConstOf(v___x_1384_, v___x_1391_);
lean_dec_ref(v___x_1384_);
if (v___x_1392_ == 0)
{
lean_dec_ref(v_arg_1379_);
lean_dec_ref(v_arg_1372_);
lean_dec_ref(v_arg_1369_);
goto v___jp_1362_;
}
else
{
lean_object* v___x_1393_; 
lean_del_object(v___x_1360_);
v___x_1393_ = l_Lean_Meta_DefEq_isInstLENat(v_arg_1379_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1432_; 
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1396_ = v___x_1393_;
v_isShared_1397_ = v_isSharedCheck_1432_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1393_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1432_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
uint8_t v___x_1398_; 
v___x_1398_ = lean_unbox(v_a_1394_);
lean_dec(v_a_1394_);
if (v___x_1398_ == 0)
{
lean_object* v___x_1399_; lean_object* v___x_1401_; 
lean_dec_ref(v_arg_1372_);
lean_dec_ref(v_arg_1369_);
v___x_1399_ = lean_box(0);
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 0, v___x_1399_);
v___x_1401_ = v___x_1396_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1399_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
else
{
lean_object* v___x_1403_; 
lean_del_object(v___x_1396_);
v___x_1403_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1372_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_object* v_a_1404_; lean_object* v___x_1405_; 
v_a_1404_ = lean_ctor_get(v___x_1403_, 0);
lean_inc(v_a_1404_);
lean_dec_ref_known(v___x_1403_, 1);
v___x_1405_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1369_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1415_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1408_ = v___x_1405_;
v_isShared_1409_ = v_isSharedCheck_1415_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1405_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1415_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1413_; 
v___x_1410_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1410_, 0, v_a_1404_);
lean_ctor_set(v___x_1410_, 1, v_a_1406_);
lean_ctor_set_uint8(v___x_1410_, sizeof(void*)*2, v___x_1390_);
v___x_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1410_);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v___x_1411_);
v___x_1413_ = v___x_1408_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1411_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
else
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
lean_dec(v_a_1404_);
v_a_1416_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1418_ = v___x_1405_;
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1405_);
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
else
{
lean_object* v_a_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1431_; 
lean_dec_ref(v_arg_1369_);
v_a_1424_ = lean_ctor_get(v___x_1403_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1426_ = v___x_1403_;
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_a_1424_);
lean_dec(v___x_1403_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1429_; 
if (v_isShared_1427_ == 0)
{
v___x_1429_ = v___x_1426_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_a_1424_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
}
}
}
else
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
lean_dec_ref(v_arg_1372_);
lean_dec_ref(v_arg_1369_);
v_a_1433_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v___x_1393_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1393_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1433_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
}
else
{
lean_object* v___x_1441_; 
lean_dec_ref(v___x_1384_);
lean_del_object(v___x_1360_);
v___x_1441_ = l_Lean_Meta_DefEq_isInstLTNat(v_arg_1379_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1481_; 
v_a_1442_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1444_ = v___x_1441_;
v_isShared_1445_ = v_isSharedCheck_1481_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1441_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1481_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
uint8_t v___x_1446_; 
v___x_1446_ = lean_unbox(v_a_1442_);
lean_dec(v_a_1442_);
if (v___x_1446_ == 0)
{
lean_object* v___x_1447_; lean_object* v___x_1449_; 
lean_dec_ref(v_arg_1372_);
lean_dec_ref(v_arg_1369_);
v___x_1447_ = lean_box(0);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 0, v___x_1447_);
v___x_1449_ = v___x_1444_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1447_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
else
{
lean_object* v___x_1451_; 
lean_del_object(v___x_1444_);
v___x_1451_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1372_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v_a_1452_; lean_object* v___x_1453_; 
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_a_1452_);
lean_dec_ref_known(v___x_1451_, 1);
v___x_1453_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1369_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1464_; 
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1456_ = v___x_1453_;
v_isShared_1457_ = v_isSharedCheck_1464_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1453_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1464_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1462_; 
v___x_1458_ = l_Nat_Internal_Linear_Expr_inc(v_a_1452_);
v___x_1459_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1459_, 0, v___x_1458_);
lean_ctor_set(v___x_1459_, 1, v_a_1454_);
lean_ctor_set_uint8(v___x_1459_, sizeof(void*)*2, v___x_1388_);
v___x_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1459_);
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 0, v___x_1460_);
v___x_1462_ = v___x_1456_;
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
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1472_; 
lean_dec(v_a_1452_);
v_a_1465_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1467_ = v___x_1453_;
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1453_);
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
else
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
lean_dec_ref(v_arg_1369_);
v_a_1473_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1451_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1451_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
}
}
else
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
lean_dec_ref(v_arg_1372_);
lean_dec_ref(v_arg_1369_);
v_a_1482_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1441_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1441_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
}
}
else
{
lean_object* v___x_1490_; 
lean_dec_ref(v___x_1384_);
lean_del_object(v___x_1360_);
v___x_1490_ = l_Lean_Meta_DefEq_isInstLENat(v_arg_1379_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1529_; 
v_a_1491_ = lean_ctor_get(v___x_1490_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1493_ = v___x_1490_;
v_isShared_1494_ = v_isSharedCheck_1529_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v___x_1490_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1529_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
uint8_t v___x_1495_; 
v___x_1495_ = lean_unbox(v_a_1491_);
lean_dec(v_a_1491_);
if (v___x_1495_ == 0)
{
lean_object* v___x_1496_; lean_object* v___x_1498_; 
lean_dec_ref(v_arg_1372_);
lean_dec_ref(v_arg_1369_);
v___x_1496_ = lean_box(0);
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 0, v___x_1496_);
v___x_1498_ = v___x_1493_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1496_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
else
{
lean_object* v___x_1500_; 
lean_del_object(v___x_1493_);
v___x_1500_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1369_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_a_1501_; lean_object* v___x_1502_; 
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_a_1501_);
lean_dec_ref_known(v___x_1500_, 1);
v___x_1502_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1372_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1512_; 
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1505_ = v___x_1502_;
v_isShared_1506_ = v_isSharedCheck_1512_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1502_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1512_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1510_; 
v___x_1507_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1507_, 0, v_a_1501_);
lean_ctor_set(v___x_1507_, 1, v_a_1503_);
lean_ctor_set_uint8(v___x_1507_, sizeof(void*)*2, v___x_1386_);
v___x_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1507_);
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 0, v___x_1508_);
v___x_1510_ = v___x_1505_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1508_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
else
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
lean_dec(v_a_1501_);
v_a_1513_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1515_ = v___x_1502_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1502_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1513_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
else
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1528_; 
lean_dec_ref(v_arg_1372_);
v_a_1521_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1523_ = v___x_1500_;
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1500_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1526_; 
if (v_isShared_1524_ == 0)
{
v___x_1526_ = v___x_1523_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1521_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
}
}
}
else
{
lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1537_; 
lean_dec_ref(v_arg_1372_);
lean_dec_ref(v_arg_1369_);
v_a_1530_ = lean_ctor_get(v___x_1490_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1532_ = v___x_1490_;
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v___x_1490_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1535_; 
if (v_isShared_1533_ == 0)
{
v___x_1535_ = v___x_1532_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_a_1530_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
}
}
else
{
lean_object* v___x_1538_; 
lean_dec_ref(v___x_1384_);
lean_del_object(v___x_1360_);
v___x_1538_ = l_Lean_Meta_DefEq_isInstLTNat(v_arg_1379_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1578_; 
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1541_ = v___x_1538_;
v_isShared_1542_ = v_isSharedCheck_1578_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1538_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1578_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
uint8_t v___x_1543_; 
v___x_1543_ = lean_unbox(v_a_1539_);
lean_dec(v_a_1539_);
if (v___x_1543_ == 0)
{
lean_object* v___x_1544_; lean_object* v___x_1546_; 
lean_dec_ref(v_arg_1372_);
lean_dec_ref(v_arg_1369_);
v___x_1544_ = lean_box(0);
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 0, v___x_1544_);
v___x_1546_ = v___x_1541_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1544_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
else
{
lean_object* v___x_1548_; 
lean_del_object(v___x_1541_);
v___x_1548_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1369_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; lean_object* v___x_1550_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
lean_inc(v_a_1549_);
lean_dec_ref_known(v___x_1548_, 1);
v___x_1550_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1372_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1561_; 
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1553_ = v___x_1550_;
v_isShared_1554_ = v_isSharedCheck_1561_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1550_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1561_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1559_; 
v___x_1555_ = l_Nat_Internal_Linear_Expr_inc(v_a_1549_);
v___x_1556_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
lean_ctor_set(v___x_1556_, 1, v_a_1551_);
lean_ctor_set_uint8(v___x_1556_, sizeof(void*)*2, v___x_1382_);
v___x_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1556_);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 0, v___x_1557_);
v___x_1559_ = v___x_1553_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1557_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
else
{
lean_object* v_a_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1569_; 
lean_dec(v_a_1549_);
v_a_1562_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1564_ = v___x_1550_;
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_a_1562_);
lean_dec(v___x_1550_);
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
else
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1577_; 
lean_dec_ref(v_arg_1372_);
v_a_1570_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1572_ = v___x_1548_;
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1548_);
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
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
lean_dec_ref(v_arg_1372_);
lean_dec_ref(v_arg_1369_);
v_a_1579_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1581_ = v___x_1538_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1538_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
if (v_isShared_1582_ == 0)
{
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_a_1579_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
}
}
else
{
lean_object* v___x_1587_; 
lean_dec_ref(v___x_1380_);
lean_del_object(v___x_1360_);
v___x_1587_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1379_, v_a_1353_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1628_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1590_ = v___x_1587_;
v_isShared_1591_ = v_isSharedCheck_1628_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1587_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1628_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; uint8_t v___x_1594_; 
v___x_1592_ = l_Lean_Expr_cleanupAnnotations(v_a_1588_);
v___x_1593_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__16));
v___x_1594_ = l_Lean_Expr_isConstOf(v___x_1592_, v___x_1593_);
lean_dec_ref(v___x_1592_);
if (v___x_1594_ == 0)
{
lean_object* v___x_1595_; lean_object* v___x_1597_; 
lean_dec_ref(v_arg_1372_);
lean_dec_ref(v_arg_1369_);
v___x_1595_ = lean_box(0);
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 0, v___x_1595_);
v___x_1597_ = v___x_1590_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1595_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
else
{
lean_object* v___x_1599_; 
lean_del_object(v___x_1590_);
v___x_1599_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1372_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v_a_1600_; lean_object* v___x_1601_; 
v_a_1600_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_a_1600_);
lean_dec_ref_known(v___x_1599_, 1);
v___x_1601_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1369_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1611_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1604_ = v___x_1601_;
v_isShared_1605_ = v_isSharedCheck_1611_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1601_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1611_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1609_; 
v___x_1606_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1606_, 0, v_a_1600_);
lean_ctor_set(v___x_1606_, 1, v_a_1602_);
lean_ctor_set_uint8(v___x_1606_, sizeof(void*)*2, v___x_1594_);
v___x_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1606_);
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 0, v___x_1607_);
v___x_1609_ = v___x_1604_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1607_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
else
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
lean_dec(v_a_1600_);
v_a_1612_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v___x_1601_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1601_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1612_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
else
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
lean_dec_ref(v_arg_1369_);
v_a_1620_ = lean_ctor_get(v___x_1599_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v___x_1599_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1599_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
}
}
else
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1636_; 
lean_dec_ref(v_arg_1372_);
lean_dec_ref(v_arg_1369_);
v_a_1629_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1631_ = v___x_1587_;
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1587_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1634_; 
if (v_isShared_1632_ == 0)
{
v___x_1634_ = v___x_1631_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_a_1629_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
}
}
}
else
{
lean_object* v___x_1637_; 
lean_dec_ref(v___x_1373_);
lean_del_object(v___x_1360_);
v___x_1637_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1372_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v_a_1638_; lean_object* v___x_1639_; 
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_a_1638_);
lean_dec_ref_known(v___x_1637_, 1);
v___x_1639_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1369_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1649_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1642_ = v___x_1639_;
v_isShared_1643_ = v_isSharedCheck_1649_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1639_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1649_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1647_; 
v___x_1644_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1644_, 0, v_a_1638_);
lean_ctor_set(v___x_1644_, 1, v_a_1640_);
lean_ctor_set_uint8(v___x_1644_, sizeof(void*)*2, v___x_1375_);
v___x_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1644_);
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 0, v___x_1645_);
v___x_1647_ = v___x_1642_;
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
else
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1657_; 
lean_dec(v_a_1638_);
v_a_1650_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1652_ = v___x_1639_;
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1639_);
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
else
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1665_; 
lean_dec_ref(v_arg_1369_);
v_a_1658_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1660_ = v___x_1637_;
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1637_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1663_; 
if (v_isShared_1661_ == 0)
{
v___x_1663_ = v___x_1660_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_a_1658_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
}
else
{
lean_object* v___x_1666_; 
lean_dec_ref(v___x_1373_);
lean_del_object(v___x_1360_);
v___x_1666_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1372_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v_a_1667_; lean_object* v___x_1668_; 
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_a_1667_);
lean_dec_ref_known(v___x_1666_, 1);
v___x_1668_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(v_arg_1369_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1680_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1671_ = v___x_1668_;
v_isShared_1672_ = v_isSharedCheck_1680_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1668_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1680_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
uint8_t v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1678_; 
v___x_1673_ = 0;
v___x_1674_ = l_Nat_Internal_Linear_Expr_inc(v_a_1667_);
v___x_1675_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1675_, 0, v___x_1674_);
lean_ctor_set(v___x_1675_, 1, v_a_1669_);
lean_ctor_set_uint8(v___x_1675_, sizeof(void*)*2, v___x_1673_);
v___x_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1675_);
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 0, v___x_1676_);
v___x_1678_ = v___x_1671_;
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
else
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
lean_dec(v_a_1667_);
v_a_1681_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1683_ = v___x_1668_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1668_);
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
else
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
lean_dec_ref(v_arg_1369_);
v_a_1689_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1691_ = v___x_1666_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1666_);
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
}
}
}
v___jp_1362_:
{
lean_object* v___x_1363_; lean_object* v___x_1365_; 
v___x_1363_ = lean_box(0);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 0, v___x_1363_);
v___x_1365_ = v___x_1360_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1363_);
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
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1705_; 
v_a_1698_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1700_ = v___x_1357_;
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1357_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_a_1698_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___boxed(lean_object* v_e_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f(v_e_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
lean_dec(v_a_1711_);
lean_dec_ref(v_a_1710_);
lean_dec(v_a_1709_);
lean_dec_ref(v_a_1708_);
lean_dec(v_a_1707_);
return v_res_1713_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_1714_; 
v___x_1714_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1714_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1715_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__0, &l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__0_once, _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__0);
v___x_1716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1715_);
return v___x_1716_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__3(void){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1719_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__2));
v___x_1720_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__1, &l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__1_once, _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__1);
v___x_1721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1720_);
lean_ctor_set(v___x_1721_, 1, v___x_1719_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(lean_object* v_x_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_){
_start:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1728_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__3, &l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__3);
v___x_1729_ = lean_st_mk_ref(v___x_1728_);
lean_inc(v_a_1726_);
lean_inc_ref(v_a_1725_);
lean_inc(v_a_1724_);
lean_inc_ref(v_a_1723_);
lean_inc(v___x_1729_);
v___x_1730_ = lean_apply_6(v_x_1722_, v___x_1729_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, lean_box(0));
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1748_; 
v_a_1731_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1733_ = v___x_1730_;
v_isShared_1734_ = v_isSharedCheck_1748_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1730_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1748_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1735_; lean_object* v_vars_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1746_; 
v___x_1735_ = lean_st_ref_get(v___x_1729_);
lean_dec(v___x_1729_);
v_vars_1736_ = lean_ctor_get(v___x_1735_, 1);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1746_ == 0)
{
lean_object* v_unused_1747_; 
v_unused_1747_ = lean_ctor_get(v___x_1735_, 0);
lean_dec(v_unused_1747_);
v___x_1738_ = v___x_1735_;
v_isShared_1739_ = v_isSharedCheck_1746_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_vars_1736_);
lean_dec(v___x_1735_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1746_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
if (v_isShared_1739_ == 0)
{
lean_ctor_set(v___x_1738_, 0, v_a_1731_);
v___x_1741_ = v___x_1738_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1731_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v_vars_1736_);
v___x_1741_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
lean_object* v___x_1743_; 
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 0, v___x_1741_);
v___x_1743_ = v___x_1733_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1741_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
}
}
}
else
{
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1756_; 
lean_dec(v___x_1729_);
v_a_1749_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1751_ = v___x_1730_;
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___x_1730_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1754_; 
if (v_isShared_1752_ == 0)
{
v___x_1754_ = v___x_1751_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_a_1749_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___boxed(lean_object* v_x_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(v_x_1757_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_);
lean_dec(v_a_1761_);
lean_dec_ref(v_a_1760_);
lean_dec(v_a_1759_);
lean_dec_ref(v_a_1758_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run(lean_object* v_00_u03b1_1764_, lean_object* v_x_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_){
_start:
{
lean_object* v___x_1771_; 
v___x_1771_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(v_x_1765_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___boxed(lean_object* v_00_u03b1_1772_, lean_object* v_x_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run(v_00_u03b1_1772_, v_x_1773_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_);
lean_dec(v_a_1777_);
lean_dec_ref(v_a_1776_);
lean_dec(v_a_1775_);
lean_dec_ref(v_a_1774_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearExpr(lean_object* v_e_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_){
_start:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1786_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___boxed), 7, 1);
lean_closure_set(v___x_1786_, 0, v_e_1780_);
v___x_1787_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(v___x_1786_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_a_1788_; lean_object* v_fst_1789_; lean_object* v_snd_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; uint8_t v___x_1793_; 
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
lean_inc(v_a_1788_);
v_fst_1789_ = lean_ctor_get(v_a_1788_, 0);
lean_inc(v_fst_1789_);
v_snd_1790_ = lean_ctor_get(v_a_1788_, 1);
lean_inc(v_snd_1790_);
lean_dec(v_a_1788_);
v___x_1791_ = lean_array_get_size(v_snd_1790_);
v___x_1792_ = lean_unsigned_to_nat(1u);
v___x_1793_ = lean_nat_dec_eq(v___x_1791_, v___x_1792_);
if (v___x_1793_ == 0)
{
lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1812_; 
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1812_ == 0)
{
lean_object* v_unused_1813_; 
v_unused_1813_ = lean_ctor_get(v___x_1787_, 0);
lean_dec(v_unused_1813_);
v___x_1795_ = v___x_1787_;
v_isShared_1796_ = v_isSharedCheck_1812_;
goto v_resetjp_1794_;
}
else
{
lean_dec(v___x_1787_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1812_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
uint8_t v___x_1797_; lean_object* v___x_1798_; lean_object* v_fst_1799_; lean_object* v_snd_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1811_; 
v___x_1797_ = 1;
v___x_1798_ = l_Lean_sortExprs(v_snd_1790_, v___x_1797_);
v_fst_1799_ = lean_ctor_get(v___x_1798_, 0);
v_snd_1800_ = lean_ctor_get(v___x_1798_, 1);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1802_ = v___x_1798_;
v_isShared_1803_ = v_isSharedCheck_1811_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_snd_1800_);
lean_inc(v_fst_1799_);
lean_dec(v___x_1798_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1811_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1804_; lean_object* v___x_1806_; 
v___x_1804_ = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Internal_Linear_Expr_applyPerm_go(v_snd_1800_, v_fst_1789_);
lean_dec(v_snd_1800_);
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 1, v_fst_1799_);
lean_ctor_set(v___x_1802_, 0, v___x_1804_);
v___x_1806_ = v___x_1802_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v___x_1804_);
lean_ctor_set(v_reuseFailAlloc_1810_, 1, v_fst_1799_);
v___x_1806_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
lean_object* v___x_1808_; 
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 0, v___x_1806_);
v___x_1808_ = v___x_1795_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1806_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
}
}
else
{
lean_dec(v_snd_1790_);
lean_dec(v_fst_1789_);
return v___x_1787_;
}
}
else
{
return v___x_1787_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearExpr___boxed(lean_object* v_e_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l_Lean_Meta_Simp_Arith_Nat_toLinearExpr(v_e_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_);
lean_dec(v_a_1818_);
lean_dec_ref(v_a_1817_);
lean_dec(v_a_1816_);
lean_dec_ref(v_a_1815_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearCnstr_x3f(lean_object* v_e_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_){
_start:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1827_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___boxed), 7, 1);
lean_closure_set(v___x_1827_, 0, v_e_1821_);
v___x_1828_ = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(v___x_1827_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1879_; 
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1831_ = v___x_1828_;
v_isShared_1832_ = v_isSharedCheck_1879_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1828_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1879_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v_fst_1833_; 
v_fst_1833_ = lean_ctor_get(v_a_1829_, 0);
lean_inc(v_fst_1833_);
if (lean_obj_tag(v_fst_1833_) == 1)
{
lean_object* v_snd_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1873_; 
v_snd_1834_ = lean_ctor_get(v_a_1829_, 1);
v_isSharedCheck_1873_ = !lean_is_exclusive(v_a_1829_);
if (v_isSharedCheck_1873_ == 0)
{
lean_object* v_unused_1874_; 
v_unused_1874_ = lean_ctor_get(v_a_1829_, 0);
lean_dec(v_unused_1874_);
v___x_1836_ = v_a_1829_;
v_isShared_1837_ = v_isSharedCheck_1873_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_snd_1834_);
lean_dec(v_a_1829_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1873_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v_val_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1872_; 
v_val_1838_ = lean_ctor_get(v_fst_1833_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v_fst_1833_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1840_ = v_fst_1833_;
v_isShared_1841_ = v_isSharedCheck_1872_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_val_1838_);
lean_dec(v_fst_1833_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1872_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; uint8_t v___x_1844_; 
v___x_1842_ = lean_array_get_size(v_snd_1834_);
v___x_1843_ = lean_unsigned_to_nat(1u);
v___x_1844_ = lean_nat_dec_le(v___x_1842_, v___x_1843_);
if (v___x_1844_ == 0)
{
uint8_t v___x_1845_; lean_object* v___x_1846_; lean_object* v_fst_1847_; lean_object* v_snd_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1862_; 
lean_del_object(v___x_1836_);
v___x_1845_ = 1;
v___x_1846_ = l_Lean_sortExprs(v_snd_1834_, v___x_1845_);
v_fst_1847_ = lean_ctor_get(v___x_1846_, 0);
v_snd_1848_ = lean_ctor_get(v___x_1846_, 1);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1850_ = v___x_1846_;
v_isShared_1851_ = v_isSharedCheck_1862_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_snd_1848_);
lean_inc(v_fst_1847_);
lean_dec(v___x_1846_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1862_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1852_; lean_object* v___x_1854_; 
v___x_1852_ = l_Nat_Internal_Linear_ExprCnstr_applyPerm(v_snd_1848_, v_val_1838_);
lean_dec(v_snd_1848_);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 1, v_fst_1847_);
lean_ctor_set(v___x_1850_, 0, v___x_1852_);
v___x_1854_ = v___x_1850_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1852_);
lean_ctor_set(v_reuseFailAlloc_1861_, 1, v_fst_1847_);
v___x_1854_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
lean_object* v___x_1856_; 
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v___x_1854_);
v___x_1856_ = v___x_1840_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v___x_1854_);
v___x_1856_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
lean_object* v___x_1858_; 
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v___x_1856_);
v___x_1858_ = v___x_1831_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1856_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
}
}
else
{
lean_object* v___x_1864_; 
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 0, v_val_1838_);
v___x_1864_ = v___x_1836_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_val_1838_);
lean_ctor_set(v_reuseFailAlloc_1871_, 1, v_snd_1834_);
v___x_1864_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
lean_object* v___x_1866_; 
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v___x_1864_);
v___x_1866_ = v___x_1840_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1864_);
v___x_1866_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
lean_object* v___x_1868_; 
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v___x_1866_);
v___x_1868_ = v___x_1831_;
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
}
}
}
}
else
{
lean_object* v___x_1875_; lean_object* v___x_1877_; 
lean_dec(v_fst_1833_);
lean_dec(v_a_1829_);
v___x_1875_ = lean_box(0);
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v___x_1875_);
v___x_1877_ = v___x_1831_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v___x_1875_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
}
else
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
v_a_1880_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v___x_1828_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1828_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1880_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearCnstr_x3f___boxed(lean_object* v_e_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l_Lean_Meta_Simp_Arith_Nat_toLinearCnstr_x3f(v_e_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_);
lean_dec(v_a_1892_);
lean_dec_ref(v_a_1891_);
lean_dec(v_a_1890_);
lean_dec_ref(v_a_1889_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0(lean_object* v___y_1895_){
_start:
{
lean_inc_ref(v___y_1895_);
return v___y_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0___boxed(lean_object* v___y_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0(v___y_1896_);
lean_dec_ref(v___y_1896_);
return v_res_1897_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1(void){
_start:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1899_ = lean_box(0);
v___x_1900_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__16));
v___x_1901_ = l_Lean_mkConst(v___x_1900_, v___x_1899_);
return v___x_1901_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__2(void){
_start:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1902_ = lean_unsigned_to_nat(0u);
v___x_1903_ = l_Lean_mkNatLit(v___x_1902_);
return v___x_1903_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__3(void){
_start:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1904_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__2, &l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__2);
v___x_1905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1904_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr(lean_object* v_ctx_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_){
_start:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; uint8_t v___x_1914_; 
v___x_1912_ = lean_unsigned_to_nat(0u);
v___x_1913_ = lean_array_get_size(v_ctx_1906_);
v___x_1914_ = lean_nat_dec_lt(v___x_1912_, v___x_1913_);
if (v___x_1914_ == 0)
{
lean_object* v___f_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
lean_dec_ref(v_ctx_1906_);
v___f_1915_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__0));
v___x_1916_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1, &l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1_once, _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1);
v___x_1917_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__3, &l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__3);
v___x_1918_ = l_Lean_RArray_toExpr___redArg(v___x_1916_, v___f_1915_, v___x_1917_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_);
return v___x_1918_;
}
else
{
lean_object* v___f_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___f_1919_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__0));
v___x_1920_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1, &l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1_once, _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1);
v___x_1921_ = l_Lean_RArray_ofArray___redArg(v_ctx_1906_);
v___x_1922_ = l_Lean_RArray_toExpr___redArg(v___x_1920_, v___f_1919_, v___x_1921_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_);
return v___x_1922_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr___boxed(lean_object* v_ctx_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_){
_start:
{
lean_object* v_res_1929_; 
v_res_1929_ = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(v_ctx_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_);
lean_dec(v_a_1927_);
lean_dec_ref(v_a_1926_);
lean_dec(v_a_1925_);
lean_dec_ref(v_a_1924_);
return v_res_1929_;
}
}
lean_object* runtime_initialize_Lean_Util_SortExprs(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_KExprMap(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_RArray(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Offset(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
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
