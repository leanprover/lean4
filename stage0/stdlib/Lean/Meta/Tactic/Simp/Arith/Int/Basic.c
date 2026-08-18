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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_KExprMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_KExprMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_mkIntSub(lean_object*, lean_object*);
lean_object* l_Lean_mkIntNeg(lean_object*);
lean_object* l_Lean_sortExprs(lean_object*, uint8_t);
lean_object* l_Lean_mkIntLit(lean_object*);
lean_object* l_Lean_RArray_toExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RArray_ofArray___redArg(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_m_65_, lean_object* v_query_66_, lean_object* v_x_67_, lean_object* v_x_68_, lean_object* v_x_69_){
_start:
{
lean_object* v_zero_70_; uint8_t v_isZero_71_; 
v_zero_70_ = lean_unsigned_to_nat(0u);
v_isZero_71_ = lean_nat_dec_eq(v_x_68_, v_zero_70_);
if (v_isZero_71_ == 1)
{
lean_dec(v_x_69_);
lean_dec(v_x_68_);
if (lean_obj_tag(v_x_67_) == 0)
{
lean_object* v___x_72_; 
v___x_72_ = lean_box(2);
return v___x_72_;
}
else
{
lean_object* v_val_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_80_; 
v_val_73_ = lean_ctor_get(v_x_67_, 0);
v_isSharedCheck_80_ = !lean_is_exclusive(v_x_67_);
if (v_isSharedCheck_80_ == 0)
{
v___x_75_ = v_x_67_;
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_val_73_);
lean_dec(v_x_67_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_78_; 
if (v_isShared_76_ == 0)
{
v___x_78_ = v___x_75_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_val_73_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
}
else
{
lean_object* v_keyArray_81_; lean_object* v_valueArray_82_; lean_object* v___x_83_; uint8_t v_isSome_84_; 
v_keyArray_81_ = lean_ctor_get(v_m_65_, 1);
v_valueArray_82_ = lean_ctor_get(v_m_65_, 2);
v___x_83_ = lean_array_fget_borrowed(v_keyArray_81_, v_x_69_);
v_isSome_84_ = lean_noption_is_some(v___x_83_);
if (v_isSome_84_ == 0)
{
lean_dec(v_x_68_);
if (lean_obj_tag(v_x_67_) == 0)
{
lean_object* v___x_85_; 
v___x_85_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_85_, 0, v_x_69_);
return v___x_85_;
}
else
{
lean_object* v_val_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_93_; 
lean_dec(v_x_69_);
v_val_86_ = lean_ctor_get(v_x_67_, 0);
v_isSharedCheck_93_ = !lean_is_exclusive(v_x_67_);
if (v_isSharedCheck_93_ == 0)
{
v___x_88_ = v_x_67_;
v_isShared_89_ = v_isSharedCheck_93_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_val_86_);
lean_dec(v_x_67_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_93_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_91_; 
if (v_isShared_89_ == 0)
{
v___x_91_ = v___x_88_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v_val_86_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
return v___x_91_;
}
}
}
}
else
{
lean_object* v_one_94_; lean_object* v_n_95_; lean_object* v___y_97_; 
v_one_94_ = lean_unsigned_to_nat(1u);
v_n_95_ = lean_nat_sub(v_x_68_, v_one_94_);
lean_dec(v_x_68_);
if (v_isSome_84_ == 0)
{
goto v___jp_103_;
}
else
{
lean_object* v___x_105_; uint8_t v_isSome_106_; 
v___x_105_ = lean_array_fget_borrowed(v_valueArray_82_, v_x_69_);
v_isSome_106_ = lean_noption_is_some(v___x_105_);
if (v_isSome_106_ == 0)
{
goto v___jp_103_;
}
else
{
lean_object* v_val_107_; uint8_t v___x_108_; 
lean_inc(v___x_83_);
v_val_107_ = lean_noption_get(v___x_83_);
v___x_108_ = lean_nat_dec_eq(v_val_107_, v_query_66_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
lean_dec(v_val_107_);
v___x_109_ = lean_array_get_size(v_keyArray_81_);
v___x_110_ = lean_nat_add(v_x_69_, v_one_94_);
lean_dec(v_x_69_);
v___x_111_ = lean_nat_dec_lt(v___x_110_, v___x_109_);
if (v___x_111_ == 0)
{
lean_dec(v___x_110_);
v_x_68_ = v_n_95_;
v_x_69_ = v_zero_70_;
goto _start;
}
else
{
v_x_68_ = v_n_95_;
v_x_69_ = v___x_110_;
goto _start;
}
}
else
{
lean_object* v_val_114_; lean_object* v___x_115_; 
lean_dec(v_n_95_);
lean_dec(v_x_67_);
lean_inc(v___x_105_);
v_val_114_ = lean_noption_get(v___x_105_);
v___x_115_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_115_, 0, v_x_69_);
lean_ctor_set(v___x_115_, 1, v_val_107_);
lean_ctor_set(v___x_115_, 2, v_val_114_);
return v___x_115_;
}
}
}
v___jp_96_:
{
lean_object* v___x_98_; lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_98_ = lean_array_get_size(v_keyArray_81_);
v___x_99_ = lean_nat_add(v_x_69_, v_one_94_);
lean_dec(v_x_69_);
v___x_100_ = lean_nat_dec_lt(v___x_99_, v___x_98_);
if (v___x_100_ == 0)
{
lean_dec(v___x_99_);
v_x_67_ = v___y_97_;
v_x_68_ = v_n_95_;
v_x_69_ = v_zero_70_;
goto _start;
}
else
{
v_x_67_ = v___y_97_;
v_x_68_ = v_n_95_;
v_x_69_ = v___x_99_;
goto _start;
}
}
v___jp_103_:
{
if (lean_obj_tag(v_x_67_) == 0)
{
lean_object* v___x_104_; 
lean_inc(v_x_69_);
v___x_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_104_, 0, v_x_69_);
v___y_97_ = v___x_104_;
goto v___jp_96_;
}
else
{
v___y_97_ = v_x_67_;
goto v___jp_96_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_m_116_, lean_object* v_query_117_, lean_object* v_x_118_, lean_object* v_x_119_, lean_object* v_x_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1_spec__2___redArg(v_m_116_, v_query_117_, v_x_118_, v_x_119_, v_x_120_);
lean_dec(v_query_117_);
lean_dec_ref(v_m_116_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1___redArg(lean_object* v_m_122_, lean_object* v_query_123_){
_start:
{
lean_object* v_keyArray_124_; lean_object* v___x_125_; uint64_t v___x_126_; uint64_t v___x_127_; uint64_t v___x_128_; uint64_t v_fold_129_; uint64_t v___x_130_; uint64_t v___x_131_; uint64_t v___x_132_; size_t v___x_133_; size_t v___x_134_; size_t v___x_135_; size_t v___x_136_; size_t v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v_keyArray_124_ = lean_ctor_get(v_m_122_, 1);
v___x_125_ = lean_array_get_size(v_keyArray_124_);
v___x_126_ = lean_uint64_of_nat(v_query_123_);
v___x_127_ = 32ULL;
v___x_128_ = lean_uint64_shift_right(v___x_126_, v___x_127_);
v_fold_129_ = lean_uint64_xor(v___x_126_, v___x_128_);
v___x_130_ = 16ULL;
v___x_131_ = lean_uint64_shift_right(v_fold_129_, v___x_130_);
v___x_132_ = lean_uint64_xor(v_fold_129_, v___x_131_);
v___x_133_ = lean_uint64_to_usize(v___x_132_);
v___x_134_ = lean_usize_of_nat(v___x_125_);
v___x_135_ = ((size_t)1ULL);
v___x_136_ = lean_usize_sub(v___x_134_, v___x_135_);
v___x_137_ = lean_usize_land(v___x_133_, v___x_136_);
v___x_138_ = lean_usize_to_nat(v___x_137_);
v___x_139_ = lean_box(0);
v___x_140_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1_spec__2___redArg(v_m_122_, v_query_123_, v___x_139_, v___x_125_, v___x_138_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_m_141_, lean_object* v_query_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1___redArg(v_m_141_, v_query_142_);
lean_dec(v_query_142_);
lean_dec_ref(v_m_141_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(lean_object* v_m_144_, lean_object* v_query_145_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1___redArg(v_m_144_, v_query_145_);
if (lean_obj_tag(v___x_146_) == 0)
{
lean_object* v_index_147_; lean_object* v_key_148_; lean_object* v_value_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_156_; 
v_index_147_ = lean_ctor_get(v___x_146_, 0);
v_key_148_ = lean_ctor_get(v___x_146_, 1);
v_value_149_ = lean_ctor_get(v___x_146_, 2);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_156_ == 0)
{
v___x_151_ = v___x_146_;
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_value_149_);
lean_inc(v_key_148_);
lean_inc(v_index_147_);
lean_dec(v___x_146_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_154_; 
if (v_isShared_152_ == 0)
{
v___x_154_ = v___x_151_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_index_147_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v_key_148_);
lean_ctor_set(v_reuseFailAlloc_155_, 2, v_value_149_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
else
{
lean_object* v___x_157_; 
lean_dec(v___x_146_);
v___x_157_ = lean_box(1);
return v___x_157_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg___boxed(lean_object* v_m_158_, lean_object* v_query_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(v_m_158_, v_query_159_);
lean_dec(v_query_159_);
lean_dec_ref(v_m_158_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0___redArg(lean_object* v_m_161_, lean_object* v_a_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(v_m_161_, v_a_162_);
if (lean_obj_tag(v___x_163_) == 0)
{
lean_object* v_value_164_; lean_object* v___x_165_; 
v_value_164_ = lean_ctor_get(v___x_163_, 2);
lean_inc(v_value_164_);
lean_dec_ref_known(v___x_163_, 3);
v___x_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_165_, 0, v_value_164_);
return v___x_165_;
}
else
{
lean_object* v___x_166_; 
v___x_166_ = lean_box(0);
return v___x_166_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0___redArg___boxed(lean_object* v_m_167_, lean_object* v_a_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0___redArg(v_m_167_, v_a_168_);
lean_dec(v_a_168_);
lean_dec_ref(v_m_167_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(lean_object* v_perm_170_, lean_object* v_a_171_){
_start:
{
switch(lean_obj_tag(v_a_171_))
{
case 0:
{
return v_a_171_;
}
case 1:
{
lean_object* v_i_172_; lean_object* v___x_173_; 
v_i_172_ = lean_ctor_get(v_a_171_, 0);
v___x_173_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0___redArg(v_perm_170_, v_i_172_);
if (lean_obj_tag(v___x_173_) == 0)
{
return v_a_171_;
}
else
{
lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_181_; 
v_isSharedCheck_181_ = !lean_is_exclusive(v_a_171_);
if (v_isSharedCheck_181_ == 0)
{
lean_object* v_unused_182_; 
v_unused_182_ = lean_ctor_get(v_a_171_, 0);
lean_dec(v_unused_182_);
v___x_175_ = v_a_171_;
v_isShared_176_ = v_isSharedCheck_181_;
goto v_resetjp_174_;
}
else
{
lean_dec(v_a_171_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_181_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v_val_177_; lean_object* v___x_179_; 
v_val_177_ = lean_ctor_get(v___x_173_, 0);
lean_inc(v_val_177_);
lean_dec_ref_known(v___x_173_, 1);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 0, v_val_177_);
v___x_179_ = v___x_175_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_val_177_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
case 2:
{
lean_object* v_a_183_; lean_object* v_b_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_193_; 
v_a_183_ = lean_ctor_get(v_a_171_, 0);
v_b_184_ = lean_ctor_get(v_a_171_, 1);
v_isSharedCheck_193_ = !lean_is_exclusive(v_a_171_);
if (v_isSharedCheck_193_ == 0)
{
v___x_186_ = v_a_171_;
v_isShared_187_ = v_isSharedCheck_193_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_b_184_);
lean_inc(v_a_183_);
lean_dec(v_a_171_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_193_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_191_; 
v___x_188_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_perm_170_, v_a_183_);
v___x_189_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_perm_170_, v_b_184_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 1, v___x_189_);
lean_ctor_set(v___x_186_, 0, v___x_188_);
v___x_191_ = v___x_186_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_188_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v___x_189_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
case 3:
{
lean_object* v_a_194_; lean_object* v_b_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_204_; 
v_a_194_ = lean_ctor_get(v_a_171_, 0);
v_b_195_ = lean_ctor_get(v_a_171_, 1);
v_isSharedCheck_204_ = !lean_is_exclusive(v_a_171_);
if (v_isSharedCheck_204_ == 0)
{
v___x_197_ = v_a_171_;
v_isShared_198_ = v_isSharedCheck_204_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_b_195_);
lean_inc(v_a_194_);
lean_dec(v_a_171_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_204_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_202_; 
v___x_199_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_perm_170_, v_a_194_);
v___x_200_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_perm_170_, v_b_195_);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 1, v___x_200_);
lean_ctor_set(v___x_197_, 0, v___x_199_);
v___x_202_ = v___x_197_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(3, 2, 0);
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
}
case 4:
{
lean_object* v_a_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_213_; 
v_a_205_ = lean_ctor_get(v_a_171_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v_a_171_);
if (v_isSharedCheck_213_ == 0)
{
v___x_207_ = v_a_171_;
v_isShared_208_ = v_isSharedCheck_213_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_a_205_);
lean_dec(v_a_171_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_213_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_209_; lean_object* v___x_211_; 
v___x_209_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_perm_170_, v_a_205_);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 0, v___x_209_);
v___x_211_ = v___x_207_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_209_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
case 5:
{
lean_object* v_k_214_; lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_223_; 
v_k_214_ = lean_ctor_get(v_a_171_, 0);
v_a_215_ = lean_ctor_get(v_a_171_, 1);
v_isSharedCheck_223_ = !lean_is_exclusive(v_a_171_);
if (v_isSharedCheck_223_ == 0)
{
v___x_217_ = v_a_171_;
v_isShared_218_ = v_isSharedCheck_223_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_inc(v_k_214_);
lean_dec(v_a_171_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_223_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_219_; lean_object* v___x_221_; 
v___x_219_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_perm_170_, v_a_215_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 1, v___x_219_);
v___x_221_ = v___x_217_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_k_214_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v___x_219_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
default: 
{
lean_object* v_a_224_; lean_object* v_k_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_233_; 
v_a_224_ = lean_ctor_get(v_a_171_, 0);
v_k_225_ = lean_ctor_get(v_a_171_, 1);
v_isSharedCheck_233_ = !lean_is_exclusive(v_a_171_);
if (v_isSharedCheck_233_ == 0)
{
v___x_227_ = v_a_171_;
v_isShared_228_ = v_isSharedCheck_233_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_k_225_);
lean_inc(v_a_224_);
lean_dec(v_a_171_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_233_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_229_; lean_object* v___x_231_; 
v___x_229_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_perm_170_, v_a_224_);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 0, v___x_229_);
v___x_231_ = v___x_227_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_229_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v_k_225_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go___boxed(lean_object* v_perm_234_, lean_object* v_a_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_perm_234_, v_a_235_);
lean_dec_ref(v_perm_234_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0(lean_object* v_00_u03b2_237_, lean_object* v_m_238_, lean_object* v_a_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0___redArg(v_m_238_, v_a_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0___boxed(lean_object* v_00_u03b2_241_, lean_object* v_m_242_, lean_object* v_a_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0(v_00_u03b2_241_, v_m_242_, v_a_243_);
lean_dec(v_a_243_);
lean_dec_ref(v_m_242_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0(lean_object* v_00_u03b2_245_, lean_object* v_m_246_, lean_object* v_query_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(v_m_246_, v_query_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0___boxed(lean_object* v_00_u03b2_249_, lean_object* v_m_250_, lean_object* v_query_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0(v_00_u03b2_249_, v_m_250_, v_query_251_);
lean_dec(v_query_251_);
lean_dec_ref(v_m_250_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_253_, lean_object* v_m_254_, lean_object* v_query_255_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1___redArg(v_m_254_, v_query_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_257_, lean_object* v_m_258_, lean_object* v_query_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1(v_00_u03b2_257_, v_m_258_, v_query_259_);
lean_dec(v_query_259_);
lean_dec_ref(v_m_258_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_261_, lean_object* v_m_262_, lean_object* v_query_263_, lean_object* v_x_264_, lean_object* v_x_265_, lean_object* v_x_266_, lean_object* v_x_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1_spec__2___redArg(v_m_262_, v_query_263_, v_x_264_, v_x_265_, v_x_266_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_269_, lean_object* v_m_270_, lean_object* v_query_271_, lean_object* v_x_272_, lean_object* v_x_273_, lean_object* v_x_274_, lean_object* v_x_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_269_, v_m_270_, v_query_271_, v_x_272_, v_x_273_, v_x_274_, v_x_275_);
lean_dec(v_query_271_);
lean_dec_ref(v_m_270_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_applyPerm(lean_object* v_perm_277_, lean_object* v_e_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_perm_277_, v_e_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_applyPerm___boxed(lean_object* v_perm_280_, lean_object* v_e_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Int_Internal_Linear_Expr_applyPerm(v_perm_280_, v_e_281_);
lean_dec_ref(v_perm_280_);
return v_res_282_;
}
}
static lean_object* _init_l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = lean_unsigned_to_nat(2u);
v___x_290_ = lean_nat_to_int(v___x_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_instReprPoly__lean_repr(lean_object* v_x_297_, lean_object* v_prec_298_){
_start:
{
lean_object* v___y_300_; lean_object* v___y_301_; lean_object* v___y_302_; 
if (lean_obj_tag(v_x_297_) == 0)
{
lean_object* v_k_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_331_; 
v_k_308_ = lean_ctor_get(v_x_297_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v_x_297_);
if (v_isSharedCheck_331_ == 0)
{
v___x_310_ = v_x_297_;
v_isShared_311_ = v_isSharedCheck_331_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_k_308_);
lean_dec(v_x_297_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_331_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___y_313_; lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_327_ = lean_unsigned_to_nat(1024u);
v___x_328_ = lean_nat_dec_le(v___x_327_, v_prec_298_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; 
v___x_329_ = lean_obj_once(&l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3, &l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3_once, _init_l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3);
v___y_313_ = v___x_329_;
goto v___jp_312_;
}
else
{
lean_object* v___x_330_; 
v___x_330_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0);
v___y_313_ = v___x_330_;
goto v___jp_312_;
}
v___jp_312_:
{
lean_object* v___x_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_314_ = ((lean_object*)(l_Int_Internal_Linear_instReprPoly__lean_repr___closed__2));
v___x_315_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
v___x_316_ = lean_int_dec_lt(v_k_308_, v___x_315_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; lean_object* v___x_319_; 
v___x_317_ = l_Int_repr(v_k_308_);
lean_dec(v_k_308_);
if (v_isShared_311_ == 0)
{
lean_ctor_set_tag(v___x_310_, 3);
lean_ctor_set(v___x_310_, 0, v___x_317_);
v___x_319_ = v___x_310_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_317_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
v___y_300_ = v___x_314_;
v___y_301_ = v___y_313_;
v___y_302_ = v___x_319_;
goto v___jp_299_;
}
}
else
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_324_; 
v___x_321_ = lean_unsigned_to_nat(1024u);
v___x_322_ = l_Int_repr(v_k_308_);
lean_dec(v_k_308_);
if (v_isShared_311_ == 0)
{
lean_ctor_set_tag(v___x_310_, 3);
lean_ctor_set(v___x_310_, 0, v___x_322_);
v___x_324_ = v___x_310_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_322_);
v___x_324_ = v_reuseFailAlloc_326_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v___x_325_; 
v___x_325_ = l_Repr_addAppParen(v___x_324_, v___x_321_);
v___y_300_ = v___x_314_;
v___y_301_ = v___y_313_;
v___y_302_ = v___x_325_;
goto v___jp_299_;
}
}
}
}
}
else
{
lean_object* v_k_332_; lean_object* v_v_333_; lean_object* v_p_334_; lean_object* v___x_335_; lean_object* v___y_337_; lean_object* v___y_338_; lean_object* v___y_339_; lean_object* v___y_340_; lean_object* v___y_354_; uint8_t v___x_364_; 
v_k_332_ = lean_ctor_get(v_x_297_, 0);
lean_inc(v_k_332_);
v_v_333_ = lean_ctor_get(v_x_297_, 1);
lean_inc(v_v_333_);
v_p_334_ = lean_ctor_get(v_x_297_, 2);
lean_inc_ref(v_p_334_);
lean_dec_ref_known(v_x_297_, 3);
v___x_335_ = lean_unsigned_to_nat(1024u);
v___x_364_ = lean_nat_dec_le(v___x_335_, v_prec_298_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; 
v___x_365_ = lean_obj_once(&l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3, &l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3_once, _init_l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3);
v___y_354_ = v___x_365_;
goto v___jp_353_;
}
else
{
lean_object* v___x_366_; 
v___x_366_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0);
v___y_354_ = v___x_366_;
goto v___jp_353_;
}
v___jp_336_:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; uint8_t v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
lean_inc(v___y_337_);
v___x_341_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_341_, 0, v___y_337_);
lean_ctor_set(v___x_341_, 1, v___y_340_);
lean_inc_n(v___y_339_, 2);
v___x_342_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v___y_339_);
v___x_343_ = l_Nat_reprFast(v_v_333_);
v___x_344_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
v___x_345_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_342_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
v___x_346_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set(v___x_346_, 1, v___y_339_);
v___x_347_ = l_Int_Internal_Linear_instReprPoly__lean_repr(v_p_334_, v___x_335_);
v___x_348_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_346_);
lean_ctor_set(v___x_348_, 1, v___x_347_);
lean_inc(v___y_338_);
v___x_349_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_349_, 0, v___y_338_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
v___x_350_ = 0;
v___x_351_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_351_, 0, v___x_349_);
lean_ctor_set_uint8(v___x_351_, sizeof(void*)*1, v___x_350_);
v___x_352_ = l_Repr_addAppParen(v___x_351_, v_prec_298_);
return v___x_352_;
}
v___jp_353_:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_355_ = lean_box(1);
v___x_356_ = ((lean_object*)(l_Int_Internal_Linear_instReprPoly__lean_repr___closed__6));
v___x_357_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
v___x_358_ = lean_int_dec_lt(v_k_332_, v___x_357_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = l_Int_repr(v_k_332_);
lean_dec(v_k_332_);
v___x_360_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
v___y_337_ = v___x_356_;
v___y_338_ = v___y_354_;
v___y_339_ = v___x_355_;
v___y_340_ = v___x_360_;
goto v___jp_336_;
}
else
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_361_ = l_Int_repr(v_k_332_);
lean_dec(v_k_332_);
v___x_362_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
v___x_363_ = l_Repr_addAppParen(v___x_362_, v___x_335_);
v___y_337_ = v___x_356_;
v___y_338_ = v___y_354_;
v___y_339_ = v___x_355_;
v___y_340_ = v___x_363_;
goto v___jp_336_;
}
}
}
v___jp_299_:
{
lean_object* v___x_303_; lean_object* v___x_304_; uint8_t v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
lean_inc(v___y_300_);
v___x_303_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_303_, 0, v___y_300_);
lean_ctor_set(v___x_303_, 1, v___y_302_);
lean_inc(v___y_301_);
v___x_304_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_304_, 0, v___y_301_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
v___x_305_ = 0;
v___x_306_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_306_, 0, v___x_304_);
lean_ctor_set_uint8(v___x_306_, sizeof(void*)*1, v___x_305_);
v___x_307_ = l_Repr_addAppParen(v___x_306_, v_prec_298_);
return v___x_307_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_instReprPoly__lean_repr___boxed(lean_object* v_x_367_, lean_object* v_prec_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Int_Internal_Linear_instReprPoly__lean_repr(v_x_367_, v_prec_368_);
lean_dec(v_prec_368_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_instReprExpr__lean_repr(lean_object* v_x_414_, lean_object* v_prec_415_){
_start:
{
lean_object* v___y_417_; lean_object* v___y_418_; lean_object* v___y_419_; lean_object* v___y_426_; lean_object* v___y_427_; lean_object* v___y_428_; 
switch(lean_obj_tag(v_x_414_))
{
case 0:
{
lean_object* v_v_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_457_; 
v_v_434_ = lean_ctor_get(v_x_414_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v_x_414_);
if (v_isSharedCheck_457_ == 0)
{
v___x_436_ = v_x_414_;
v_isShared_437_ = v_isSharedCheck_457_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_v_434_);
lean_dec(v_x_414_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_457_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___y_439_; lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_453_ = lean_unsigned_to_nat(1024u);
v___x_454_ = lean_nat_dec_le(v___x_453_, v_prec_415_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; 
v___x_455_ = lean_obj_once(&l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3, &l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3_once, _init_l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3);
v___y_439_ = v___x_455_;
goto v___jp_438_;
}
else
{
lean_object* v___x_456_; 
v___x_456_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0);
v___y_439_ = v___x_456_;
goto v___jp_438_;
}
v___jp_438_:
{
lean_object* v___x_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_440_ = ((lean_object*)(l_Int_Internal_Linear_instReprExpr__lean_repr___closed__2));
v___x_441_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
v___x_442_ = lean_int_dec_lt(v_v_434_, v___x_441_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; lean_object* v___x_445_; 
v___x_443_ = l_Int_repr(v_v_434_);
lean_dec(v_v_434_);
if (v_isShared_437_ == 0)
{
lean_ctor_set_tag(v___x_436_, 3);
lean_ctor_set(v___x_436_, 0, v___x_443_);
v___x_445_ = v___x_436_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_443_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
v___y_426_ = v___y_439_;
v___y_427_ = v___x_440_;
v___y_428_ = v___x_445_;
goto v___jp_425_;
}
}
else
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_450_; 
v___x_447_ = lean_unsigned_to_nat(1024u);
v___x_448_ = l_Int_repr(v_v_434_);
lean_dec(v_v_434_);
if (v_isShared_437_ == 0)
{
lean_ctor_set_tag(v___x_436_, 3);
lean_ctor_set(v___x_436_, 0, v___x_448_);
v___x_450_ = v___x_436_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_448_);
v___x_450_ = v_reuseFailAlloc_452_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v___x_451_; 
v___x_451_ = l_Repr_addAppParen(v___x_450_, v___x_447_);
v___y_426_ = v___y_439_;
v___y_427_ = v___x_440_;
v___y_428_ = v___x_451_;
goto v___jp_425_;
}
}
}
}
}
case 1:
{
lean_object* v_i_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_478_; 
v_i_458_ = lean_ctor_get(v_x_414_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v_x_414_);
if (v_isSharedCheck_478_ == 0)
{
v___x_460_ = v_x_414_;
v_isShared_461_ = v_isSharedCheck_478_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_i_458_);
lean_dec(v_x_414_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_478_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___y_463_; lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_474_ = lean_unsigned_to_nat(1024u);
v___x_475_ = lean_nat_dec_le(v___x_474_, v_prec_415_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; 
v___x_476_ = lean_obj_once(&l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3, &l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3_once, _init_l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3);
v___y_463_ = v___x_476_;
goto v___jp_462_;
}
else
{
lean_object* v___x_477_; 
v___x_477_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0);
v___y_463_ = v___x_477_;
goto v___jp_462_;
}
v___jp_462_:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_467_; 
v___x_464_ = ((lean_object*)(l_Int_Internal_Linear_instReprExpr__lean_repr___closed__5));
v___x_465_ = l_Nat_reprFast(v_i_458_);
if (v_isShared_461_ == 0)
{
lean_ctor_set_tag(v___x_460_, 3);
lean_ctor_set(v___x_460_, 0, v___x_465_);
v___x_467_ = v___x_460_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_465_);
v___x_467_ = v_reuseFailAlloc_473_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
lean_object* v___x_468_; lean_object* v___x_469_; uint8_t v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_468_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_464_);
lean_ctor_set(v___x_468_, 1, v___x_467_);
lean_inc(v___y_463_);
v___x_469_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_469_, 0, v___y_463_);
lean_ctor_set(v___x_469_, 1, v___x_468_);
v___x_470_ = 0;
v___x_471_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_471_, 0, v___x_469_);
lean_ctor_set_uint8(v___x_471_, sizeof(void*)*1, v___x_470_);
v___x_472_ = l_Repr_addAppParen(v___x_471_, v_prec_415_);
return v___x_472_;
}
}
}
}
case 2:
{
lean_object* v_a_479_; lean_object* v_b_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_503_; 
v_a_479_ = lean_ctor_get(v_x_414_, 0);
v_b_480_ = lean_ctor_get(v_x_414_, 1);
v_isSharedCheck_503_ = !lean_is_exclusive(v_x_414_);
if (v_isSharedCheck_503_ == 0)
{
v___x_482_ = v_x_414_;
v_isShared_483_ = v_isSharedCheck_503_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_b_480_);
lean_inc(v_a_479_);
lean_dec(v_x_414_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_503_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_484_; lean_object* v___y_486_; uint8_t v___x_500_; 
v___x_484_ = lean_unsigned_to_nat(1024u);
v___x_500_ = lean_nat_dec_le(v___x_484_, v_prec_415_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; 
v___x_501_ = lean_obj_once(&l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3, &l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3_once, _init_l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3);
v___y_486_ = v___x_501_;
goto v___jp_485_;
}
else
{
lean_object* v___x_502_; 
v___x_502_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0);
v___y_486_ = v___x_502_;
goto v___jp_485_;
}
v___jp_485_:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_491_; 
v___x_487_ = lean_box(1);
v___x_488_ = ((lean_object*)(l_Int_Internal_Linear_instReprExpr__lean_repr___closed__8));
v___x_489_ = l_Int_Internal_Linear_instReprExpr__lean_repr(v_a_479_, v___x_484_);
if (v_isShared_483_ == 0)
{
lean_ctor_set_tag(v___x_482_, 5);
lean_ctor_set(v___x_482_, 1, v___x_489_);
lean_ctor_set(v___x_482_, 0, v___x_488_);
v___x_491_ = v___x_482_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_488_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v___x_489_);
v___x_491_ = v_reuseFailAlloc_499_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; uint8_t v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_492_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
lean_ctor_set(v___x_492_, 1, v___x_487_);
v___x_493_ = l_Int_Internal_Linear_instReprExpr__lean_repr(v_b_480_, v___x_484_);
v___x_494_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_492_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
lean_inc(v___y_486_);
v___x_495_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_495_, 0, v___y_486_);
lean_ctor_set(v___x_495_, 1, v___x_494_);
v___x_496_ = 0;
v___x_497_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_497_, 0, v___x_495_);
lean_ctor_set_uint8(v___x_497_, sizeof(void*)*1, v___x_496_);
v___x_498_ = l_Repr_addAppParen(v___x_497_, v_prec_415_);
return v___x_498_;
}
}
}
}
case 3:
{
lean_object* v_a_504_; lean_object* v_b_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_528_; 
v_a_504_ = lean_ctor_get(v_x_414_, 0);
v_b_505_ = lean_ctor_get(v_x_414_, 1);
v_isSharedCheck_528_ = !lean_is_exclusive(v_x_414_);
if (v_isSharedCheck_528_ == 0)
{
v___x_507_ = v_x_414_;
v_isShared_508_ = v_isSharedCheck_528_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_b_505_);
lean_inc(v_a_504_);
lean_dec(v_x_414_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_528_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_509_; lean_object* v___y_511_; uint8_t v___x_525_; 
v___x_509_ = lean_unsigned_to_nat(1024u);
v___x_525_ = lean_nat_dec_le(v___x_509_, v_prec_415_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; 
v___x_526_ = lean_obj_once(&l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3, &l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3_once, _init_l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3);
v___y_511_ = v___x_526_;
goto v___jp_510_;
}
else
{
lean_object* v___x_527_; 
v___x_527_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0);
v___y_511_ = v___x_527_;
goto v___jp_510_;
}
v___jp_510_:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_516_; 
v___x_512_ = lean_box(1);
v___x_513_ = ((lean_object*)(l_Int_Internal_Linear_instReprExpr__lean_repr___closed__11));
v___x_514_ = l_Int_Internal_Linear_instReprExpr__lean_repr(v_a_504_, v___x_509_);
if (v_isShared_508_ == 0)
{
lean_ctor_set_tag(v___x_507_, 5);
lean_ctor_set(v___x_507_, 1, v___x_514_);
lean_ctor_set(v___x_507_, 0, v___x_513_);
v___x_516_ = v___x_507_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v___x_514_);
v___x_516_ = v_reuseFailAlloc_524_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_517_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_517_, 0, v___x_516_);
lean_ctor_set(v___x_517_, 1, v___x_512_);
v___x_518_ = l_Int_Internal_Linear_instReprExpr__lean_repr(v_b_505_, v___x_509_);
v___x_519_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_519_, 0, v___x_517_);
lean_ctor_set(v___x_519_, 1, v___x_518_);
lean_inc(v___y_511_);
v___x_520_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_520_, 0, v___y_511_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = 0;
v___x_522_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_522_, 0, v___x_520_);
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*1, v___x_521_);
v___x_523_ = l_Repr_addAppParen(v___x_522_, v_prec_415_);
return v___x_523_;
}
}
}
}
case 4:
{
lean_object* v_a_529_; lean_object* v___x_530_; lean_object* v___y_532_; uint8_t v___x_540_; 
v_a_529_ = lean_ctor_get(v_x_414_, 0);
lean_inc_ref(v_a_529_);
lean_dec_ref_known(v_x_414_, 1);
v___x_530_ = lean_unsigned_to_nat(1024u);
v___x_540_ = lean_nat_dec_le(v___x_530_, v_prec_415_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; 
v___x_541_ = lean_obj_once(&l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3, &l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3_once, _init_l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3);
v___y_532_ = v___x_541_;
goto v___jp_531_;
}
else
{
lean_object* v___x_542_; 
v___x_542_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0);
v___y_532_ = v___x_542_;
goto v___jp_531_;
}
v___jp_531_:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; uint8_t v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_533_ = ((lean_object*)(l_Int_Internal_Linear_instReprExpr__lean_repr___closed__14));
v___x_534_ = l_Int_Internal_Linear_instReprExpr__lean_repr(v_a_529_, v___x_530_);
v___x_535_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_533_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
lean_inc(v___y_532_);
v___x_536_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_536_, 0, v___y_532_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = 0;
v___x_538_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_538_, 0, v___x_536_);
lean_ctor_set_uint8(v___x_538_, sizeof(void*)*1, v___x_537_);
v___x_539_ = l_Repr_addAppParen(v___x_538_, v_prec_415_);
return v___x_539_;
}
}
case 5:
{
lean_object* v_k_543_; lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_578_; 
v_k_543_ = lean_ctor_get(v_x_414_, 0);
v_a_544_ = lean_ctor_get(v_x_414_, 1);
v_isSharedCheck_578_ = !lean_is_exclusive(v_x_414_);
if (v_isSharedCheck_578_ == 0)
{
v___x_546_ = v_x_414_;
v_isShared_547_ = v_isSharedCheck_578_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_inc(v_k_543_);
lean_dec(v_x_414_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_578_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_548_; lean_object* v___y_550_; lean_object* v___y_551_; lean_object* v___y_552_; lean_object* v___y_553_; lean_object* v___y_565_; uint8_t v___x_575_; 
v___x_548_ = lean_unsigned_to_nat(1024u);
v___x_575_ = lean_nat_dec_le(v___x_548_, v_prec_415_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; 
v___x_576_ = lean_obj_once(&l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3, &l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3_once, _init_l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3);
v___y_565_ = v___x_576_;
goto v___jp_564_;
}
else
{
lean_object* v___x_577_; 
v___x_577_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0);
v___y_565_ = v___x_577_;
goto v___jp_564_;
}
v___jp_549_:
{
lean_object* v___x_555_; 
lean_inc(v___y_551_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 1, v___y_553_);
lean_ctor_set(v___x_546_, 0, v___y_551_);
v___x_555_ = v___x_546_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___y_551_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v___y_553_);
v___x_555_ = v_reuseFailAlloc_563_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; uint8_t v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
lean_inc(v___y_550_);
v___x_556_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
lean_ctor_set(v___x_556_, 1, v___y_550_);
v___x_557_ = l_Int_Internal_Linear_instReprExpr__lean_repr(v_a_544_, v___x_548_);
v___x_558_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_556_);
lean_ctor_set(v___x_558_, 1, v___x_557_);
lean_inc(v___y_552_);
v___x_559_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_559_, 0, v___y_552_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
v___x_560_ = 0;
v___x_561_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_561_, 0, v___x_559_);
lean_ctor_set_uint8(v___x_561_, sizeof(void*)*1, v___x_560_);
v___x_562_ = l_Repr_addAppParen(v___x_561_, v_prec_415_);
return v___x_562_;
}
}
v___jp_564_:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_566_ = lean_box(1);
v___x_567_ = ((lean_object*)(l_Int_Internal_Linear_instReprExpr__lean_repr___closed__17));
v___x_568_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
v___x_569_ = lean_int_dec_lt(v_k_543_, v___x_568_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = l_Int_repr(v_k_543_);
lean_dec(v_k_543_);
v___x_571_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
v___y_550_ = v___x_566_;
v___y_551_ = v___x_567_;
v___y_552_ = v___y_565_;
v___y_553_ = v___x_571_;
goto v___jp_549_;
}
else
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_572_ = l_Int_repr(v_k_543_);
lean_dec(v_k_543_);
v___x_573_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
v___x_574_ = l_Repr_addAppParen(v___x_573_, v___x_548_);
v___y_550_ = v___x_566_;
v___y_551_ = v___x_567_;
v___y_552_ = v___y_565_;
v___y_553_ = v___x_574_;
goto v___jp_549_;
}
}
}
}
default: 
{
lean_object* v_a_579_; lean_object* v_k_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_604_; 
v_a_579_ = lean_ctor_get(v_x_414_, 0);
v_k_580_ = lean_ctor_get(v_x_414_, 1);
v_isSharedCheck_604_ = !lean_is_exclusive(v_x_414_);
if (v_isSharedCheck_604_ == 0)
{
v___x_582_ = v_x_414_;
v_isShared_583_ = v_isSharedCheck_604_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_k_580_);
lean_inc(v_a_579_);
lean_dec(v_x_414_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_604_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_584_; lean_object* v___y_586_; uint8_t v___x_601_; 
v___x_584_ = lean_unsigned_to_nat(1024u);
v___x_601_ = lean_nat_dec_le(v___x_584_, v_prec_415_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; 
v___x_602_ = lean_obj_once(&l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3, &l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3_once, _init_l_Int_Internal_Linear_instReprPoly__lean_repr___closed__3);
v___y_586_ = v___x_602_;
goto v___jp_585_;
}
else
{
lean_object* v___x_603_; 
v___x_603_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0);
v___y_586_ = v___x_603_;
goto v___jp_585_;
}
v___jp_585_:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_591_; 
v___x_587_ = lean_box(1);
v___x_588_ = ((lean_object*)(l_Int_Internal_Linear_instReprExpr__lean_repr___closed__20));
v___x_589_ = l_Int_Internal_Linear_instReprExpr__lean_repr(v_a_579_, v___x_584_);
if (v_isShared_583_ == 0)
{
lean_ctor_set_tag(v___x_582_, 5);
lean_ctor_set(v___x_582_, 1, v___x_589_);
lean_ctor_set(v___x_582_, 0, v___x_588_);
v___x_591_ = v___x_582_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_588_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v___x_589_);
v___x_591_ = v_reuseFailAlloc_600_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
lean_object* v___x_592_; lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_592_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
lean_ctor_set(v___x_592_, 1, v___x_587_);
v___x_593_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
v___x_594_ = lean_int_dec_lt(v_k_580_, v___x_593_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = l_Int_repr(v_k_580_);
lean_dec(v_k_580_);
v___x_596_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
v___y_417_ = v___x_592_;
v___y_418_ = v___y_586_;
v___y_419_ = v___x_596_;
goto v___jp_416_;
}
else
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_597_ = l_Int_repr(v_k_580_);
lean_dec(v_k_580_);
v___x_598_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
v___x_599_ = l_Repr_addAppParen(v___x_598_, v___x_584_);
v___y_417_ = v___x_592_;
v___y_418_ = v___y_586_;
v___y_419_ = v___x_599_;
goto v___jp_416_;
}
}
}
}
}
}
v___jp_416_:
{
lean_object* v___x_420_; lean_object* v___x_421_; uint8_t v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_420_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_420_, 0, v___y_417_);
lean_ctor_set(v___x_420_, 1, v___y_419_);
lean_inc(v___y_418_);
v___x_421_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_421_, 0, v___y_418_);
lean_ctor_set(v___x_421_, 1, v___x_420_);
v___x_422_ = 0;
v___x_423_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_423_, 0, v___x_421_);
lean_ctor_set_uint8(v___x_423_, sizeof(void*)*1, v___x_422_);
v___x_424_ = l_Repr_addAppParen(v___x_423_, v_prec_415_);
return v___x_424_;
}
v___jp_425_:
{
lean_object* v___x_429_; lean_object* v___x_430_; uint8_t v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
lean_inc(v___y_427_);
v___x_429_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_429_, 0, v___y_427_);
lean_ctor_set(v___x_429_, 1, v___y_428_);
lean_inc(v___y_426_);
v___x_430_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_430_, 0, v___y_426_);
lean_ctor_set(v___x_430_, 1, v___x_429_);
v___x_431_ = 0;
v___x_432_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_432_, 0, v___x_430_);
lean_ctor_set_uint8(v___x_432_, sizeof(void*)*1, v___x_431_);
v___x_433_ = l_Repr_addAppParen(v___x_432_, v_prec_415_);
return v___x_433_;
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_instReprExpr__lean_repr___boxed(lean_object* v_x_605_, lean_object* v_prec_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Int_Internal_Linear_instReprExpr__lean_repr(v_x_605_, v_prec_606_);
lean_dec(v_prec_606_);
return v_res_607_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__6(void){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_621_ = lean_box(0);
v___x_622_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__5));
v___x_623_ = l_Lean_mkConst(v___x_622_, v___x_621_);
return v___x_623_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__10(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = lean_unsigned_to_nat(0u);
v___x_630_ = l_Lean_Level_ofNat(v___x_629_);
return v___x_630_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11(void){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_631_ = lean_box(0);
v___x_632_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__10, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__10_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__10);
v___x_633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
lean_ctor_set(v___x_633_, 1, v___x_631_);
return v___x_633_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12(void){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_634_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11);
v___x_635_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__9));
v___x_636_ = l_Lean_Expr_const___override(v___x_635_, v___x_634_);
return v___x_636_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_639_ = lean_box(0);
v___x_640_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13));
v___x_641_ = l_Lean_Expr_const___override(v___x_640_, v___x_639_);
return v___x_641_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_646_ = lean_box(0);
v___x_647_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16));
v___x_648_ = l_Lean_Expr_const___override(v___x_647_, v___x_646_);
return v___x_648_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__20(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_656_ = lean_box(0);
v___x_657_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__19));
v___x_658_ = l_Lean_mkConst(v___x_657_, v___x_656_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly(lean_object* v_p_659_){
_start:
{
if (lean_obj_tag(v_p_659_) == 0)
{
lean_object* v_k_660_; lean_object* v___x_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
v_k_660_ = lean_ctor_get(v_p_659_, 0);
lean_inc(v_k_660_);
lean_dec_ref_known(v_p_659_, 1);
v___x_661_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__6, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__6_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__6);
v___x_662_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
v___x_663_ = lean_int_dec_le(v___x_662_, v_k_660_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_664_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12);
v___x_665_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14);
v___x_666_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17);
v___x_667_ = lean_int_neg(v_k_660_);
lean_dec(v_k_660_);
v___x_668_ = l_Int_toNat(v___x_667_);
lean_dec(v___x_667_);
v___x_669_ = l_Lean_instToExprInt_mkNat(v___x_668_);
v___x_670_ = l_Lean_mkApp3(v___x_664_, v___x_665_, v___x_666_, v___x_669_);
v___x_671_ = l_Lean_Expr_app___override(v___x_661_, v___x_670_);
return v___x_671_;
}
else
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_672_ = l_Int_toNat(v_k_660_);
lean_dec(v_k_660_);
v___x_673_ = l_Lean_instToExprInt_mkNat(v___x_672_);
v___x_674_ = l_Lean_Expr_app___override(v___x_661_, v___x_673_);
return v___x_674_;
}
}
else
{
lean_object* v_k_675_; lean_object* v_v_676_; lean_object* v_p_677_; lean_object* v___x_678_; lean_object* v___y_680_; lean_object* v___x_684_; uint8_t v___x_685_; 
v_k_675_ = lean_ctor_get(v_p_659_, 0);
lean_inc(v_k_675_);
v_v_676_ = lean_ctor_get(v_p_659_, 1);
lean_inc(v_v_676_);
v_p_677_ = lean_ctor_get(v_p_659_, 2);
lean_inc_ref(v_p_677_);
lean_dec_ref_known(v_p_659_, 3);
v___x_678_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__20, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__20_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__20);
v___x_684_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
v___x_685_ = lean_int_dec_le(v___x_684_, v_k_675_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_686_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12);
v___x_687_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14);
v___x_688_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17);
v___x_689_ = lean_int_neg(v_k_675_);
lean_dec(v_k_675_);
v___x_690_ = l_Int_toNat(v___x_689_);
lean_dec(v___x_689_);
v___x_691_ = l_Lean_instToExprInt_mkNat(v___x_690_);
v___x_692_ = l_Lean_mkApp3(v___x_686_, v___x_687_, v___x_688_, v___x_691_);
v___y_680_ = v___x_692_;
goto v___jp_679_;
}
else
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = l_Int_toNat(v_k_675_);
lean_dec(v_k_675_);
v___x_694_ = l_Lean_instToExprInt_mkNat(v___x_693_);
v___y_680_ = v___x_694_;
goto v___jp_679_;
}
v___jp_679_:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_681_ = l_Lean_mkNatLit(v_v_676_);
v___x_682_ = l_Lean_Meta_Simp_Arith_Int_ofPoly(v_p_677_);
v___x_683_ = l_Lean_mkApp3(v___x_678_, v___y_680_, v___x_681_, v___x_682_);
return v___x_683_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__2(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_701_ = lean_box(0);
v___x_702_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__1));
v___x_703_ = l_Lean_mkConst(v___x_702_, v___x_701_);
return v___x_703_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__3(void){
_start:
{
lean_object* v___x_704_; lean_object* v___f_705_; lean_object* v___x_706_; 
v___x_704_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__2, &l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__2);
v___f_705_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__0));
v___x_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_706_, 0, v___f_705_);
lean_ctor_set(v___x_706_, 1, v___x_704_);
return v___x_706_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_instToExprPoly(void){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__3, &l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__3);
return v___x_707_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__2(void){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_715_ = lean_box(0);
v___x_716_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1));
v___x_717_ = l_Lean_mkConst(v___x_716_, v___x_715_);
return v___x_717_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__5(void){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_725_ = lean_box(0);
v___x_726_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4));
v___x_727_ = l_Lean_mkConst(v___x_726_, v___x_725_);
return v___x_727_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__7(void){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_734_ = lean_box(0);
v___x_735_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6));
v___x_736_ = l_Lean_mkConst(v___x_735_, v___x_734_);
return v___x_736_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__10(void){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_744_ = lean_box(0);
v___x_745_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9));
v___x_746_ = l_Lean_mkConst(v___x_745_, v___x_744_);
return v___x_746_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__12(void){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_753_ = lean_box(0);
v___x_754_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11));
v___x_755_ = l_Lean_mkConst(v___x_754_, v___x_753_);
return v___x_755_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__15(void){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_763_ = lean_box(0);
v___x_764_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14));
v___x_765_ = l_Lean_mkConst(v___x_764_, v___x_763_);
return v___x_765_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__18(void){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_773_ = lean_box(0);
v___x_774_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17));
v___x_775_ = l_Lean_mkConst(v___x_774_, v___x_773_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(lean_object* v_e_776_){
_start:
{
switch(lean_obj_tag(v_e_776_))
{
case 0:
{
lean_object* v_v_777_; lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_780_; 
v_v_777_ = lean_ctor_get(v_e_776_, 0);
lean_inc(v_v_777_);
lean_dec_ref_known(v_e_776_, 1);
v___x_778_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__2, &l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__2);
v___x_779_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
v___x_780_ = lean_int_dec_le(v___x_779_, v_v_777_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_781_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12);
v___x_782_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14);
v___x_783_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17);
v___x_784_ = lean_int_neg(v_v_777_);
lean_dec(v_v_777_);
v___x_785_ = l_Int_toNat(v___x_784_);
lean_dec(v___x_784_);
v___x_786_ = l_Lean_instToExprInt_mkNat(v___x_785_);
v___x_787_ = l_Lean_mkApp3(v___x_781_, v___x_782_, v___x_783_, v___x_786_);
v___x_788_ = l_Lean_Expr_app___override(v___x_778_, v___x_787_);
return v___x_788_;
}
else
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_789_ = l_Int_toNat(v_v_777_);
lean_dec(v_v_777_);
v___x_790_ = l_Lean_instToExprInt_mkNat(v___x_789_);
v___x_791_ = l_Lean_Expr_app___override(v___x_778_, v___x_790_);
return v___x_791_;
}
}
case 1:
{
lean_object* v_i_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v_i_792_ = lean_ctor_get(v_e_776_, 0);
lean_inc(v_i_792_);
lean_dec_ref_known(v_e_776_, 1);
v___x_793_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__5, &l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__5_once, _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__5);
v___x_794_ = l_Lean_mkNatLit(v_i_792_);
v___x_795_ = l_Lean_Expr_app___override(v___x_793_, v___x_794_);
return v___x_795_;
}
case 2:
{
lean_object* v_a_796_; lean_object* v_b_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v_a_796_ = lean_ctor_get(v_e_776_, 0);
lean_inc_ref(v_a_796_);
v_b_797_ = lean_ctor_get(v_e_776_, 1);
lean_inc_ref(v_b_797_);
lean_dec_ref_known(v_e_776_, 2);
v___x_798_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__7, &l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__7_once, _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__7);
v___x_799_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_a_796_);
v___x_800_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_b_797_);
v___x_801_ = l_Lean_mkAppB(v___x_798_, v___x_799_, v___x_800_);
return v___x_801_;
}
case 3:
{
lean_object* v_a_802_; lean_object* v_b_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v_a_802_ = lean_ctor_get(v_e_776_, 0);
lean_inc_ref(v_a_802_);
v_b_803_ = lean_ctor_get(v_e_776_, 1);
lean_inc_ref(v_b_803_);
lean_dec_ref_known(v_e_776_, 2);
v___x_804_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__10, &l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__10_once, _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__10);
v___x_805_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_a_802_);
v___x_806_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_b_803_);
v___x_807_ = l_Lean_mkAppB(v___x_804_, v___x_805_, v___x_806_);
return v___x_807_;
}
case 4:
{
lean_object* v_a_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v_a_808_ = lean_ctor_get(v_e_776_, 0);
lean_inc_ref(v_a_808_);
lean_dec_ref_known(v_e_776_, 1);
v___x_809_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__12, &l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__12);
v___x_810_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_a_808_);
v___x_811_ = l_Lean_Expr_app___override(v___x_809_, v___x_810_);
return v___x_811_;
}
case 5:
{
lean_object* v_k_812_; lean_object* v_a_813_; lean_object* v___x_814_; lean_object* v___y_816_; lean_object* v___x_819_; uint8_t v___x_820_; 
v_k_812_ = lean_ctor_get(v_e_776_, 0);
lean_inc(v_k_812_);
v_a_813_ = lean_ctor_get(v_e_776_, 1);
lean_inc_ref(v_a_813_);
lean_dec_ref_known(v_e_776_, 2);
v___x_814_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__15, &l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__15_once, _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__15);
v___x_819_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
v___x_820_ = lean_int_dec_le(v___x_819_, v_k_812_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_821_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12);
v___x_822_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14);
v___x_823_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17);
v___x_824_ = lean_int_neg(v_k_812_);
lean_dec(v_k_812_);
v___x_825_ = l_Int_toNat(v___x_824_);
lean_dec(v___x_824_);
v___x_826_ = l_Lean_instToExprInt_mkNat(v___x_825_);
v___x_827_ = l_Lean_mkApp3(v___x_821_, v___x_822_, v___x_823_, v___x_826_);
v___y_816_ = v___x_827_;
goto v___jp_815_;
}
else
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = l_Int_toNat(v_k_812_);
lean_dec(v_k_812_);
v___x_829_ = l_Lean_instToExprInt_mkNat(v___x_828_);
v___y_816_ = v___x_829_;
goto v___jp_815_;
}
v___jp_815_:
{
lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_817_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_a_813_);
v___x_818_ = l_Lean_mkAppB(v___x_814_, v___y_816_, v___x_817_);
return v___x_818_;
}
}
default: 
{
lean_object* v_a_830_; lean_object* v_k_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; uint8_t v___x_835_; 
v_a_830_ = lean_ctor_get(v_e_776_, 0);
lean_inc_ref(v_a_830_);
v_k_831_ = lean_ctor_get(v_e_776_, 1);
lean_inc(v_k_831_);
lean_dec_ref_known(v_e_776_, 2);
v___x_832_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__18, &l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__18_once, _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__18);
v___x_833_ = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(v_a_830_);
v___x_834_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
v___x_835_ = lean_int_dec_le(v___x_834_, v_k_831_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_836_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12);
v___x_837_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14);
v___x_838_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17);
v___x_839_ = lean_int_neg(v_k_831_);
lean_dec(v_k_831_);
v___x_840_ = l_Int_toNat(v___x_839_);
lean_dec(v___x_839_);
v___x_841_ = l_Lean_instToExprInt_mkNat(v___x_840_);
v___x_842_ = l_Lean_mkApp3(v___x_836_, v___x_837_, v___x_838_, v___x_841_);
v___x_843_ = l_Lean_mkAppB(v___x_832_, v___x_833_, v___x_842_);
return v___x_843_;
}
else
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_844_ = l_Int_toNat(v_k_831_);
lean_dec(v_k_831_);
v___x_845_ = l_Lean_instToExprInt_mkNat(v___x_844_);
v___x_846_ = l_Lean_mkAppB(v___x_832_, v___x_833_, v___x_845_);
return v___x_846_;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__2(void){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_853_ = lean_box(0);
v___x_854_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__1));
v___x_855_ = l_Lean_mkConst(v___x_854_, v___x_853_);
return v___x_855_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__3(void){
_start:
{
lean_object* v___x_856_; lean_object* v___f_857_; lean_object* v___x_858_; 
v___x_856_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__2, &l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__2);
v___f_857_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__0));
v___x_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_858_, 0, v___f_857_);
lean_ctor_set(v___x_858_, 1, v___x_856_);
return v___x_858_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_instToExprExpr(void){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__3, &l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__3);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_denoteExpr___redArg(lean_object* v_ctx_860_, lean_object* v_e_861_){
_start:
{
switch(lean_obj_tag(v_e_861_))
{
case 0:
{
lean_object* v_v_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_884_; 
lean_dec_ref(v_ctx_860_);
v_v_863_ = lean_ctor_get(v_e_861_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v_e_861_);
if (v_isSharedCheck_884_ == 0)
{
v___x_865_ = v_e_861_;
v_isShared_866_ = v_isSharedCheck_884_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_v_863_);
lean_dec(v_e_861_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_884_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_867_; uint8_t v___x_868_; 
v___x_867_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
v___x_868_ = lean_int_dec_le(v___x_867_, v_v_863_);
if (v___x_868_ == 0)
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_877_; 
v___x_869_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12);
v___x_870_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14);
v___x_871_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17);
v___x_872_ = lean_int_neg(v_v_863_);
lean_dec(v_v_863_);
v___x_873_ = l_Int_toNat(v___x_872_);
lean_dec(v___x_872_);
v___x_874_ = l_Lean_instToExprInt_mkNat(v___x_873_);
v___x_875_ = l_Lean_mkApp3(v___x_869_, v___x_870_, v___x_871_, v___x_874_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_875_);
v___x_877_ = v___x_865_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_875_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
else
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_882_; 
v___x_879_ = l_Int_toNat(v_v_863_);
lean_dec(v_v_863_);
v___x_880_ = l_Lean_instToExprInt_mkNat(v___x_879_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_880_);
v___x_882_ = v___x_865_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_880_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
case 1:
{
lean_object* v_i_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_893_; 
v_i_885_ = lean_ctor_get(v_e_861_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v_e_861_);
if (v_isSharedCheck_893_ == 0)
{
v___x_887_ = v_e_861_;
v_isShared_888_ = v_isSharedCheck_893_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_i_885_);
lean_dec(v_e_861_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_893_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_889_; lean_object* v___x_891_; 
v___x_889_ = lean_apply_1(v_ctx_860_, v_i_885_);
if (v_isShared_888_ == 0)
{
lean_ctor_set_tag(v___x_887_, 0);
lean_ctor_set(v___x_887_, 0, v___x_889_);
v___x_891_ = v___x_887_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_889_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
case 2:
{
lean_object* v_a_894_; lean_object* v_b_895_; lean_object* v___x_896_; lean_object* v_a_897_; lean_object* v___x_898_; lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_907_; 
v_a_894_ = lean_ctor_get(v_e_861_, 0);
lean_inc_ref(v_a_894_);
v_b_895_ = lean_ctor_get(v_e_861_, 1);
lean_inc_ref(v_b_895_);
lean_dec_ref_known(v_e_861_, 2);
lean_inc_ref(v_ctx_860_);
v___x_896_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v_ctx_860_, v_a_894_);
v_a_897_ = lean_ctor_get(v___x_896_, 0);
lean_inc(v_a_897_);
lean_dec_ref(v___x_896_);
v___x_898_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v_ctx_860_, v_b_895_);
v_a_899_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_907_ == 0)
{
v___x_901_ = v___x_898_;
v_isShared_902_ = v_isSharedCheck_907_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_898_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_907_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_903_; lean_object* v___x_905_; 
v___x_903_ = l_Lean_mkIntAdd(v_a_897_, v_a_899_);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 0, v___x_903_);
v___x_905_ = v___x_901_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_903_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
case 3:
{
lean_object* v_a_908_; lean_object* v_b_909_; lean_object* v___x_910_; lean_object* v_a_911_; lean_object* v___x_912_; lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_921_; 
v_a_908_ = lean_ctor_get(v_e_861_, 0);
lean_inc_ref(v_a_908_);
v_b_909_ = lean_ctor_get(v_e_861_, 1);
lean_inc_ref(v_b_909_);
lean_dec_ref_known(v_e_861_, 2);
lean_inc_ref(v_ctx_860_);
v___x_910_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v_ctx_860_, v_a_908_);
v_a_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_a_911_);
lean_dec_ref(v___x_910_);
v___x_912_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v_ctx_860_, v_b_909_);
v_a_913_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_921_ == 0)
{
v___x_915_ = v___x_912_;
v_isShared_916_ = v_isSharedCheck_921_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_912_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_921_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_917_; lean_object* v___x_919_; 
v___x_917_ = l_Lean_mkIntSub(v_a_911_, v_a_913_);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 0, v___x_917_);
v___x_919_ = v___x_915_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_917_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
case 4:
{
lean_object* v_a_922_; lean_object* v___x_923_; lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_932_; 
v_a_922_ = lean_ctor_get(v_e_861_, 0);
lean_inc_ref(v_a_922_);
lean_dec_ref_known(v_e_861_, 1);
v___x_923_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v_ctx_860_, v_a_922_);
v_a_924_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_932_ == 0)
{
v___x_926_ = v___x_923_;
v_isShared_927_ = v_isSharedCheck_932_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_923_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_932_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_928_; lean_object* v___x_930_; 
v___x_928_ = l_Lean_mkIntNeg(v_a_924_);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 0, v___x_928_);
v___x_930_ = v___x_926_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_928_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
case 5:
{
lean_object* v_k_933_; lean_object* v_a_934_; lean_object* v___x_935_; lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_957_; 
v_k_933_ = lean_ctor_get(v_e_861_, 0);
lean_inc(v_k_933_);
v_a_934_ = lean_ctor_get(v_e_861_, 1);
lean_inc_ref(v_a_934_);
lean_dec_ref_known(v_e_861_, 2);
v___x_935_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v_ctx_860_, v_a_934_);
v_a_936_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_957_ == 0)
{
v___x_938_ = v___x_935_;
v_isShared_939_ = v_isSharedCheck_957_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_935_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_957_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___y_941_; lean_object* v___x_946_; uint8_t v___x_947_; 
v___x_946_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
v___x_947_ = lean_int_dec_le(v___x_946_, v_k_933_);
if (v___x_947_ == 0)
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_948_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12);
v___x_949_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14);
v___x_950_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17);
v___x_951_ = lean_int_neg(v_k_933_);
lean_dec(v_k_933_);
v___x_952_ = l_Int_toNat(v___x_951_);
lean_dec(v___x_951_);
v___x_953_ = l_Lean_instToExprInt_mkNat(v___x_952_);
v___x_954_ = l_Lean_mkApp3(v___x_948_, v___x_949_, v___x_950_, v___x_953_);
v___y_941_ = v___x_954_;
goto v___jp_940_;
}
else
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = l_Int_toNat(v_k_933_);
lean_dec(v_k_933_);
v___x_956_ = l_Lean_instToExprInt_mkNat(v___x_955_);
v___y_941_ = v___x_956_;
goto v___jp_940_;
}
v___jp_940_:
{
lean_object* v___x_942_; lean_object* v___x_944_; 
v___x_942_ = l_Lean_mkIntMul(v___y_941_, v_a_936_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 0, v___x_942_);
v___x_944_ = v___x_938_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_942_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
}
default: 
{
lean_object* v_a_958_; lean_object* v_k_959_; lean_object* v___x_960_; lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_982_; 
v_a_958_ = lean_ctor_get(v_e_861_, 0);
lean_inc_ref(v_a_958_);
v_k_959_ = lean_ctor_get(v_e_861_, 1);
lean_inc(v_k_959_);
lean_dec_ref_known(v_e_861_, 2);
v___x_960_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v_ctx_860_, v_a_958_);
v_a_961_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_982_ == 0)
{
v___x_963_ = v___x_960_;
v_isShared_964_ = v_isSharedCheck_982_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_960_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_982_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___y_966_; lean_object* v___x_971_; uint8_t v___x_972_; 
v___x_971_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
v___x_972_ = lean_int_dec_le(v___x_971_, v_k_959_);
if (v___x_972_ == 0)
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_973_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12);
v___x_974_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14);
v___x_975_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17);
v___x_976_ = lean_int_neg(v_k_959_);
lean_dec(v_k_959_);
v___x_977_ = l_Int_toNat(v___x_976_);
lean_dec(v___x_976_);
v___x_978_ = l_Lean_instToExprInt_mkNat(v___x_977_);
v___x_979_ = l_Lean_mkApp3(v___x_973_, v___x_974_, v___x_975_, v___x_978_);
v___y_966_ = v___x_979_;
goto v___jp_965_;
}
else
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = l_Int_toNat(v_k_959_);
lean_dec(v_k_959_);
v___x_981_ = l_Lean_instToExprInt_mkNat(v___x_980_);
v___y_966_ = v___x_981_;
goto v___jp_965_;
}
v___jp_965_:
{
lean_object* v___x_967_; lean_object* v___x_969_; 
v___x_967_ = l_Lean_mkIntMul(v_a_961_, v___y_966_);
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 0, v___x_967_);
v___x_969_ = v___x_963_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_967_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_denoteExpr___redArg___boxed(lean_object* v_ctx_983_, lean_object* v_e_984_, lean_object* v_a_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v_ctx_983_, v_e_984_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_denoteExpr(lean_object* v_ctx_987_, lean_object* v_e_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = l_Int_Internal_Linear_Expr_denoteExpr___redArg(v_ctx_987_, v_e_988_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Expr_denoteExpr___boxed(lean_object* v_ctx_995_, lean_object* v_e_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Int_Internal_Linear_Expr_denoteExpr(v_ctx_995_, v_e_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
lean_dec(v_a_1000_);
lean_dec_ref(v_a_999_);
lean_dec(v_a_998_);
lean_dec_ref(v_a_997_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_denoteExpr_go___redArg(lean_object* v_ctx_1003_, lean_object* v_r_1004_, lean_object* v_p_1005_){
_start:
{
lean_object* v___y_1008_; 
if (lean_obj_tag(v_p_1005_) == 0)
{
lean_object* v_k_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1030_; 
lean_dec_ref(v_ctx_1003_);
v_k_1011_ = lean_ctor_get(v_p_1005_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v_p_1005_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1013_ = v_p_1005_;
v_isShared_1014_ = v_isSharedCheck_1030_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_k_1011_);
lean_dec(v_p_1005_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1030_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1015_; uint8_t v___x_1016_; 
v___x_1015_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
v___x_1016_ = lean_int_dec_eq(v_k_1011_, v___x_1015_);
if (v___x_1016_ == 0)
{
uint8_t v___x_1017_; 
lean_del_object(v___x_1013_);
v___x_1017_ = lean_int_dec_le(v___x_1015_, v_k_1011_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1018_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12);
v___x_1019_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14);
v___x_1020_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17);
v___x_1021_ = lean_int_neg(v_k_1011_);
lean_dec(v_k_1011_);
v___x_1022_ = l_Int_toNat(v___x_1021_);
lean_dec(v___x_1021_);
v___x_1023_ = l_Lean_instToExprInt_mkNat(v___x_1022_);
v___x_1024_ = l_Lean_mkApp3(v___x_1018_, v___x_1019_, v___x_1020_, v___x_1023_);
v___y_1008_ = v___x_1024_;
goto v___jp_1007_;
}
else
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = l_Int_toNat(v_k_1011_);
lean_dec(v_k_1011_);
v___x_1026_ = l_Lean_instToExprInt_mkNat(v___x_1025_);
v___y_1008_ = v___x_1026_;
goto v___jp_1007_;
}
}
else
{
lean_object* v___x_1028_; 
lean_dec(v_k_1011_);
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 0, v_r_1004_);
v___x_1028_ = v___x_1013_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_r_1004_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
else
{
lean_object* v_k_1031_; lean_object* v_v_1032_; lean_object* v_p_1033_; lean_object* v___y_1035_; lean_object* v___x_1040_; uint8_t v___x_1041_; 
v_k_1031_ = lean_ctor_get(v_p_1005_, 0);
lean_inc(v_k_1031_);
v_v_1032_ = lean_ctor_get(v_p_1005_, 1);
lean_inc(v_v_1032_);
v_p_1033_ = lean_ctor_get(v_p_1005_, 2);
lean_inc_ref(v_p_1033_);
lean_dec_ref_known(v_p_1005_, 3);
v___x_1040_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0);
v___x_1041_ = lean_int_dec_eq(v_k_1031_, v___x_1040_);
if (v___x_1041_ == 0)
{
lean_object* v___x_1042_; uint8_t v___x_1043_; 
v___x_1042_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
v___x_1043_ = lean_int_dec_le(v___x_1042_, v_k_1031_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1044_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12);
v___x_1045_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14);
v___x_1046_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17);
v___x_1047_ = lean_int_neg(v_k_1031_);
lean_dec(v_k_1031_);
v___x_1048_ = l_Int_toNat(v___x_1047_);
lean_dec(v___x_1047_);
v___x_1049_ = l_Lean_instToExprInt_mkNat(v___x_1048_);
v___x_1050_ = l_Lean_mkApp3(v___x_1044_, v___x_1045_, v___x_1046_, v___x_1049_);
v___y_1035_ = v___x_1050_;
goto v___jp_1034_;
}
else
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = l_Int_toNat(v_k_1031_);
lean_dec(v_k_1031_);
v___x_1052_ = l_Lean_instToExprInt_mkNat(v___x_1051_);
v___y_1035_ = v___x_1052_;
goto v___jp_1034_;
}
}
else
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
lean_dec(v_k_1031_);
lean_inc_ref(v_ctx_1003_);
v___x_1053_ = lean_apply_1(v_ctx_1003_, v_v_1032_);
v___x_1054_ = l_Lean_mkIntAdd(v_r_1004_, v___x_1053_);
v_r_1004_ = v___x_1054_;
v_p_1005_ = v_p_1033_;
goto _start;
}
v___jp_1034_:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
lean_inc_ref(v_ctx_1003_);
v___x_1036_ = lean_apply_1(v_ctx_1003_, v_v_1032_);
v___x_1037_ = l_Lean_mkIntMul(v___y_1035_, v___x_1036_);
v___x_1038_ = l_Lean_mkIntAdd(v_r_1004_, v___x_1037_);
v_r_1004_ = v___x_1038_;
v_p_1005_ = v_p_1033_;
goto _start;
}
}
v___jp_1007_:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = l_Lean_mkIntAdd(v_r_1004_, v___y_1008_);
v___x_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
return v___x_1010_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_denoteExpr_go___redArg___boxed(lean_object* v_ctx_1056_, lean_object* v_r_1057_, lean_object* v_p_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_denoteExpr_go___redArg(v_ctx_1056_, v_r_1057_, v_p_1058_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_denoteExpr_go(lean_object* v_ctx_1061_, lean_object* v_r_1062_, lean_object* v_p_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_denoteExpr_go___redArg(v_ctx_1061_, v_r_1062_, v_p_1063_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_denoteExpr_go___boxed(lean_object* v_ctx_1070_, lean_object* v_r_1071_, lean_object* v_p_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_denoteExpr_go(v_ctx_1070_, v_r_1071_, v_p_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_);
lean_dec(v_a_1076_);
lean_dec_ref(v_a_1075_);
lean_dec(v_a_1074_);
lean_dec_ref(v_a_1073_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr___redArg(lean_object* v_ctx_1079_, lean_object* v_p_1080_){
_start:
{
if (lean_obj_tag(v_p_1080_) == 0)
{
lean_object* v_k_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1103_; 
lean_dec_ref(v_ctx_1079_);
v_k_1082_ = lean_ctor_get(v_p_1080_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v_p_1080_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1084_ = v_p_1080_;
v_isShared_1085_ = v_isSharedCheck_1103_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_k_1082_);
lean_dec(v_p_1080_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1103_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1086_; uint8_t v___x_1087_; 
v___x_1086_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
v___x_1087_ = lean_int_dec_le(v___x_1086_, v_k_1082_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1096_; 
v___x_1088_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12);
v___x_1089_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14);
v___x_1090_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17);
v___x_1091_ = lean_int_neg(v_k_1082_);
lean_dec(v_k_1082_);
v___x_1092_ = l_Int_toNat(v___x_1091_);
lean_dec(v___x_1091_);
v___x_1093_ = l_Lean_instToExprInt_mkNat(v___x_1092_);
v___x_1094_ = l_Lean_mkApp3(v___x_1088_, v___x_1089_, v___x_1090_, v___x_1093_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 0, v___x_1094_);
v___x_1096_ = v___x_1084_;
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
else
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1101_; 
v___x_1098_ = l_Int_toNat(v_k_1082_);
lean_dec(v_k_1082_);
v___x_1099_ = l_Lean_instToExprInt_mkNat(v___x_1098_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 0, v___x_1099_);
v___x_1101_ = v___x_1084_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1099_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
else
{
lean_object* v_k_1104_; lean_object* v_v_1105_; lean_object* v_p_1106_; lean_object* v___y_1108_; lean_object* v___x_1112_; uint8_t v___x_1113_; 
v_k_1104_ = lean_ctor_get(v_p_1080_, 0);
lean_inc(v_k_1104_);
v_v_1105_ = lean_ctor_get(v_p_1080_, 1);
lean_inc(v_v_1105_);
v_p_1106_ = lean_ctor_get(v_p_1080_, 2);
lean_inc_ref(v_p_1106_);
lean_dec_ref_known(v_p_1080_, 3);
v___x_1112_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0);
v___x_1113_ = lean_int_dec_eq(v_k_1104_, v___x_1112_);
if (v___x_1113_ == 0)
{
lean_object* v___x_1114_; uint8_t v___x_1115_; 
v___x_1114_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
v___x_1115_ = lean_int_dec_le(v___x_1114_, v_k_1104_);
if (v___x_1115_ == 0)
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1116_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12);
v___x_1117_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14);
v___x_1118_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17, &l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17_once, _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17);
v___x_1119_ = lean_int_neg(v_k_1104_);
lean_dec(v_k_1104_);
v___x_1120_ = l_Int_toNat(v___x_1119_);
lean_dec(v___x_1119_);
v___x_1121_ = l_Lean_instToExprInt_mkNat(v___x_1120_);
v___x_1122_ = l_Lean_mkApp3(v___x_1116_, v___x_1117_, v___x_1118_, v___x_1121_);
v___y_1108_ = v___x_1122_;
goto v___jp_1107_;
}
else
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = l_Int_toNat(v_k_1104_);
lean_dec(v_k_1104_);
v___x_1124_ = l_Lean_instToExprInt_mkNat(v___x_1123_);
v___y_1108_ = v___x_1124_;
goto v___jp_1107_;
}
}
else
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
lean_dec(v_k_1104_);
lean_inc_ref(v_ctx_1079_);
v___x_1125_ = lean_apply_1(v_ctx_1079_, v_v_1105_);
v___x_1126_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_denoteExpr_go___redArg(v_ctx_1079_, v___x_1125_, v_p_1106_);
return v___x_1126_;
}
v___jp_1107_:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
lean_inc_ref(v_ctx_1079_);
v___x_1109_ = lean_apply_1(v_ctx_1079_, v_v_1105_);
v___x_1110_ = l_Lean_mkIntMul(v___y_1108_, v___x_1109_);
v___x_1111_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_denoteExpr_go___redArg(v_ctx_1079_, v___x_1110_, v_p_1106_);
return v___x_1111_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr___redArg___boxed(lean_object* v_ctx_1127_, lean_object* v_p_1128_, lean_object* v_a_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_Int_Internal_Linear_Poly_denoteExpr___redArg(v_ctx_1127_, v_p_1128_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr(lean_object* v_ctx_1131_, lean_object* v_p_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l_Int_Internal_Linear_Poly_denoteExpr___redArg(v_ctx_1131_, v_p_1132_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_denoteExpr___boxed(lean_object* v_ctx_1139_, lean_object* v_p_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Int_Internal_Linear_Poly_denoteExpr(v_ctx_1139_, v_p_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_);
lean_dec(v_a_1144_);
lean_dec_ref(v_a_1143_);
lean_dec(v_a_1142_);
lean_dec_ref(v_a_1141_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(lean_object* v_e_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_){
_start:
{
lean_object* v___x_1154_; lean_object* v_varMap_1155_; lean_object* v___x_1156_; 
v___x_1154_ = lean_st_ref_get(v_a_1148_);
v_varMap_1155_ = lean_ctor_get(v___x_1154_, 0);
lean_inc_ref(v_varMap_1155_);
lean_dec(v___x_1154_);
lean_inc_ref(v_e_1147_);
v___x_1156_ = l_Lean_Meta_KExprMap_find_x3f___redArg(v_varMap_1155_, v_e_1147_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_);
lean_dec_ref(v_varMap_1155_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1205_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1159_ = v___x_1156_;
v_isShared_1160_ = v_isSharedCheck_1205_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1156_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1205_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
if (lean_obj_tag(v_a_1157_) == 1)
{
lean_object* v_val_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1171_; 
lean_dec_ref(v_e_1147_);
v_val_1161_ = lean_ctor_get(v_a_1157_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_a_1157_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1163_ = v_a_1157_;
v_isShared_1164_ = v_isSharedCheck_1171_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_val_1161_);
lean_dec(v_a_1157_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1171_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_val_1161_);
v___x_1166_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
lean_object* v___x_1168_; 
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v___x_1166_);
v___x_1168_ = v___x_1159_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1166_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
else
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v_vars_1174_; lean_object* v_varMap_1175_; lean_object* v_vars_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1204_; 
lean_del_object(v___x_1159_);
lean_dec(v_a_1157_);
v___x_1172_ = lean_st_ref_get(v_a_1148_);
v___x_1173_ = lean_st_ref_get(v_a_1148_);
v_vars_1174_ = lean_ctor_get(v___x_1172_, 1);
lean_inc_ref(v_vars_1174_);
lean_dec(v___x_1172_);
v_varMap_1175_ = lean_ctor_get(v___x_1173_, 0);
v_vars_1176_ = lean_ctor_get(v___x_1173_, 1);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1178_ = v___x_1173_;
v_isShared_1179_ = v_isSharedCheck_1204_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_vars_1176_);
lean_inc(v_varMap_1175_);
lean_dec(v___x_1173_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1204_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1180_ = lean_array_get_size(v_vars_1174_);
lean_dec_ref(v_vars_1174_);
lean_inc_ref(v_e_1147_);
v___x_1181_ = l_Lean_Meta_KExprMap_insert___redArg(v_varMap_1175_, v_e_1147_, v___x_1180_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1195_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1184_ = v___x_1181_;
v_isShared_1185_ = v_isSharedCheck_1195_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1181_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1195_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1186_; lean_object* v___x_1188_; 
v___x_1186_ = lean_array_push(v_vars_1176_, v_e_1147_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 1, v___x_1186_);
lean_ctor_set(v___x_1178_, 0, v_a_1182_);
v___x_1188_ = v___x_1178_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1182_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v___x_1186_);
v___x_1188_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1192_; 
v___x_1189_ = lean_st_ref_swap(v_a_1148_, v___x_1188_);
lean_dec(v___x_1189_);
v___x_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1180_);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 0, v___x_1190_);
v___x_1192_ = v___x_1184_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1190_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
else
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
lean_del_object(v___x_1178_);
lean_dec_ref(v_vars_1176_);
lean_dec_ref(v_e_1147_);
v_a_1196_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1181_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1181_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1196_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1213_; 
lean_dec_ref(v_e_1147_);
v_a_1206_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1208_ = v___x_1156_;
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1156_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1209_ == 0)
{
v___x_1211_ = v___x_1208_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1206_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar___boxed(lean_object* v_e_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec_ref(v_a_1216_);
lean_dec(v_a_1215_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit(lean_object* v_e_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_){
_start:
{
lean_object* v___x_1274_; 
lean_inc_ref(v_e_1267_);
v___x_1274_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1267_, v_a_1270_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; lean_object* v___x_1276_; uint8_t v___x_1277_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_a_1275_);
lean_dec_ref_known(v___x_1274_, 1);
v___x_1276_ = l_Lean_Expr_cleanupAnnotations(v_a_1275_);
v___x_1277_ = l_Lean_Expr_isApp(v___x_1276_);
if (v___x_1277_ == 0)
{
lean_object* v___x_1278_; 
lean_dec_ref(v___x_1276_);
v___x_1278_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1278_;
}
else
{
lean_object* v_arg_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; uint8_t v___x_1282_; 
v_arg_1279_ = lean_ctor_get(v___x_1276_, 1);
lean_inc_ref(v_arg_1279_);
v___x_1280_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1276_);
v___x_1281_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__0));
v___x_1282_ = l_Lean_Expr_isConstOf(v___x_1280_, v___x_1281_);
if (v___x_1282_ == 0)
{
uint8_t v___x_1283_; 
v___x_1283_ = l_Lean_Expr_isApp(v___x_1280_);
if (v___x_1283_ == 0)
{
lean_object* v___x_1284_; 
lean_dec_ref(v___x_1280_);
lean_dec_ref(v_arg_1279_);
v___x_1284_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1284_;
}
else
{
lean_object* v_arg_1285_; lean_object* v_b_1287_; lean_object* v___y_1288_; lean_object* v___y_1289_; lean_object* v___y_1290_; lean_object* v___y_1291_; lean_object* v___y_1292_; lean_object* v___x_1336_; lean_object* v___x_1337_; uint8_t v___x_1338_; 
v_arg_1285_ = lean_ctor_get(v___x_1280_, 1);
lean_inc_ref(v_arg_1285_);
v___x_1336_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1280_);
v___x_1337_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__2));
v___x_1338_ = l_Lean_Expr_isConstOf(v___x_1336_, v___x_1337_);
if (v___x_1338_ == 0)
{
lean_object* v___x_1339_; uint8_t v___x_1340_; 
v___x_1339_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__3));
v___x_1340_ = l_Lean_Expr_isConstOf(v___x_1336_, v___x_1339_);
if (v___x_1340_ == 0)
{
lean_object* v___x_1341_; uint8_t v___x_1342_; 
v___x_1341_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__4));
v___x_1342_ = l_Lean_Expr_isConstOf(v___x_1336_, v___x_1341_);
if (v___x_1342_ == 0)
{
uint8_t v___x_1343_; 
v___x_1343_ = l_Lean_Expr_isApp(v___x_1336_);
if (v___x_1343_ == 0)
{
lean_object* v___x_1344_; 
lean_dec_ref(v___x_1336_);
lean_dec_ref(v_arg_1285_);
lean_dec_ref(v_arg_1279_);
v___x_1344_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1344_;
}
else
{
lean_object* v_arg_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; 
v_arg_1345_ = lean_ctor_get(v___x_1336_, 1);
lean_inc_ref(v_arg_1345_);
v___x_1346_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1336_);
v___x_1347_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__9));
v___x_1348_ = l_Lean_Expr_isConstOf(v___x_1346_, v___x_1347_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1349_; uint8_t v___x_1350_; 
v___x_1349_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__7));
v___x_1350_ = l_Lean_Expr_isConstOf(v___x_1346_, v___x_1349_);
if (v___x_1350_ == 0)
{
uint8_t v___x_1351_; 
v___x_1351_ = l_Lean_Expr_isApp(v___x_1346_);
if (v___x_1351_ == 0)
{
lean_object* v___x_1352_; 
lean_dec_ref(v___x_1346_);
lean_dec_ref(v_arg_1345_);
lean_dec_ref(v_arg_1285_);
lean_dec_ref(v_arg_1279_);
v___x_1352_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1352_;
}
else
{
lean_object* v___x_1353_; lean_object* v___x_1354_; uint8_t v___x_1355_; 
v___x_1353_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1346_);
v___x_1354_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__9));
v___x_1355_ = l_Lean_Expr_isConstOf(v___x_1353_, v___x_1354_);
if (v___x_1355_ == 0)
{
lean_object* v___x_1356_; uint8_t v___x_1357_; 
v___x_1356_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__11));
v___x_1357_ = l_Lean_Expr_isConstOf(v___x_1353_, v___x_1356_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; uint8_t v___x_1359_; 
v___x_1358_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__13));
v___x_1359_ = l_Lean_Expr_isConstOf(v___x_1353_, v___x_1358_);
if (v___x_1359_ == 0)
{
uint8_t v___x_1360_; 
v___x_1360_ = l_Lean_Expr_isApp(v___x_1353_);
if (v___x_1360_ == 0)
{
lean_object* v___x_1361_; 
lean_dec_ref(v___x_1353_);
lean_dec_ref(v_arg_1345_);
lean_dec_ref(v_arg_1285_);
lean_dec_ref(v_arg_1279_);
v___x_1361_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1361_;
}
else
{
lean_object* v___x_1362_; uint8_t v___x_1363_; 
v___x_1362_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1353_);
v___x_1363_ = l_Lean_Expr_isApp(v___x_1362_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; 
lean_dec_ref(v___x_1362_);
lean_dec_ref(v_arg_1345_);
lean_dec_ref(v_arg_1285_);
lean_dec_ref(v_arg_1279_);
v___x_1364_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1364_;
}
else
{
lean_object* v___x_1365_; lean_object* v___x_1366_; uint8_t v___x_1367_; 
v___x_1365_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1362_);
v___x_1366_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__16));
v___x_1367_ = l_Lean_Expr_isConstOf(v___x_1365_, v___x_1366_);
if (v___x_1367_ == 0)
{
lean_object* v___x_1368_; uint8_t v___x_1369_; 
v___x_1368_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__19));
v___x_1369_ = l_Lean_Expr_isConstOf(v___x_1365_, v___x_1368_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1370_; uint8_t v___x_1371_; 
v___x_1370_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__22));
v___x_1371_ = l_Lean_Expr_isConstOf(v___x_1365_, v___x_1370_);
lean_dec_ref(v___x_1365_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; 
lean_dec_ref(v_arg_1345_);
lean_dec_ref(v_arg_1285_);
lean_dec_ref(v_arg_1279_);
v___x_1372_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1372_;
}
else
{
lean_object* v___x_1373_; 
v___x_1373_ = l_Lean_Meta_DefEq_isInstHAddInt(v_arg_1345_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v_a_1374_; uint8_t v___x_1375_; 
v_a_1374_ = lean_ctor_get(v___x_1373_, 0);
lean_inc(v_a_1374_);
lean_dec_ref_known(v___x_1373_, 1);
v___x_1375_ = lean_unbox(v_a_1374_);
lean_dec(v_a_1374_);
if (v___x_1375_ == 0)
{
lean_object* v___x_1376_; 
lean_dec_ref(v_arg_1285_);
lean_dec_ref(v_arg_1279_);
v___x_1376_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1376_;
}
else
{
lean_object* v___x_1377_; 
lean_dec_ref(v_e_1267_);
v___x_1377_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1285_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; lean_object* v___x_1379_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_a_1378_);
lean_dec_ref_known(v___x_1377_, 1);
v___x_1379_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1279_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1388_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1382_ = v___x_1379_;
v_isShared_1383_ = v_isSharedCheck_1388_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1379_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1388_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1384_; lean_object* v___x_1386_; 
v___x_1384_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1384_, 0, v_a_1378_);
lean_ctor_set(v___x_1384_, 1, v_a_1380_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 0, v___x_1384_);
v___x_1386_ = v___x_1382_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1384_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
else
{
lean_dec(v_a_1378_);
return v___x_1379_;
}
}
else
{
lean_dec_ref(v_arg_1279_);
return v___x_1377_;
}
}
}
else
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
lean_dec_ref(v_arg_1285_);
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_e_1267_);
v_a_1389_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1391_ = v___x_1373_;
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1373_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
if (v_isShared_1392_ == 0)
{
v___x_1394_ = v___x_1391_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1389_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
}
}
else
{
lean_object* v___x_1397_; 
lean_dec_ref(v___x_1365_);
v___x_1397_ = l_Lean_Meta_DefEq_isInstHSubInt(v_arg_1345_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; uint8_t v___x_1399_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_a_1398_);
lean_dec_ref_known(v___x_1397_, 1);
v___x_1399_ = lean_unbox(v_a_1398_);
lean_dec(v_a_1398_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1400_; 
lean_dec_ref(v_arg_1285_);
lean_dec_ref(v_arg_1279_);
v___x_1400_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1400_;
}
else
{
lean_object* v___x_1401_; 
lean_dec_ref(v_e_1267_);
v___x_1401_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1285_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; lean_object* v___x_1403_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
lean_inc(v_a_1402_);
lean_dec_ref_known(v___x_1401_, 1);
v___x_1403_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1279_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_object* v_a_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1412_; 
v_a_1404_ = lean_ctor_get(v___x_1403_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1406_ = v___x_1403_;
v_isShared_1407_ = v_isSharedCheck_1412_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_a_1404_);
lean_dec(v___x_1403_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1412_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1408_; lean_object* v___x_1410_; 
v___x_1408_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1408_, 0, v_a_1402_);
lean_ctor_set(v___x_1408_, 1, v_a_1404_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 0, v___x_1408_);
v___x_1410_ = v___x_1406_;
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
else
{
lean_dec(v_a_1402_);
return v___x_1403_;
}
}
else
{
lean_dec_ref(v_arg_1279_);
return v___x_1401_;
}
}
}
else
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
lean_dec_ref(v_arg_1285_);
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_e_1267_);
v_a_1413_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___x_1397_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1397_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
}
else
{
lean_object* v___x_1421_; 
lean_dec_ref(v___x_1365_);
v___x_1421_ = l_Lean_Meta_DefEq_isInstHMulInt(v_arg_1345_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; uint8_t v___x_1423_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_a_1422_);
lean_dec_ref_known(v___x_1421_, 1);
v___x_1423_ = lean_unbox(v_a_1422_);
lean_dec(v_a_1422_);
if (v___x_1423_ == 0)
{
lean_object* v___x_1424_; 
lean_dec_ref(v_arg_1285_);
lean_dec_ref(v_arg_1279_);
v___x_1424_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1424_;
}
else
{
v_b_1287_ = v_arg_1279_;
v___y_1288_ = v_a_1268_;
v___y_1289_ = v_a_1269_;
v___y_1290_ = v_a_1270_;
v___y_1291_ = v_a_1271_;
v___y_1292_ = v_a_1272_;
goto v___jp_1286_;
}
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1432_; 
lean_dec_ref(v_arg_1285_);
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_e_1267_);
v_a_1425_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1432_ == 0)
{
v___x_1427_ = v___x_1421_;
v_isShared_1428_ = v_isSharedCheck_1432_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1421_);
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
}
else
{
lean_object* v___x_1433_; 
lean_dec_ref(v___x_1353_);
v___x_1433_ = l_Lean_Meta_DefEq_isInstAddInt(v_arg_1345_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v_a_1434_; uint8_t v___x_1435_; 
v_a_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_a_1434_);
lean_dec_ref_known(v___x_1433_, 1);
v___x_1435_ = lean_unbox(v_a_1434_);
lean_dec(v_a_1434_);
if (v___x_1435_ == 0)
{
lean_object* v___x_1436_; 
lean_dec_ref(v_arg_1285_);
lean_dec_ref(v_arg_1279_);
v___x_1436_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1436_;
}
else
{
lean_object* v___x_1437_; 
lean_dec_ref(v_e_1267_);
v___x_1437_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1285_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1438_; lean_object* v___x_1439_; 
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc(v_a_1438_);
lean_dec_ref_known(v___x_1437_, 1);
v___x_1439_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1279_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1448_; 
v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1442_ = v___x_1439_;
v_isShared_1443_ = v_isSharedCheck_1448_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1439_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1448_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1444_; lean_object* v___x_1446_; 
v___x_1444_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1444_, 0, v_a_1438_);
lean_ctor_set(v___x_1444_, 1, v_a_1440_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 0, v___x_1444_);
v___x_1446_ = v___x_1442_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1444_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
else
{
lean_dec(v_a_1438_);
return v___x_1439_;
}
}
else
{
lean_dec_ref(v_arg_1279_);
return v___x_1437_;
}
}
}
else
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1456_; 
lean_dec_ref(v_arg_1285_);
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_e_1267_);
v_a_1449_ = lean_ctor_get(v___x_1433_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1433_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1451_ = v___x_1433_;
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1433_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
if (v_isShared_1452_ == 0)
{
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_a_1449_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
}
}
else
{
lean_object* v___x_1457_; 
lean_dec_ref(v___x_1353_);
v___x_1457_ = l_Lean_Meta_DefEq_isInstSubInt(v_arg_1345_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; uint8_t v___x_1459_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_a_1458_);
lean_dec_ref_known(v___x_1457_, 1);
v___x_1459_ = lean_unbox(v_a_1458_);
lean_dec(v_a_1458_);
if (v___x_1459_ == 0)
{
lean_object* v___x_1460_; 
lean_dec_ref(v_arg_1285_);
lean_dec_ref(v_arg_1279_);
v___x_1460_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1460_;
}
else
{
lean_object* v___x_1461_; 
lean_dec_ref(v_e_1267_);
v___x_1461_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1285_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v_a_1462_; lean_object* v___x_1463_; 
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
lean_inc(v_a_1462_);
lean_dec_ref_known(v___x_1461_, 1);
v___x_1463_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1279_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1472_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1466_ = v___x_1463_;
v_isShared_1467_ = v_isSharedCheck_1472_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1463_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1472_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1468_; lean_object* v___x_1470_; 
v___x_1468_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1468_, 0, v_a_1462_);
lean_ctor_set(v___x_1468_, 1, v_a_1464_);
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 0, v___x_1468_);
v___x_1470_ = v___x_1466_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___x_1468_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
else
{
lean_dec(v_a_1462_);
return v___x_1463_;
}
}
else
{
lean_dec_ref(v_arg_1279_);
return v___x_1461_;
}
}
}
else
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
lean_dec_ref(v_arg_1285_);
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_e_1267_);
v_a_1473_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1457_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1457_);
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
else
{
lean_object* v___x_1481_; 
lean_dec_ref(v___x_1353_);
v___x_1481_ = l_Lean_Meta_DefEq_isInstMulInt(v_arg_1345_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v_a_1482_; uint8_t v___x_1483_; 
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
lean_inc(v_a_1482_);
lean_dec_ref_known(v___x_1481_, 1);
v___x_1483_ = lean_unbox(v_a_1482_);
lean_dec(v_a_1482_);
if (v___x_1483_ == 0)
{
lean_object* v___x_1484_; 
lean_dec_ref(v_arg_1285_);
lean_dec_ref(v_arg_1279_);
v___x_1484_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1484_;
}
else
{
v_b_1287_ = v_arg_1279_;
v___y_1288_ = v_a_1268_;
v___y_1289_ = v_a_1269_;
v___y_1290_ = v_a_1270_;
v___y_1291_ = v_a_1271_;
v___y_1292_ = v_a_1272_;
goto v___jp_1286_;
}
}
else
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
lean_dec_ref(v_arg_1285_);
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_e_1267_);
v_a_1485_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1487_ = v___x_1481_;
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1481_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1485_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
}
}
else
{
lean_object* v___x_1493_; 
lean_dec_ref(v___x_1346_);
lean_dec_ref(v_arg_1345_);
lean_dec_ref(v_arg_1285_);
lean_dec_ref(v_arg_1279_);
lean_inc_ref(v_e_1267_);
v___x_1493_ = l_Lean_Meta_getIntValue_x3f(v_e_1267_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1510_; 
v_a_1494_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1496_ = v___x_1493_;
v_isShared_1497_ = v_isSharedCheck_1510_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1493_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1510_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
if (lean_obj_tag(v_a_1494_) == 1)
{
lean_object* v_val_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1508_; 
lean_dec_ref(v_e_1267_);
v_val_1498_ = lean_ctor_get(v_a_1494_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v_a_1494_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1500_ = v_a_1494_;
v_isShared_1501_ = v_isSharedCheck_1508_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_val_1498_);
lean_dec(v_a_1494_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1508_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1503_; 
if (v_isShared_1501_ == 0)
{
lean_ctor_set_tag(v___x_1500_, 0);
v___x_1503_ = v___x_1500_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_val_1498_);
v___x_1503_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
lean_object* v___x_1505_; 
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 0, v___x_1503_);
v___x_1505_ = v___x_1496_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1503_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
else
{
lean_object* v___x_1509_; 
lean_del_object(v___x_1496_);
lean_dec(v_a_1494_);
v___x_1509_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1509_;
}
}
}
else
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1518_; 
lean_dec_ref(v_e_1267_);
v_a_1511_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1513_ = v___x_1493_;
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1493_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1514_ == 0)
{
v___x_1516_ = v___x_1513_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1511_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
}
}
else
{
lean_object* v___x_1519_; 
lean_dec_ref(v___x_1346_);
lean_dec_ref(v_arg_1345_);
v___x_1519_ = l_Lean_Meta_DefEq_isInstNegInt(v_arg_1285_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_object* v_a_1520_; uint8_t v___x_1521_; 
v_a_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_a_1520_);
lean_dec_ref_known(v___x_1519_, 1);
v___x_1521_ = lean_unbox(v_a_1520_);
lean_dec(v_a_1520_);
if (v___x_1521_ == 0)
{
lean_object* v___x_1522_; 
lean_dec_ref(v_arg_1279_);
v___x_1522_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1522_;
}
else
{
lean_object* v___x_1523_; 
lean_dec_ref(v_e_1267_);
v___x_1523_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1279_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1532_; 
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1526_ = v___x_1523_;
v_isShared_1527_ = v_isSharedCheck_1532_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_dec(v___x_1523_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1532_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1528_; lean_object* v___x_1530_; 
v___x_1528_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1528_, 0, v_a_1524_);
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 0, v___x_1528_);
v___x_1530_ = v___x_1526_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1528_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
else
{
return v___x_1523_;
}
}
}
else
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1540_; 
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_e_1267_);
v_a_1533_ = lean_ctor_get(v___x_1519_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1535_ = v___x_1519_;
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1519_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1538_; 
if (v_isShared_1536_ == 0)
{
v___x_1538_ = v___x_1535_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_a_1533_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
}
}
}
else
{
lean_object* v___x_1541_; 
lean_dec_ref(v___x_1336_);
lean_dec_ref(v_e_1267_);
v___x_1541_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1285_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; lean_object* v___x_1543_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_a_1542_);
lean_dec_ref_known(v___x_1541_, 1);
v___x_1543_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1279_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1552_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1546_ = v___x_1543_;
v_isShared_1547_ = v_isSharedCheck_1552_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v___x_1543_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1552_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v___x_1548_; lean_object* v___x_1550_; 
v___x_1548_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1548_, 0, v_a_1542_);
lean_ctor_set(v___x_1548_, 1, v_a_1544_);
if (v_isShared_1547_ == 0)
{
lean_ctor_set(v___x_1546_, 0, v___x_1548_);
v___x_1550_ = v___x_1546_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___x_1548_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
else
{
lean_dec(v_a_1542_);
return v___x_1543_;
}
}
else
{
lean_dec_ref(v_arg_1279_);
return v___x_1541_;
}
}
}
else
{
lean_object* v___x_1553_; 
lean_dec_ref(v___x_1336_);
lean_dec_ref(v_e_1267_);
v___x_1553_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1285_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; lean_object* v___x_1555_; 
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_a_1554_);
lean_dec_ref_known(v___x_1553_, 1);
v___x_1555_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1279_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1564_; 
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1558_ = v___x_1555_;
v_isShared_1559_ = v_isSharedCheck_1564_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1555_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1564_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1560_; lean_object* v___x_1562_; 
v___x_1560_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1560_, 0, v_a_1554_);
lean_ctor_set(v___x_1560_, 1, v_a_1556_);
if (v_isShared_1559_ == 0)
{
lean_ctor_set(v___x_1558_, 0, v___x_1560_);
v___x_1562_ = v___x_1558_;
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
}
else
{
lean_dec(v_a_1554_);
return v___x_1555_;
}
}
else
{
lean_dec_ref(v_arg_1279_);
return v___x_1553_;
}
}
}
else
{
lean_dec_ref(v___x_1336_);
v_b_1287_ = v_arg_1279_;
v___y_1288_ = v_a_1268_;
v___y_1289_ = v_a_1269_;
v___y_1290_ = v_a_1270_;
v___y_1291_ = v_a_1271_;
v___y_1292_ = v_a_1272_;
goto v___jp_1286_;
}
v___jp_1286_:
{
lean_object* v___x_1293_; 
lean_inc_ref(v_arg_1285_);
v___x_1293_ = l_Lean_Meta_getIntValue_x3f(v_arg_1285_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_a_1294_);
lean_dec_ref_known(v___x_1293_, 1);
if (lean_obj_tag(v_a_1294_) == 0)
{
lean_object* v___x_1295_; 
v___x_1295_ = l_Lean_Meta_getIntValue_x3f(v_b_1287_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_a_1296_; 
v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
lean_inc(v_a_1296_);
lean_dec_ref_known(v___x_1295_, 1);
if (lean_obj_tag(v_a_1296_) == 0)
{
lean_object* v___x_1297_; 
lean_dec_ref(v_arg_1285_);
v___x_1297_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1267_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
return v___x_1297_;
}
else
{
lean_object* v_val_1298_; lean_object* v___x_1299_; 
lean_dec_ref(v_e_1267_);
v_val_1298_ = lean_ctor_get(v_a_1296_, 0);
lean_inc(v_val_1298_);
lean_dec_ref_known(v_a_1296_, 1);
v___x_1299_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1285_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1308_; 
v_a_1300_ = lean_ctor_get(v___x_1299_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1302_ = v___x_1299_;
v_isShared_1303_ = v_isSharedCheck_1308_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1299_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1308_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1304_; lean_object* v___x_1306_; 
v___x_1304_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_1304_, 0, v_a_1300_);
lean_ctor_set(v___x_1304_, 1, v_val_1298_);
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 0, v___x_1304_);
v___x_1306_ = v___x_1302_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v___x_1304_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
else
{
lean_dec(v_val_1298_);
return v___x_1299_;
}
}
}
else
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
lean_dec_ref(v_arg_1285_);
lean_dec_ref(v_e_1267_);
v_a_1309_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1311_ = v___x_1295_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1295_);
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
lean_object* v_val_1317_; lean_object* v___x_1318_; 
lean_dec_ref(v_arg_1285_);
lean_dec_ref(v_e_1267_);
v_val_1317_ = lean_ctor_get(v_a_1294_, 0);
lean_inc(v_val_1317_);
lean_dec_ref_known(v_a_1294_, 1);
v___x_1318_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_b_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1327_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1321_ = v___x_1318_;
v_isShared_1322_ = v_isSharedCheck_1327_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1318_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1327_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1323_; lean_object* v___x_1325_; 
v___x_1323_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1323_, 0, v_val_1317_);
lean_ctor_set(v___x_1323_, 1, v_a_1319_);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 0, v___x_1323_);
v___x_1325_ = v___x_1321_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v___x_1323_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
else
{
lean_dec(v_val_1317_);
return v___x_1318_;
}
}
}
else
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
lean_dec_ref(v_b_1287_);
lean_dec_ref(v_arg_1285_);
lean_dec_ref(v_e_1267_);
v_a_1328_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1293_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1293_);
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
}
else
{
lean_object* v___x_1565_; 
lean_dec_ref(v___x_1280_);
lean_dec_ref(v_e_1267_);
v___x_1565_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1279_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1574_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1565_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1568_ = v___x_1565_;
v_isShared_1569_ = v_isSharedCheck_1574_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1565_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1574_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1570_; lean_object* v___x_1572_; 
v___x_1570_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_1570_, 0, v_a_1566_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 0, v___x_1570_);
v___x_1572_ = v___x_1568_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1570_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
else
{
return v___x_1565_;
}
}
}
}
else
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
lean_dec_ref(v_e_1267_);
v_a_1575_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1577_ = v___x_1274_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1274_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1578_ == 0)
{
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1575_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(lean_object* v_e_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_){
_start:
{
switch(lean_obj_tag(v_e_1583_))
{
case 10:
{
lean_object* v_expr_1590_; 
v_expr_1590_ = lean_ctor_get(v_e_1583_, 1);
lean_inc_ref(v_expr_1590_);
lean_dec_ref_known(v_e_1583_, 2);
v_e_1583_ = v_expr_1590_;
goto _start;
}
case 5:
{
lean_object* v___x_1592_; 
v___x_1592_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit(v_e_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_);
return v___x_1592_;
}
case 2:
{
lean_object* v___x_1593_; 
v___x_1593_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit(v_e_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_);
return v___x_1593_;
}
default: 
{
lean_object* v___x_1594_; 
v___x_1594_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(v_e_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_);
return v___x_1594_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr___boxed(lean_object* v_e_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_e_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_);
lean_dec(v_a_1600_);
lean_dec_ref(v_a_1599_);
lean_dec(v_a_1598_);
lean_dec_ref(v_a_1597_);
lean_dec(v_a_1596_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___boxed(lean_object* v_e_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit(v_e_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_);
lean_dec(v_a_1608_);
lean_dec_ref(v_a_1607_);
lean_dec(v_a_1606_);
lean_dec_ref(v_a_1605_);
lean_dec(v_a_1604_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f(lean_object* v_e_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1614_, v_a_1617_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1710_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1624_ = v___x_1621_;
v_isShared_1625_ = v_isSharedCheck_1710_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1621_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1710_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1631_; uint8_t v___x_1632_; 
v___x_1631_ = l_Lean_Expr_cleanupAnnotations(v_a_1622_);
v___x_1632_ = l_Lean_Expr_isApp(v___x_1631_);
if (v___x_1632_ == 0)
{
lean_dec_ref(v___x_1631_);
goto v___jp_1626_;
}
else
{
lean_object* v_arg_1633_; lean_object* v___x_1634_; uint8_t v___x_1635_; 
v_arg_1633_ = lean_ctor_get(v___x_1631_, 1);
lean_inc_ref(v_arg_1633_);
v___x_1634_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1631_);
v___x_1635_ = l_Lean_Expr_isApp(v___x_1634_);
if (v___x_1635_ == 0)
{
lean_dec_ref(v___x_1634_);
lean_dec_ref(v_arg_1633_);
goto v___jp_1626_;
}
else
{
lean_object* v_arg_1636_; lean_object* v___x_1637_; uint8_t v___x_1638_; 
v_arg_1636_ = lean_ctor_get(v___x_1634_, 1);
lean_inc_ref(v_arg_1636_);
v___x_1637_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1634_);
v___x_1638_ = l_Lean_Expr_isApp(v___x_1637_);
if (v___x_1638_ == 0)
{
lean_dec_ref(v___x_1637_);
lean_dec_ref(v_arg_1636_);
lean_dec_ref(v_arg_1633_);
goto v___jp_1626_;
}
else
{
lean_object* v_arg_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; uint8_t v___x_1642_; 
v_arg_1639_ = lean_ctor_get(v___x_1637_, 1);
lean_inc_ref(v_arg_1639_);
v___x_1640_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1637_);
v___x_1641_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___closed__1));
v___x_1642_ = l_Lean_Expr_isConstOf(v___x_1640_, v___x_1641_);
lean_dec_ref(v___x_1640_);
if (v___x_1642_ == 0)
{
lean_dec_ref(v_arg_1639_);
lean_dec_ref(v_arg_1636_);
lean_dec_ref(v_arg_1633_);
goto v___jp_1626_;
}
else
{
lean_object* v___x_1643_; 
lean_del_object(v___x_1624_);
v___x_1643_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1639_, v_a_1617_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1701_; 
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1646_ = v___x_1643_;
v_isShared_1647_ = v_isSharedCheck_1701_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1643_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1701_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; uint8_t v___x_1650_; 
v___x_1648_ = l_Lean_Expr_cleanupAnnotations(v_a_1644_);
v___x_1649_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13));
v___x_1650_ = l_Lean_Expr_isConstOf(v___x_1648_, v___x_1649_);
lean_dec_ref(v___x_1648_);
if (v___x_1650_ == 0)
{
lean_object* v___x_1651_; lean_object* v___x_1653_; 
lean_dec_ref(v_arg_1636_);
lean_dec_ref(v_arg_1633_);
v___x_1651_ = lean_box(0);
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 0, v___x_1651_);
v___x_1653_ = v___x_1646_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1651_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
else
{
lean_object* v___x_1655_; 
lean_del_object(v___x_1646_);
v___x_1655_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1636_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1692_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1658_ = v___x_1655_;
v_isShared_1659_ = v_isSharedCheck_1692_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1655_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1692_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1660_; 
v___x_1660_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1633_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1683_; 
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1663_ = v___x_1660_;
v_isShared_1664_ = v_isSharedCheck_1683_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1660_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1683_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
switch(lean_obj_tag(v_a_1656_))
{
case 1:
{
switch(lean_obj_tag(v_a_1661_))
{
case 1:
{
lean_object* v___x_1671_; lean_object* v___x_1673_; 
lean_dec_ref_known(v_a_1661_, 1);
lean_dec_ref_known(v_a_1656_, 1);
lean_del_object(v___x_1663_);
v___x_1671_ = lean_box(0);
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 0, v___x_1671_);
v___x_1673_ = v___x_1658_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1671_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
case 0:
{
lean_object* v___x_1675_; lean_object* v___x_1677_; 
lean_dec_ref_known(v_a_1661_, 1);
lean_dec_ref_known(v_a_1656_, 1);
lean_del_object(v___x_1663_);
v___x_1675_ = lean_box(0);
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 0, v___x_1675_);
v___x_1677_ = v___x_1658_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1675_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
default: 
{
lean_del_object(v___x_1658_);
goto v___jp_1665_;
}
}
}
case 0:
{
if (lean_obj_tag(v_a_1661_) == 1)
{
lean_object* v___x_1679_; lean_object* v___x_1681_; 
lean_dec_ref_known(v_a_1661_, 1);
lean_dec_ref_known(v_a_1656_, 1);
lean_del_object(v___x_1663_);
v___x_1679_ = lean_box(0);
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 0, v___x_1679_);
v___x_1681_ = v___x_1658_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1679_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
else
{
lean_del_object(v___x_1658_);
goto v___jp_1665_;
}
}
default: 
{
lean_del_object(v___x_1658_);
goto v___jp_1665_;
}
}
v___jp_1665_:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1669_; 
v___x_1666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1666_, 0, v_a_1656_);
lean_ctor_set(v___x_1666_, 1, v_a_1661_);
v___x_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1666_);
if (v_isShared_1664_ == 0)
{
lean_ctor_set(v___x_1663_, 0, v___x_1667_);
v___x_1669_ = v___x_1663_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v___x_1667_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
else
{
lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1691_; 
lean_del_object(v___x_1658_);
lean_dec(v_a_1656_);
v_a_1684_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1686_ = v___x_1660_;
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_dec(v___x_1660_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1689_; 
if (v_isShared_1687_ == 0)
{
v___x_1689_ = v___x_1686_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_a_1684_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
}
}
else
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
lean_dec_ref(v_arg_1633_);
v_a_1693_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v___x_1655_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1655_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1693_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
}
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
lean_dec_ref(v_arg_1636_);
lean_dec_ref(v_arg_1633_);
v_a_1702_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1643_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1643_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1702_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
}
}
}
v___jp_1626_:
{
lean_object* v___x_1627_; lean_object* v___x_1629_; 
v___x_1627_ = lean_box(0);
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 0, v___x_1627_);
v___x_1629_ = v___x_1624_;
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
lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1718_; 
v_a_1711_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1713_ = v___x_1621_;
v_isShared_1714_ = v_isSharedCheck_1718_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1621_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___boxed(lean_object* v_e_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f(v_e_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_);
lean_dec(v_a_1724_);
lean_dec_ref(v_a_1723_);
lean_dec(v_a_1722_);
lean_dec_ref(v_a_1721_);
lean_dec(v_a_1720_);
return v_res_1726_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14(void){
_start:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1753_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__0);
v___x_1754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f(lean_object* v_e_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1755_, v_a_1758_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_2052_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_1765_ = v___x_1762_;
v_isShared_1766_ = v_isSharedCheck_2052_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1762_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_2052_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1772_; uint8_t v___x_1773_; 
v___x_1772_ = l_Lean_Expr_cleanupAnnotations(v_a_1763_);
v___x_1773_ = l_Lean_Expr_isApp(v___x_1772_);
if (v___x_1773_ == 0)
{
lean_dec_ref(v___x_1772_);
goto v___jp_1767_;
}
else
{
lean_object* v_arg_1774_; lean_object* v___x_1775_; uint8_t v___x_1776_; 
v_arg_1774_ = lean_ctor_get(v___x_1772_, 1);
lean_inc_ref(v_arg_1774_);
v___x_1775_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1772_);
v___x_1776_ = l_Lean_Expr_isApp(v___x_1775_);
if (v___x_1776_ == 0)
{
lean_dec_ref(v___x_1775_);
lean_dec_ref(v_arg_1774_);
goto v___jp_1767_;
}
else
{
lean_object* v_arg_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; uint8_t v___x_1780_; 
v_arg_1777_ = lean_ctor_get(v___x_1775_, 1);
lean_inc_ref(v_arg_1777_);
v___x_1778_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1775_);
v___x_1779_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__1));
v___x_1780_ = l_Lean_Expr_isConstOf(v___x_1778_, v___x_1779_);
if (v___x_1780_ == 0)
{
lean_object* v___x_1781_; uint8_t v___x_1782_; 
v___x_1781_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__3));
v___x_1782_ = l_Lean_Expr_isConstOf(v___x_1778_, v___x_1781_);
if (v___x_1782_ == 0)
{
uint8_t v___x_1783_; 
v___x_1783_ = l_Lean_Expr_isApp(v___x_1778_);
if (v___x_1783_ == 0)
{
lean_dec_ref(v___x_1778_);
lean_dec_ref(v_arg_1777_);
lean_dec_ref(v_arg_1774_);
goto v___jp_1767_;
}
else
{
lean_object* v_arg_1784_; lean_object* v___x_1785_; uint8_t v___x_1786_; 
v_arg_1784_ = lean_ctor_get(v___x_1778_, 1);
lean_inc_ref(v_arg_1784_);
v___x_1785_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1778_);
v___x_1786_ = l_Lean_Expr_isApp(v___x_1785_);
if (v___x_1786_ == 0)
{
lean_dec_ref(v___x_1785_);
lean_dec_ref(v_arg_1784_);
lean_dec_ref(v_arg_1777_);
lean_dec_ref(v_arg_1774_);
goto v___jp_1767_;
}
else
{
lean_object* v___x_1787_; lean_object* v___x_1788_; uint8_t v___x_1789_; 
v___x_1787_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1785_);
v___x_1788_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__6));
v___x_1789_ = l_Lean_Expr_isConstOf(v___x_1787_, v___x_1788_);
if (v___x_1789_ == 0)
{
lean_object* v___x_1790_; uint8_t v___x_1791_; 
v___x_1790_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__9));
v___x_1791_ = l_Lean_Expr_isConstOf(v___x_1787_, v___x_1790_);
if (v___x_1791_ == 0)
{
lean_object* v___x_1792_; uint8_t v___x_1793_; 
v___x_1792_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__11));
v___x_1793_ = l_Lean_Expr_isConstOf(v___x_1787_, v___x_1792_);
if (v___x_1793_ == 0)
{
lean_object* v___x_1794_; uint8_t v___x_1795_; 
v___x_1794_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__13));
v___x_1795_ = l_Lean_Expr_isConstOf(v___x_1787_, v___x_1794_);
lean_dec_ref(v___x_1787_);
if (v___x_1795_ == 0)
{
lean_dec_ref(v_arg_1784_);
lean_dec_ref(v_arg_1777_);
lean_dec_ref(v_arg_1774_);
goto v___jp_1767_;
}
else
{
lean_object* v___x_1796_; 
lean_del_object(v___x_1765_);
v___x_1796_ = l_Lean_Meta_DefEq_isInstLEInt(v_arg_1784_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1835_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1799_ = v___x_1796_;
v_isShared_1800_ = v_isSharedCheck_1835_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1796_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1835_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
uint8_t v___x_1801_; 
v___x_1801_ = lean_unbox(v_a_1797_);
lean_dec(v_a_1797_);
if (v___x_1801_ == 0)
{
lean_object* v___x_1802_; lean_object* v___x_1804_; 
lean_dec_ref(v_arg_1777_);
lean_dec_ref(v_arg_1774_);
v___x_1802_ = lean_box(0);
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 0, v___x_1802_);
v___x_1804_ = v___x_1799_;
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
else
{
lean_object* v___x_1806_; 
lean_del_object(v___x_1799_);
v___x_1806_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1777_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v_a_1807_; lean_object* v___x_1808_; 
v_a_1807_ = lean_ctor_get(v___x_1806_, 0);
lean_inc(v_a_1807_);
lean_dec_ref_known(v___x_1806_, 1);
v___x_1808_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1774_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1818_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1811_ = v___x_1808_;
v_isShared_1812_ = v_isSharedCheck_1818_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1808_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1818_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1816_; 
v___x_1813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1813_, 0, v_a_1807_);
lean_ctor_set(v___x_1813_, 1, v_a_1809_);
v___x_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1813_);
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 0, v___x_1814_);
v___x_1816_ = v___x_1811_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v___x_1814_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
else
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1826_; 
lean_dec(v_a_1807_);
v_a_1819_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1821_ = v___x_1808_;
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1808_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1824_; 
if (v_isShared_1822_ == 0)
{
v___x_1824_ = v___x_1821_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_a_1819_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
}
else
{
lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1834_; 
lean_dec_ref(v_arg_1774_);
v_a_1827_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1829_ = v___x_1806_;
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_dec(v___x_1806_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1832_; 
if (v_isShared_1830_ == 0)
{
v___x_1832_ = v___x_1829_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_a_1827_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
}
}
}
}
else
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1843_; 
lean_dec_ref(v_arg_1777_);
lean_dec_ref(v_arg_1774_);
v_a_1836_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1838_ = v___x_1796_;
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1796_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1839_ == 0)
{
v___x_1841_ = v___x_1838_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_a_1836_);
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
}
else
{
lean_object* v___x_1844_; 
lean_dec_ref(v___x_1787_);
lean_del_object(v___x_1765_);
v___x_1844_ = l_Lean_Meta_DefEq_isInstLTInt(v_arg_1784_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v_a_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1885_; 
v_a_1845_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1847_ = v___x_1844_;
v_isShared_1848_ = v_isSharedCheck_1885_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v___x_1844_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1885_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
uint8_t v___x_1849_; 
v___x_1849_ = lean_unbox(v_a_1845_);
lean_dec(v_a_1845_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1850_; lean_object* v___x_1852_; 
lean_dec_ref(v_arg_1777_);
lean_dec_ref(v_arg_1774_);
v___x_1850_ = lean_box(0);
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 0, v___x_1850_);
v___x_1852_ = v___x_1847_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1850_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
else
{
lean_object* v___x_1854_; 
lean_del_object(v___x_1847_);
v___x_1854_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1777_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_object* v_a_1855_; lean_object* v___x_1856_; 
v_a_1855_ = lean_ctor_get(v___x_1854_, 0);
lean_inc(v_a_1855_);
lean_dec_ref_known(v___x_1854_, 1);
v___x_1856_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1774_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1868_; 
v_a_1857_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1859_ = v___x_1856_;
v_isShared_1860_ = v_isSharedCheck_1868_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1856_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1868_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1866_; 
v___x_1861_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14, &l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14);
v___x_1862_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1862_, 0, v_a_1855_);
lean_ctor_set(v___x_1862_, 1, v___x_1861_);
v___x_1863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1862_);
lean_ctor_set(v___x_1863_, 1, v_a_1857_);
v___x_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1863_);
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
}
else
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
lean_dec(v_a_1855_);
v_a_1869_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1871_ = v___x_1856_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1856_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1869_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
lean_dec_ref(v_arg_1774_);
v_a_1877_ = lean_ctor_get(v___x_1854_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1854_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1854_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
}
}
else
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1893_; 
lean_dec_ref(v_arg_1777_);
lean_dec_ref(v_arg_1774_);
v_a_1886_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1888_ = v___x_1844_;
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1844_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1891_; 
if (v_isShared_1889_ == 0)
{
v___x_1891_ = v___x_1888_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1886_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
}
}
else
{
lean_object* v___x_1894_; 
lean_dec_ref(v___x_1787_);
lean_del_object(v___x_1765_);
v___x_1894_ = l_Lean_Meta_DefEq_isInstLEInt(v_arg_1784_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1933_; 
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1897_ = v___x_1894_;
v_isShared_1898_ = v_isSharedCheck_1933_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1894_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1933_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
uint8_t v___x_1899_; 
v___x_1899_ = lean_unbox(v_a_1895_);
lean_dec(v_a_1895_);
if (v___x_1899_ == 0)
{
lean_object* v___x_1900_; lean_object* v___x_1902_; 
lean_dec_ref(v_arg_1777_);
lean_dec_ref(v_arg_1774_);
v___x_1900_ = lean_box(0);
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 0, v___x_1900_);
v___x_1902_ = v___x_1897_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v___x_1900_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
else
{
lean_object* v___x_1904_; 
lean_del_object(v___x_1897_);
v___x_1904_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1774_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v___x_1906_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
lean_inc(v_a_1905_);
lean_dec_ref_known(v___x_1904_, 1);
v___x_1906_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1777_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1916_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1909_ = v___x_1906_;
v_isShared_1910_ = v_isSharedCheck_1916_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1906_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1916_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1914_; 
v___x_1911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1911_, 0, v_a_1905_);
lean_ctor_set(v___x_1911_, 1, v_a_1907_);
v___x_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1911_);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 0, v___x_1912_);
v___x_1914_ = v___x_1909_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v___x_1912_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
lean_dec(v_a_1905_);
v_a_1917_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1906_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1906_);
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
else
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1932_; 
lean_dec_ref(v_arg_1777_);
v_a_1925_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1927_ = v___x_1904_;
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1904_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1930_; 
if (v_isShared_1928_ == 0)
{
v___x_1930_ = v___x_1927_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_a_1925_);
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
}
}
else
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
lean_dec_ref(v_arg_1777_);
lean_dec_ref(v_arg_1774_);
v_a_1934_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1936_ = v___x_1894_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1894_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
if (v_isShared_1937_ == 0)
{
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1934_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
}
}
}
else
{
lean_object* v___x_1942_; 
lean_dec_ref(v___x_1787_);
lean_del_object(v___x_1765_);
v___x_1942_ = l_Lean_Meta_DefEq_isInstLTInt(v_arg_1784_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1983_; 
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1945_ = v___x_1942_;
v_isShared_1946_ = v_isSharedCheck_1983_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1942_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1983_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
uint8_t v___x_1947_; 
v___x_1947_ = lean_unbox(v_a_1943_);
lean_dec(v_a_1943_);
if (v___x_1947_ == 0)
{
lean_object* v___x_1948_; lean_object* v___x_1950_; 
lean_dec_ref(v_arg_1777_);
lean_dec_ref(v_arg_1774_);
v___x_1948_ = lean_box(0);
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 0, v___x_1948_);
v___x_1950_ = v___x_1945_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v___x_1948_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
else
{
lean_object* v___x_1952_; 
lean_del_object(v___x_1945_);
v___x_1952_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1774_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v_a_1953_; lean_object* v___x_1954_; 
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_a_1953_);
lean_dec_ref_known(v___x_1952_, 1);
v___x_1954_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1777_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1966_; 
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1957_ = v___x_1954_;
v_isShared_1958_ = v_isSharedCheck_1966_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1954_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1966_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1964_; 
v___x_1959_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14, &l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14);
v___x_1960_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1960_, 0, v_a_1953_);
lean_ctor_set(v___x_1960_, 1, v___x_1959_);
v___x_1961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1960_);
lean_ctor_set(v___x_1961_, 1, v_a_1955_);
v___x_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1961_);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 0, v___x_1962_);
v___x_1964_ = v___x_1957_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1962_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
else
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1974_; 
lean_dec(v_a_1953_);
v_a_1967_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1969_ = v___x_1954_;
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1954_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_a_1967_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
else
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
lean_dec_ref(v_arg_1777_);
v_a_1975_ = lean_ctor_get(v___x_1952_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1977_ = v___x_1952_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1952_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1975_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
}
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1991_; 
lean_dec_ref(v_arg_1777_);
lean_dec_ref(v_arg_1774_);
v_a_1984_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1986_ = v___x_1942_;
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1942_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
if (v_isShared_1987_ == 0)
{
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1984_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1992_; 
lean_dec_ref(v___x_1778_);
lean_del_object(v___x_1765_);
v___x_1992_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1777_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v_a_1993_; lean_object* v___x_1994_; 
v_a_1993_ = lean_ctor_get(v___x_1992_, 0);
lean_inc(v_a_1993_);
lean_dec_ref_known(v___x_1992_, 1);
v___x_1994_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1774_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2004_; 
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1997_ = v___x_1994_;
v_isShared_1998_ = v_isSharedCheck_2004_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1994_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2004_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2002_; 
v___x_1999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1999_, 0, v_a_1993_);
lean_ctor_set(v___x_1999_, 1, v_a_1995_);
v___x_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2000_, 0, v___x_1999_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v___x_2000_);
v___x_2002_ = v___x_1997_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_2000_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
else
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2012_; 
lean_dec(v_a_1993_);
v_a_2005_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2007_ = v___x_1994_;
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_1994_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2010_; 
if (v_isShared_2008_ == 0)
{
v___x_2010_ = v___x_2007_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_a_2005_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
}
else
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
lean_dec_ref(v_arg_1774_);
v_a_2013_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2015_ = v___x_1992_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_1992_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2013_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
}
else
{
lean_object* v___x_2021_; 
lean_dec_ref(v___x_1778_);
lean_del_object(v___x_1765_);
v___x_2021_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1777_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; lean_object* v___x_2023_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_a_2022_);
lean_dec_ref_known(v___x_2021_, 1);
v___x_2023_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_1774_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_);
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
lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2033_; 
v___x_2028_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14, &l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14_once, _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14);
v___x_2029_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2029_, 0, v_a_2022_);
lean_ctor_set(v___x_2029_, 1, v___x_2028_);
v___x_2030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2029_);
lean_ctor_set(v___x_2030_, 1, v_a_2024_);
v___x_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2030_);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 0, v___x_2031_);
v___x_2033_ = v___x_2026_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2031_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
else
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2043_; 
lean_dec(v_a_2022_);
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
else
{
lean_object* v_a_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2051_; 
lean_dec_ref(v_arg_1774_);
v_a_2044_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2046_ = v___x_2021_;
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_a_2044_);
lean_dec(v___x_2021_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2049_; 
if (v_isShared_2047_ == 0)
{
v___x_2049_ = v___x_2046_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_a_2044_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
}
}
}
v___jp_1767_:
{
lean_object* v___x_1768_; lean_object* v___x_1770_; 
v___x_1768_ = lean_box(0);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 0, v___x_1768_);
v___x_1770_ = v___x_1765_;
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
}
else
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
v_a_2053_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___x_1762_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_1762_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___boxed(lean_object* v_e_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f(v_e_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_);
lean_dec(v_a_2066_);
lean_dec_ref(v_a_2065_);
lean_dec(v_a_2064_);
lean_dec_ref(v_a_2063_);
lean_dec(v_a_2062_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f(lean_object* v_e_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_){
_start:
{
lean_object* v___x_2081_; 
v___x_2081_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2074_, v_a_2077_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2168_; 
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2084_ = v___x_2081_;
v_isShared_2085_ = v_isSharedCheck_2168_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2081_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2168_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2091_; uint8_t v___x_2092_; 
v___x_2091_ = l_Lean_Expr_cleanupAnnotations(v_a_2082_);
v___x_2092_ = l_Lean_Expr_isApp(v___x_2091_);
if (v___x_2092_ == 0)
{
lean_dec_ref(v___x_2091_);
goto v___jp_2086_;
}
else
{
lean_object* v_arg_2093_; lean_object* v___x_2094_; uint8_t v___x_2095_; 
v_arg_2093_ = lean_ctor_get(v___x_2091_, 1);
lean_inc_ref(v_arg_2093_);
v___x_2094_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2091_);
v___x_2095_ = l_Lean_Expr_isApp(v___x_2094_);
if (v___x_2095_ == 0)
{
lean_dec_ref(v___x_2094_);
lean_dec_ref(v_arg_2093_);
goto v___jp_2086_;
}
else
{
lean_object* v_arg_2096_; lean_object* v___x_2097_; uint8_t v___x_2098_; 
v_arg_2096_ = lean_ctor_get(v___x_2094_, 1);
lean_inc_ref(v_arg_2096_);
v___x_2097_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2094_);
v___x_2098_ = l_Lean_Expr_isApp(v___x_2097_);
if (v___x_2098_ == 0)
{
lean_dec_ref(v___x_2097_);
lean_dec_ref(v_arg_2096_);
lean_dec_ref(v_arg_2093_);
goto v___jp_2086_;
}
else
{
lean_object* v_arg_2099_; lean_object* v___x_2100_; uint8_t v___x_2101_; 
v_arg_2099_ = lean_ctor_get(v___x_2097_, 1);
lean_inc_ref(v_arg_2099_);
v___x_2100_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2097_);
v___x_2101_ = l_Lean_Expr_isApp(v___x_2100_);
if (v___x_2101_ == 0)
{
lean_dec_ref(v___x_2100_);
lean_dec_ref(v_arg_2099_);
lean_dec_ref(v_arg_2096_);
lean_dec_ref(v_arg_2093_);
goto v___jp_2086_;
}
else
{
lean_object* v___x_2102_; lean_object* v___x_2103_; uint8_t v___x_2104_; 
v___x_2102_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2100_);
v___x_2103_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__2));
v___x_2104_ = l_Lean_Expr_isConstOf(v___x_2102_, v___x_2103_);
lean_dec_ref(v___x_2102_);
if (v___x_2104_ == 0)
{
lean_dec_ref(v_arg_2099_);
lean_dec_ref(v_arg_2096_);
lean_dec_ref(v_arg_2093_);
goto v___jp_2086_;
}
else
{
lean_object* v___x_2105_; 
lean_del_object(v___x_2084_);
v___x_2105_ = l_Lean_Meta_DefEq_isInstDvdInt(v_arg_2099_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2159_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2108_ = v___x_2105_;
v_isShared_2109_ = v_isSharedCheck_2159_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2105_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2159_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
uint8_t v___x_2110_; 
v___x_2110_ = lean_unbox(v_a_2106_);
lean_dec(v_a_2106_);
if (v___x_2110_ == 0)
{
lean_object* v___x_2111_; lean_object* v___x_2113_; 
lean_dec_ref(v_arg_2096_);
lean_dec_ref(v_arg_2093_);
v___x_2111_ = lean_box(0);
if (v_isShared_2109_ == 0)
{
lean_ctor_set(v___x_2108_, 0, v___x_2111_);
v___x_2113_ = v___x_2108_;
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
else
{
lean_object* v___x_2115_; 
lean_del_object(v___x_2108_);
v___x_2115_ = l_Lean_Meta_getIntValue_x3f(v_arg_2096_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2150_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2118_ = v___x_2115_;
v_isShared_2119_ = v_isSharedCheck_2150_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___x_2115_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2150_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
if (lean_obj_tag(v_a_2116_) == 1)
{
lean_object* v_val_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2145_; 
lean_del_object(v___x_2118_);
v_val_2120_ = lean_ctor_get(v_a_2116_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v_a_2116_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2122_ = v_a_2116_;
v_isShared_2123_ = v_isSharedCheck_2145_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_val_2120_);
lean_dec(v_a_2116_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2145_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2124_; 
v___x_2124_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(v_arg_2093_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2136_; 
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2127_ = v___x_2124_;
v_isShared_2128_ = v_isSharedCheck_2136_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2124_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2136_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2129_; lean_object* v___x_2131_; 
v___x_2129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2129_, 0, v_val_2120_);
lean_ctor_set(v___x_2129_, 1, v_a_2125_);
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 0, v___x_2129_);
v___x_2131_ = v___x_2122_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v___x_2129_);
v___x_2131_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
lean_object* v___x_2133_; 
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 0, v___x_2131_);
v___x_2133_ = v___x_2127_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v___x_2131_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
lean_del_object(v___x_2122_);
lean_dec(v_val_2120_);
v_a_2137_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2124_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2124_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2137_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
}
else
{
lean_object* v___x_2146_; lean_object* v___x_2148_; 
lean_dec(v_a_2116_);
lean_dec_ref(v_arg_2093_);
v___x_2146_ = lean_box(0);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 0, v___x_2146_);
v___x_2148_ = v___x_2118_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v___x_2146_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
lean_dec_ref(v_arg_2093_);
v_a_2151_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2115_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2115_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2151_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
}
}
else
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2167_; 
lean_dec_ref(v_arg_2096_);
lean_dec_ref(v_arg_2093_);
v_a_2160_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2162_ = v___x_2105_;
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2105_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2165_; 
if (v_isShared_2163_ == 0)
{
v___x_2165_ = v___x_2162_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_a_2160_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
}
}
}
}
}
v___jp_2086_:
{
lean_object* v___x_2087_; lean_object* v___x_2089_; 
v___x_2087_ = lean_box(0);
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 0, v___x_2087_);
v___x_2089_ = v___x_2084_;
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
else
{
lean_object* v_a_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2176_; 
v_a_2169_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2171_ = v___x_2081_;
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_a_2169_);
lean_dec(v___x_2081_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2174_; 
if (v_isShared_2172_ == 0)
{
v___x_2174_ = v___x_2171_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_a_2169_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___boxed(lean_object* v_e_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f(v_e_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_);
lean_dec(v_a_2182_);
lean_dec_ref(v_a_2181_);
lean_dec(v_a_2180_);
lean_dec_ref(v_a_2179_);
lean_dec(v_a_2178_);
return v_res_2184_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_2185_; 
v___x_2185_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2185_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2186_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__0, &l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__0_once, _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__0);
v___x_2187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2186_);
return v___x_2187_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__3(void){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2190_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__2));
v___x_2191_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__1, &l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__1_once, _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__1);
v___x_2192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2191_);
lean_ctor_set(v___x_2192_, 1, v___x_2190_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(lean_object* v_x_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_){
_start:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2199_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__3, &l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__3);
v___x_2200_ = lean_st_mk_ref(v___x_2199_);
lean_inc(v_a_2197_);
lean_inc_ref(v_a_2196_);
lean_inc(v_a_2195_);
lean_inc_ref(v_a_2194_);
lean_inc(v___x_2200_);
v___x_2201_ = lean_apply_6(v_x_2193_, v___x_2200_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, lean_box(0));
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2219_; 
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2204_ = v___x_2201_;
v_isShared_2205_ = v_isSharedCheck_2219_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_2201_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2219_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2206_; lean_object* v_vars_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2217_; 
v___x_2206_ = lean_st_ref_get(v___x_2200_);
lean_dec(v___x_2200_);
v_vars_2207_ = lean_ctor_get(v___x_2206_, 1);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2217_ == 0)
{
lean_object* v_unused_2218_; 
v_unused_2218_ = lean_ctor_get(v___x_2206_, 0);
lean_dec(v_unused_2218_);
v___x_2209_ = v___x_2206_;
v_isShared_2210_ = v_isSharedCheck_2217_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_vars_2207_);
lean_dec(v___x_2206_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2217_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2212_; 
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 0, v_a_2202_);
v___x_2212_ = v___x_2209_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2202_);
lean_ctor_set(v_reuseFailAlloc_2216_, 1, v_vars_2207_);
v___x_2212_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
lean_object* v___x_2214_; 
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 0, v___x_2212_);
v___x_2214_ = v___x_2204_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v___x_2212_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
}
}
else
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
lean_dec(v___x_2200_);
v_a_2220_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2222_ = v___x_2201_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2201_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2223_ == 0)
{
v___x_2225_ = v___x_2222_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2220_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___boxed(lean_object* v_x_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_){
_start:
{
lean_object* v_res_2234_; 
v_res_2234_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(v_x_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_);
lean_dec(v_a_2232_);
lean_dec_ref(v_a_2231_);
lean_dec(v_a_2230_);
lean_dec_ref(v_a_2229_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run(lean_object* v_00_u03b1_2235_, lean_object* v_x_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_){
_start:
{
lean_object* v___x_2242_; 
v___x_2242_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(v_x_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run___boxed(lean_object* v_00_u03b1_2243_, lean_object* v_x_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run(v_00_u03b1_2243_, v_x_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_);
lean_dec(v_a_2248_);
lean_dec_ref(v_a_2247_);
lean_dec(v_a_2246_);
lean_dec_ref(v_a_2245_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toLinearExpr(lean_object* v_e_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_){
_start:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2257_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr___boxed), 7, 1);
lean_closure_set(v___x_2257_, 0, v_e_2251_);
v___x_2258_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(v___x_2257_, v_a_2252_, v_a_2253_, v_a_2254_, v_a_2255_);
if (lean_obj_tag(v___x_2258_) == 0)
{
lean_object* v_a_2259_; lean_object* v_fst_2260_; lean_object* v_snd_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; uint8_t v___x_2264_; 
v_a_2259_ = lean_ctor_get(v___x_2258_, 0);
lean_inc(v_a_2259_);
v_fst_2260_ = lean_ctor_get(v_a_2259_, 0);
lean_inc(v_fst_2260_);
v_snd_2261_ = lean_ctor_get(v_a_2259_, 1);
lean_inc(v_snd_2261_);
lean_dec(v_a_2259_);
v___x_2262_ = lean_array_get_size(v_snd_2261_);
v___x_2263_ = lean_unsigned_to_nat(1u);
v___x_2264_ = lean_nat_dec_eq(v___x_2262_, v___x_2263_);
if (v___x_2264_ == 0)
{
lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2282_; 
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2282_ == 0)
{
lean_object* v_unused_2283_; 
v_unused_2283_ = lean_ctor_get(v___x_2258_, 0);
lean_dec(v_unused_2283_);
v___x_2266_ = v___x_2258_;
v_isShared_2267_ = v_isSharedCheck_2282_;
goto v_resetjp_2265_;
}
else
{
lean_dec(v___x_2258_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2282_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2268_; lean_object* v_fst_2269_; lean_object* v_snd_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2281_; 
v___x_2268_ = l_Lean_sortExprs(v_snd_2261_, v___x_2264_);
v_fst_2269_ = lean_ctor_get(v___x_2268_, 0);
v_snd_2270_ = lean_ctor_get(v___x_2268_, 1);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2272_ = v___x_2268_;
v_isShared_2273_ = v_isSharedCheck_2281_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_snd_2270_);
lean_inc(v_fst_2269_);
lean_dec(v___x_2268_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2281_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2274_; lean_object* v___x_2276_; 
v___x_2274_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_snd_2270_, v_fst_2260_);
lean_dec(v_snd_2270_);
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 1, v_fst_2269_);
lean_ctor_set(v___x_2272_, 0, v___x_2274_);
v___x_2276_ = v___x_2272_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___x_2274_);
lean_ctor_set(v_reuseFailAlloc_2280_, 1, v_fst_2269_);
v___x_2276_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
lean_object* v___x_2278_; 
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 0, v___x_2276_);
v___x_2278_ = v___x_2266_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v___x_2276_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
}
}
else
{
lean_dec(v_snd_2261_);
lean_dec(v_fst_2260_);
return v___x_2258_;
}
}
else
{
return v___x_2258_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toLinearExpr___boxed(lean_object* v_e_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_){
_start:
{
lean_object* v_res_2290_; 
v_res_2290_ = l_Lean_Meta_Simp_Arith_Int_toLinearExpr(v_e_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_);
lean_dec(v_a_2288_);
lean_dec_ref(v_a_2287_);
lean_dec(v_a_2286_);
lean_dec_ref(v_a_2285_);
return v_res_2290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_adapter(lean_object* v_e_2291_, lean_object* v_k_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_){
_start:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2298_ = lean_apply_1(v_k_2292_, v_e_2291_);
v___x_2299_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(v___x_2298_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2362_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2302_ = v___x_2299_;
v_isShared_2303_ = v_isSharedCheck_2362_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v___x_2299_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2362_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v_fst_2304_; 
v_fst_2304_ = lean_ctor_get(v_a_2300_, 0);
lean_inc(v_fst_2304_);
if (lean_obj_tag(v_fst_2304_) == 1)
{
lean_object* v_val_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2357_; 
v_val_2305_ = lean_ctor_get(v_fst_2304_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v_fst_2304_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2307_ = v_fst_2304_;
v_isShared_2308_ = v_isSharedCheck_2357_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_val_2305_);
lean_dec(v_fst_2304_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2357_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v_snd_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2355_; 
v_snd_2309_ = lean_ctor_get(v_a_2300_, 1);
v_isSharedCheck_2355_ = !lean_is_exclusive(v_a_2300_);
if (v_isSharedCheck_2355_ == 0)
{
lean_object* v_unused_2356_; 
v_unused_2356_ = lean_ctor_get(v_a_2300_, 0);
lean_dec(v_unused_2356_);
v___x_2311_ = v_a_2300_;
v_isShared_2312_ = v_isSharedCheck_2355_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_snd_2309_);
lean_dec(v_a_2300_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2355_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v_fst_2313_; lean_object* v_snd_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2354_; 
v_fst_2313_ = lean_ctor_get(v_val_2305_, 0);
v_snd_2314_ = lean_ctor_get(v_val_2305_, 1);
v_isSharedCheck_2354_ = !lean_is_exclusive(v_val_2305_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2316_ = v_val_2305_;
v_isShared_2317_ = v_isSharedCheck_2354_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_snd_2314_);
lean_inc(v_fst_2313_);
lean_dec(v_val_2305_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2354_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; uint8_t v___x_2320_; 
v___x_2318_ = lean_array_get_size(v_snd_2309_);
v___x_2319_ = lean_unsigned_to_nat(1u);
v___x_2320_ = lean_nat_dec_le(v___x_2318_, v___x_2319_);
if (v___x_2320_ == 0)
{
lean_object* v___x_2321_; lean_object* v_fst_2322_; lean_object* v_snd_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2341_; 
lean_del_object(v___x_2311_);
v___x_2321_ = l_Lean_sortExprs(v_snd_2309_, v___x_2320_);
v_fst_2322_ = lean_ctor_get(v___x_2321_, 0);
v_snd_2323_ = lean_ctor_get(v___x_2321_, 1);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2325_ = v___x_2321_;
v_isShared_2326_ = v_isSharedCheck_2341_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_snd_2323_);
lean_inc(v_fst_2322_);
lean_dec(v___x_2321_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2341_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2330_; 
v___x_2327_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_snd_2323_, v_fst_2313_);
v___x_2328_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_snd_2323_, v_snd_2314_);
lean_dec(v_snd_2323_);
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 1, v_fst_2322_);
lean_ctor_set(v___x_2325_, 0, v___x_2328_);
v___x_2330_ = v___x_2325_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v___x_2328_);
lean_ctor_set(v_reuseFailAlloc_2340_, 1, v_fst_2322_);
v___x_2330_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
lean_object* v___x_2332_; 
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 1, v___x_2330_);
lean_ctor_set(v___x_2316_, 0, v___x_2327_);
v___x_2332_ = v___x_2316_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v___x_2327_);
lean_ctor_set(v_reuseFailAlloc_2339_, 1, v___x_2330_);
v___x_2332_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
lean_object* v___x_2334_; 
if (v_isShared_2308_ == 0)
{
lean_ctor_set(v___x_2307_, 0, v___x_2332_);
v___x_2334_ = v___x_2307_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v___x_2332_);
v___x_2334_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
lean_object* v___x_2336_; 
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 0, v___x_2334_);
v___x_2336_ = v___x_2302_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v___x_2334_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
return v___x_2336_;
}
}
}
}
}
}
else
{
lean_object* v___x_2343_; 
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 1, v_snd_2309_);
lean_ctor_set(v___x_2316_, 0, v_snd_2314_);
v___x_2343_ = v___x_2316_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_snd_2314_);
lean_ctor_set(v_reuseFailAlloc_2353_, 1, v_snd_2309_);
v___x_2343_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
lean_object* v___x_2345_; 
if (v_isShared_2312_ == 0)
{
lean_ctor_set(v___x_2311_, 1, v___x_2343_);
lean_ctor_set(v___x_2311_, 0, v_fst_2313_);
v___x_2345_ = v___x_2311_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_fst_2313_);
lean_ctor_set(v_reuseFailAlloc_2352_, 1, v___x_2343_);
v___x_2345_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
lean_object* v___x_2347_; 
if (v_isShared_2308_ == 0)
{
lean_ctor_set(v___x_2307_, 0, v___x_2345_);
v___x_2347_ = v___x_2307_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2345_);
v___x_2347_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
lean_object* v___x_2349_; 
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 0, v___x_2347_);
v___x_2349_ = v___x_2302_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v___x_2347_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
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
lean_object* v___x_2358_; lean_object* v___x_2360_; 
lean_dec(v_fst_2304_);
lean_dec(v_a_2300_);
v___x_2358_ = lean_box(0);
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 0, v___x_2358_);
v___x_2360_ = v___x_2302_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v___x_2358_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
else
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2370_; 
v_a_2363_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2365_ = v___x_2299_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2299_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2368_; 
if (v_isShared_2366_ == 0)
{
v___x_2368_ = v___x_2365_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2363_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_adapter___boxed(lean_object* v_e_2371_, lean_object* v_k_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_adapter(v_e_2371_, v_k_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
lean_dec(v_a_2376_);
lean_dec_ref(v_a_2375_);
lean_dec(v_a_2374_);
lean_dec_ref(v_a_2373_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(lean_object* v_e_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_){
_start:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2385_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___boxed), 7, 1);
lean_closure_set(v___x_2385_, 0, v_e_2379_);
v___x_2386_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(v___x_2385_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2449_; 
v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2389_ = v___x_2386_;
v_isShared_2390_ = v_isSharedCheck_2449_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2386_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2449_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v_fst_2391_; 
v_fst_2391_ = lean_ctor_get(v_a_2387_, 0);
lean_inc(v_fst_2391_);
if (lean_obj_tag(v_fst_2391_) == 1)
{
lean_object* v_val_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2444_; 
v_val_2392_ = lean_ctor_get(v_fst_2391_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v_fst_2391_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2394_ = v_fst_2391_;
v_isShared_2395_ = v_isSharedCheck_2444_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_val_2392_);
lean_dec(v_fst_2391_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2444_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v_snd_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2442_; 
v_snd_2396_ = lean_ctor_get(v_a_2387_, 1);
v_isSharedCheck_2442_ = !lean_is_exclusive(v_a_2387_);
if (v_isSharedCheck_2442_ == 0)
{
lean_object* v_unused_2443_; 
v_unused_2443_ = lean_ctor_get(v_a_2387_, 0);
lean_dec(v_unused_2443_);
v___x_2398_ = v_a_2387_;
v_isShared_2399_ = v_isSharedCheck_2442_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_snd_2396_);
lean_dec(v_a_2387_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2442_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v_fst_2400_; lean_object* v_snd_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2441_; 
v_fst_2400_ = lean_ctor_get(v_val_2392_, 0);
v_snd_2401_ = lean_ctor_get(v_val_2392_, 1);
v_isSharedCheck_2441_ = !lean_is_exclusive(v_val_2392_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2403_ = v_val_2392_;
v_isShared_2404_ = v_isSharedCheck_2441_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_snd_2401_);
lean_inc(v_fst_2400_);
lean_dec(v_val_2392_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2441_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; uint8_t v___x_2407_; 
v___x_2405_ = lean_array_get_size(v_snd_2396_);
v___x_2406_ = lean_unsigned_to_nat(1u);
v___x_2407_ = lean_nat_dec_le(v___x_2405_, v___x_2406_);
if (v___x_2407_ == 0)
{
lean_object* v___x_2408_; lean_object* v_fst_2409_; lean_object* v_snd_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2428_; 
lean_del_object(v___x_2398_);
v___x_2408_ = l_Lean_sortExprs(v_snd_2396_, v___x_2407_);
v_fst_2409_ = lean_ctor_get(v___x_2408_, 0);
v_snd_2410_ = lean_ctor_get(v___x_2408_, 1);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2412_ = v___x_2408_;
v_isShared_2413_ = v_isSharedCheck_2428_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_snd_2410_);
lean_inc(v_fst_2409_);
lean_dec(v___x_2408_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2428_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2417_; 
v___x_2414_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_snd_2410_, v_fst_2400_);
v___x_2415_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_snd_2410_, v_snd_2401_);
lean_dec(v_snd_2410_);
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 1, v_fst_2409_);
lean_ctor_set(v___x_2412_, 0, v___x_2415_);
v___x_2417_ = v___x_2412_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2415_);
lean_ctor_set(v_reuseFailAlloc_2427_, 1, v_fst_2409_);
v___x_2417_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
lean_object* v___x_2419_; 
if (v_isShared_2404_ == 0)
{
lean_ctor_set(v___x_2403_, 1, v___x_2417_);
lean_ctor_set(v___x_2403_, 0, v___x_2414_);
v___x_2419_ = v___x_2403_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2414_);
lean_ctor_set(v_reuseFailAlloc_2426_, 1, v___x_2417_);
v___x_2419_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
lean_object* v___x_2421_; 
if (v_isShared_2395_ == 0)
{
lean_ctor_set(v___x_2394_, 0, v___x_2419_);
v___x_2421_ = v___x_2394_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v___x_2419_);
v___x_2421_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
lean_object* v___x_2423_; 
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 0, v___x_2421_);
v___x_2423_ = v___x_2389_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v___x_2421_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
}
}
}
else
{
lean_object* v___x_2430_; 
if (v_isShared_2404_ == 0)
{
lean_ctor_set(v___x_2403_, 1, v_snd_2396_);
lean_ctor_set(v___x_2403_, 0, v_snd_2401_);
v___x_2430_ = v___x_2403_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_snd_2401_);
lean_ctor_set(v_reuseFailAlloc_2440_, 1, v_snd_2396_);
v___x_2430_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
lean_object* v___x_2432_; 
if (v_isShared_2399_ == 0)
{
lean_ctor_set(v___x_2398_, 1, v___x_2430_);
lean_ctor_set(v___x_2398_, 0, v_fst_2400_);
v___x_2432_ = v___x_2398_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_fst_2400_);
lean_ctor_set(v_reuseFailAlloc_2439_, 1, v___x_2430_);
v___x_2432_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
lean_object* v___x_2434_; 
if (v_isShared_2395_ == 0)
{
lean_ctor_set(v___x_2394_, 0, v___x_2432_);
v___x_2434_ = v___x_2394_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v___x_2432_);
v___x_2434_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
lean_object* v___x_2436_; 
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 0, v___x_2434_);
v___x_2436_ = v___x_2389_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v___x_2434_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
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
lean_object* v___x_2445_; lean_object* v___x_2447_; 
lean_dec(v_fst_2391_);
lean_dec(v_a_2387_);
v___x_2445_ = lean_box(0);
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 0, v___x_2445_);
v___x_2447_ = v___x_2389_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v___x_2445_);
v___x_2447_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
return v___x_2447_;
}
}
}
}
else
{
lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2457_; 
v_a_2450_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2452_ = v___x_2386_;
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v___x_2386_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2455_; 
if (v_isShared_2453_ == 0)
{
v___x_2455_ = v___x_2452_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_a_2450_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f___boxed(lean_object* v_e_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_){
_start:
{
lean_object* v_res_2464_; 
v_res_2464_ = l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(v_e_2458_, v_a_2459_, v_a_2460_, v_a_2461_, v_a_2462_);
lean_dec(v_a_2462_);
lean_dec_ref(v_a_2461_);
lean_dec(v_a_2460_);
lean_dec_ref(v_a_2459_);
return v_res_2464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(lean_object* v_e_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_){
_start:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2471_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___boxed), 7, 1);
lean_closure_set(v___x_2471_, 0, v_e_2465_);
v___x_2472_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(v___x_2471_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_);
if (lean_obj_tag(v___x_2472_) == 0)
{
lean_object* v_a_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2535_; 
v_a_2473_ = lean_ctor_get(v___x_2472_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2475_ = v___x_2472_;
v_isShared_2476_ = v_isSharedCheck_2535_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_a_2473_);
lean_dec(v___x_2472_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2535_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v_fst_2477_; 
v_fst_2477_ = lean_ctor_get(v_a_2473_, 0);
lean_inc(v_fst_2477_);
if (lean_obj_tag(v_fst_2477_) == 1)
{
lean_object* v_val_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2530_; 
v_val_2478_ = lean_ctor_get(v_fst_2477_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v_fst_2477_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2480_ = v_fst_2477_;
v_isShared_2481_ = v_isSharedCheck_2530_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_val_2478_);
lean_dec(v_fst_2477_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2530_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v_snd_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2528_; 
v_snd_2482_ = lean_ctor_get(v_a_2473_, 1);
v_isSharedCheck_2528_ = !lean_is_exclusive(v_a_2473_);
if (v_isSharedCheck_2528_ == 0)
{
lean_object* v_unused_2529_; 
v_unused_2529_ = lean_ctor_get(v_a_2473_, 0);
lean_dec(v_unused_2529_);
v___x_2484_ = v_a_2473_;
v_isShared_2485_ = v_isSharedCheck_2528_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_snd_2482_);
lean_dec(v_a_2473_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2528_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v_fst_2486_; lean_object* v_snd_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2527_; 
v_fst_2486_ = lean_ctor_get(v_val_2478_, 0);
v_snd_2487_ = lean_ctor_get(v_val_2478_, 1);
v_isSharedCheck_2527_ = !lean_is_exclusive(v_val_2478_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2489_ = v_val_2478_;
v_isShared_2490_ = v_isSharedCheck_2527_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_snd_2487_);
lean_inc(v_fst_2486_);
lean_dec(v_val_2478_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2527_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; uint8_t v___x_2493_; 
v___x_2491_ = lean_array_get_size(v_snd_2482_);
v___x_2492_ = lean_unsigned_to_nat(1u);
v___x_2493_ = lean_nat_dec_le(v___x_2491_, v___x_2492_);
if (v___x_2493_ == 0)
{
lean_object* v___x_2494_; lean_object* v_fst_2495_; lean_object* v_snd_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2514_; 
lean_del_object(v___x_2484_);
v___x_2494_ = l_Lean_sortExprs(v_snd_2482_, v___x_2493_);
v_fst_2495_ = lean_ctor_get(v___x_2494_, 0);
v_snd_2496_ = lean_ctor_get(v___x_2494_, 1);
v_isSharedCheck_2514_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2498_ = v___x_2494_;
v_isShared_2499_ = v_isSharedCheck_2514_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_snd_2496_);
lean_inc(v_fst_2495_);
lean_dec(v___x_2494_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2514_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2503_; 
v___x_2500_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_snd_2496_, v_fst_2486_);
v___x_2501_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_snd_2496_, v_snd_2487_);
lean_dec(v_snd_2496_);
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 1, v_fst_2495_);
lean_ctor_set(v___x_2498_, 0, v___x_2501_);
v___x_2503_ = v___x_2498_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2501_);
lean_ctor_set(v_reuseFailAlloc_2513_, 1, v_fst_2495_);
v___x_2503_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
lean_object* v___x_2505_; 
if (v_isShared_2490_ == 0)
{
lean_ctor_set(v___x_2489_, 1, v___x_2503_);
lean_ctor_set(v___x_2489_, 0, v___x_2500_);
v___x_2505_ = v___x_2489_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v___x_2500_);
lean_ctor_set(v_reuseFailAlloc_2512_, 1, v___x_2503_);
v___x_2505_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
lean_object* v___x_2507_; 
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 0, v___x_2505_);
v___x_2507_ = v___x_2480_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v___x_2505_);
v___x_2507_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
lean_object* v___x_2509_; 
if (v_isShared_2476_ == 0)
{
lean_ctor_set(v___x_2475_, 0, v___x_2507_);
v___x_2509_ = v___x_2475_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v___x_2507_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
}
}
}
else
{
lean_object* v___x_2516_; 
if (v_isShared_2490_ == 0)
{
lean_ctor_set(v___x_2489_, 1, v_snd_2482_);
lean_ctor_set(v___x_2489_, 0, v_snd_2487_);
v___x_2516_ = v___x_2489_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_snd_2487_);
lean_ctor_set(v_reuseFailAlloc_2526_, 1, v_snd_2482_);
v___x_2516_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
lean_object* v___x_2518_; 
if (v_isShared_2485_ == 0)
{
lean_ctor_set(v___x_2484_, 1, v___x_2516_);
lean_ctor_set(v___x_2484_, 0, v_fst_2486_);
v___x_2518_ = v___x_2484_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_fst_2486_);
lean_ctor_set(v_reuseFailAlloc_2525_, 1, v___x_2516_);
v___x_2518_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
lean_object* v___x_2520_; 
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 0, v___x_2518_);
v___x_2520_ = v___x_2480_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___x_2518_);
v___x_2520_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
lean_object* v___x_2522_; 
if (v_isShared_2476_ == 0)
{
lean_ctor_set(v___x_2475_, 0, v___x_2520_);
v___x_2522_ = v___x_2475_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v___x_2520_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
return v___x_2522_;
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
lean_object* v___x_2531_; lean_object* v___x_2533_; 
lean_dec(v_fst_2477_);
lean_dec(v_a_2473_);
v___x_2531_ = lean_box(0);
if (v_isShared_2476_ == 0)
{
lean_ctor_set(v___x_2475_, 0, v___x_2531_);
v___x_2533_ = v___x_2475_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v___x_2531_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
}
else
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
v_a_2536_ = lean_ctor_get(v___x_2472_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2538_ = v___x_2472_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2472_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2536_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f___boxed(lean_object* v_e_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_){
_start:
{
lean_object* v_res_2550_; 
v_res_2550_ = l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(v_e_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_);
lean_dec(v_a_2548_);
lean_dec_ref(v_a_2547_);
lean_dec(v_a_2546_);
lean_dec_ref(v_a_2545_);
return v_res_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(lean_object* v_e_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_){
_start:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; 
v___x_2557_ = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___boxed), 7, 1);
lean_closure_set(v___x_2557_, 0, v_e_2551_);
v___x_2558_ = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(v___x_2557_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2620_; 
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2561_ = v___x_2558_;
v_isShared_2562_ = v_isSharedCheck_2620_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2558_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2620_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v_fst_2563_; 
v_fst_2563_ = lean_ctor_get(v_a_2559_, 0);
lean_inc(v_fst_2563_);
if (lean_obj_tag(v_fst_2563_) == 1)
{
lean_object* v_val_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2615_; 
v_val_2564_ = lean_ctor_get(v_fst_2563_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v_fst_2563_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2566_ = v_fst_2563_;
v_isShared_2567_ = v_isSharedCheck_2615_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_val_2564_);
lean_dec(v_fst_2563_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2615_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v_snd_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2613_; 
v_snd_2568_ = lean_ctor_get(v_a_2559_, 1);
v_isSharedCheck_2613_ = !lean_is_exclusive(v_a_2559_);
if (v_isSharedCheck_2613_ == 0)
{
lean_object* v_unused_2614_; 
v_unused_2614_ = lean_ctor_get(v_a_2559_, 0);
lean_dec(v_unused_2614_);
v___x_2570_ = v_a_2559_;
v_isShared_2571_ = v_isSharedCheck_2613_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_snd_2568_);
lean_dec(v_a_2559_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2613_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v_fst_2572_; lean_object* v_snd_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2612_; 
v_fst_2572_ = lean_ctor_get(v_val_2564_, 0);
v_snd_2573_ = lean_ctor_get(v_val_2564_, 1);
v_isSharedCheck_2612_ = !lean_is_exclusive(v_val_2564_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2575_ = v_val_2564_;
v_isShared_2576_ = v_isSharedCheck_2612_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_snd_2573_);
lean_inc(v_fst_2572_);
lean_dec(v_val_2564_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2612_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2577_; lean_object* v___x_2578_; uint8_t v___x_2579_; 
v___x_2577_ = lean_array_get_size(v_snd_2568_);
v___x_2578_ = lean_unsigned_to_nat(1u);
v___x_2579_ = lean_nat_dec_le(v___x_2577_, v___x_2578_);
if (v___x_2579_ == 0)
{
lean_object* v___x_2580_; lean_object* v_fst_2581_; lean_object* v_snd_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2599_; 
lean_del_object(v___x_2570_);
v___x_2580_ = l_Lean_sortExprs(v_snd_2568_, v___x_2579_);
v_fst_2581_ = lean_ctor_get(v___x_2580_, 0);
v_snd_2582_ = lean_ctor_get(v___x_2580_, 1);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2584_ = v___x_2580_;
v_isShared_2585_ = v_isSharedCheck_2599_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_snd_2582_);
lean_inc(v_fst_2581_);
lean_dec(v___x_2580_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2599_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2586_; lean_object* v___x_2588_; 
v___x_2586_ = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Expr_applyPerm_go(v_snd_2582_, v_snd_2573_);
lean_dec(v_snd_2582_);
if (v_isShared_2585_ == 0)
{
lean_ctor_set(v___x_2584_, 1, v_fst_2581_);
lean_ctor_set(v___x_2584_, 0, v___x_2586_);
v___x_2588_ = v___x_2584_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2586_);
lean_ctor_set(v_reuseFailAlloc_2598_, 1, v_fst_2581_);
v___x_2588_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
lean_object* v___x_2590_; 
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 1, v___x_2588_);
v___x_2590_ = v___x_2575_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_fst_2572_);
lean_ctor_set(v_reuseFailAlloc_2597_, 1, v___x_2588_);
v___x_2590_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
lean_object* v___x_2592_; 
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 0, v___x_2590_);
v___x_2592_ = v___x_2566_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v___x_2590_);
v___x_2592_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
lean_object* v___x_2594_; 
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 0, v___x_2592_);
v___x_2594_ = v___x_2561_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v___x_2592_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
return v___x_2594_;
}
}
}
}
}
}
else
{
lean_object* v___x_2601_; 
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 1, v_snd_2568_);
lean_ctor_set(v___x_2575_, 0, v_snd_2573_);
v___x_2601_ = v___x_2575_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_snd_2573_);
lean_ctor_set(v_reuseFailAlloc_2611_, 1, v_snd_2568_);
v___x_2601_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
lean_object* v___x_2603_; 
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 1, v___x_2601_);
lean_ctor_set(v___x_2570_, 0, v_fst_2572_);
v___x_2603_ = v___x_2570_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_fst_2572_);
lean_ctor_set(v_reuseFailAlloc_2610_, 1, v___x_2601_);
v___x_2603_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
lean_object* v___x_2605_; 
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 0, v___x_2603_);
v___x_2605_ = v___x_2566_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v___x_2603_);
v___x_2605_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
lean_object* v___x_2607_; 
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 0, v___x_2605_);
v___x_2607_ = v___x_2561_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v___x_2605_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
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
lean_object* v___x_2616_; lean_object* v___x_2618_; 
lean_dec(v_fst_2563_);
lean_dec(v_a_2559_);
v___x_2616_ = lean_box(0);
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 0, v___x_2616_);
v___x_2618_ = v___x_2561_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v___x_2616_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
else
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2628_; 
v_a_2621_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2623_ = v___x_2558_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2558_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2626_; 
if (v_isShared_2624_ == 0)
{
v___x_2626_ = v___x_2623_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_a_2621_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f___boxed(lean_object* v_e_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_){
_start:
{
lean_object* v_res_2635_; 
v_res_2635_ = l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(v_e_2629_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_);
lean_dec(v_a_2633_);
lean_dec_ref(v_a_2632_);
lean_dec(v_a_2631_);
lean_dec_ref(v_a_2630_);
return v_res_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr___lam__0(lean_object* v___y_2636_){
_start:
{
lean_inc_ref(v___y_2636_);
return v___y_2636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr___lam__0___boxed(lean_object* v___y_2637_){
_start:
{
lean_object* v_res_2638_; 
v_res_2638_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr___lam__0(v___y_2637_);
lean_dec_ref(v___y_2637_);
return v_res_2638_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1(void){
_start:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2640_ = lean_box(0);
v___x_2641_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13));
v___x_2642_ = l_Lean_mkConst(v___x_2641_, v___x_2640_);
return v___x_2642_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__2(void){
_start:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2643_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1, &l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Internal_Linear_Poly_toExpr_go___closed__1);
v___x_2644_ = l_Lean_mkIntLit(v___x_2643_);
return v___x_2644_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__3(void){
_start:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; 
v___x_2645_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__2, &l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__2_once, _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__2);
v___x_2646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2646_, 0, v___x_2645_);
return v___x_2646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr(lean_object* v_ctx_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_){
_start:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; uint8_t v___x_2655_; 
v___x_2653_ = lean_unsigned_to_nat(0u);
v___x_2654_ = lean_array_get_size(v_ctx_2647_);
v___x_2655_ = lean_nat_dec_lt(v___x_2653_, v___x_2654_);
if (v___x_2655_ == 0)
{
lean_object* v___f_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
lean_dec_ref(v_ctx_2647_);
v___f_2656_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__0));
v___x_2657_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1, &l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1_once, _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1);
v___x_2658_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__3, &l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__3_once, _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__3);
v___x_2659_ = l_Lean_RArray_toExpr___redArg(v___x_2657_, v___f_2656_, v___x_2658_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
return v___x_2659_;
}
else
{
lean_object* v___f_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___f_2660_ = ((lean_object*)(l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__0));
v___x_2661_ = lean_obj_once(&l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1, &l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1_once, _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1);
v___x_2662_ = l_Lean_RArray_ofArray___redArg(v_ctx_2647_);
v___x_2663_ = l_Lean_RArray_toExpr___redArg(v___x_2661_, v___f_2660_, v___x_2662_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
return v___x_2663_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr___boxed(lean_object* v_ctx_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_){
_start:
{
lean_object* v_res_2670_; 
v_res_2670_ = l_Lean_Meta_Simp_Arith_Int_toContextExpr(v_ctx_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_);
lean_dec(v_a_2668_);
lean_dec_ref(v_a_2667_);
lean_dec(v_a_2666_);
lean_dec_ref(v_a_2665_);
return v_res_2670_;
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
