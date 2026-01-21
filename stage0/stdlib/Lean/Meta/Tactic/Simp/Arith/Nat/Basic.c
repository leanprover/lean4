// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Arith.Nat.Basic
// Imports: public import Lean.Util.SortExprs public import Lean.Meta.KExprMap import Lean.Data.RArray import Lean.Meta.AppBuilder import Lean.Meta.NatInstTesters import Lean.Meta.Offset
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
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__14;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__5;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2;
lean_object* l_Lean_mkNatLit(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___boxed(lean_object*, lean_object*);
static lean_object* l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__4;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__2;
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DefEq_isInstHAddNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4;
size_t lean_uint64_to_usize(uint64_t);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__19;
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_applyPerm(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__4;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__12;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__10;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__5;
static lean_object* l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__5;
uint8_t l_Lean_Expr_isApp(lean_object*);
static lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr_spec__0(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__15;
lean_object* l_Lean_mkInstOfNatNat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__14;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__8;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DefEq_isInstLTNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__3;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__1;
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__6;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__4;
lean_object* l_Lean_Meta_evalNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__9;
lean_object* l_Lean_Meta_DefEq_isInstHMulNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RArray_toExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__1;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__10;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_applyPerm___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2;
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatAdd(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr;
lean_object* l_Lean_sortExprs(lean_object*, uint8_t);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_ExprCnstr_applyPerm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__6;
lean_object* l_Lean_Meta_DefEq_isInstMulNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__5;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__13;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__8;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7;
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__6;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__3;
lean_object* l_Lean_Meta_KExprMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__1;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__16;
lean_object* l_Lean_Meta_KExprMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__2;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__10;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__18;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__11;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearCnstr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__8;
lean_object* l_Lean_RArray_ofArray___redArg(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__5;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__1;
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__0;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__2;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean___closed__0;
static lean_object* l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg(lean_object*);
static lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__3;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_DefEq_isInstLENat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0___boxed(lean_object*);
static lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLE(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__9;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__3;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__9;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__15;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__9;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__1;
static lean_object* l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_Nat_Linear_ExprCnstr_applyPerm___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__0;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__2;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__17;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__3;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__6;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean___closed__0;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4;
lean_object* l_Lean_Meta_Structural_isInstOfNatNat___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg(lean_object*);
static lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__0;
static lean_object* l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__7;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__13;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__11;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__13;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__15;
static lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__5;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__15;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__0;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__5;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__0;
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__3;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__2;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__0;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__6;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__12;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__10;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__7;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__12;
lean_object* l_Lean_Meta_DefEq_isInstAddNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__6;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__12;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__5;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__16;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__3;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__15;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__11;
lean_object* l_Lean_mkNatMul(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__13;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__16;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__2;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__9;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__8;
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7;
lean_object* lean_st_ref_set(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__14;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__14;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__0;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__3;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__0;
lean_object* l_Lean_Meta_isDefEqI(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__11;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr___redArg(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__14;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__17;
static lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__6;
lean_object* l_Nat_Linear_Expr_inc(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__7;
lean_object* l_Lean_mkNatEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__2;
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__10;
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__7;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__0;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__16;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_nat_dec_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_uint64_of_nat(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(x_2, x_17);
lean_dec(x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0___redArg(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
return x_2;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec_ref(x_4);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec_ref(x_4);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
case 2:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
x_13 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(x_1, x_11);
x_14 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(x_1, x_12);
lean_ctor_set(x_2, 1, x_14);
lean_ctor_set(x_2, 0, x_13);
return x_2;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_2);
x_17 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(x_1, x_15);
x_18 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(x_1, x_16);
x_19 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
case 3:
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_2);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_2, 1);
x_22 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(x_1, x_21);
lean_ctor_set(x_2, 1, x_22);
return x_2;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_2);
x_25 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(x_1, x_24);
x_26 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
default: 
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_2);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_2, 0);
x_29 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(x_1, x_28);
lean_ctor_set(x_2, 0, x_29);
return x_2;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_2, 0);
x_31 = lean_ctor_get(x_2, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_2);
x_32 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(x_1, x_30);
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_applyPerm(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_applyPerm___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_Linear_Expr_applyPerm(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_ExprCnstr_applyPerm(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(x_1, x_4);
x_7 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(x_1, x_5);
lean_ctor_set(x_2, 1, x_7);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_11 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(x_1, x_9);
x_12 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(x_1, x_10);
x_13 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_8);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_ExprCnstr_applyPerm___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_Linear_ExprCnstr_applyPerm(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat.Linear.Expr.num", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__1;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat.Linear.Expr.var", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__6;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat.Linear.Expr.add", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__9;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat.Linear.Expr.mulL", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__11;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__12;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat.Linear.Expr.mulR", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__14;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__15;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_15; uint8_t x_16; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_4 = x_1;
} else {
 lean_dec_ref(x_1);
 x_4 = lean_box(0);
}
x_15 = lean_unsigned_to_nat(1024u);
x_16 = lean_nat_dec_le(x_15, x_2);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3;
x_5 = x_17;
goto block_14;
}
else
{
lean_object* x_18; 
x_18 = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4;
x_5 = x_18;
goto block_14;
}
block_14:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_6 = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__2;
x_7 = l_Nat_reprFast(x_3);
if (lean_is_scalar(x_4)) {
 x_8 = lean_alloc_ctor(3, 1, 0);
} else {
 x_8 = x_4;
 lean_ctor_set_tag(x_8, 3);
}
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_9);
x_11 = 0;
x_12 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_11);
x_13 = l_Repr_addAppParen(x_12, x_2);
return x_13;
}
}
case 1:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_31; uint8_t x_32; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_20 = x_1;
} else {
 lean_dec_ref(x_1);
 x_20 = lean_box(0);
}
x_31 = lean_unsigned_to_nat(1024u);
x_32 = lean_nat_dec_le(x_31, x_2);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3;
x_21 = x_33;
goto block_30;
}
else
{
lean_object* x_34; 
x_34 = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4;
x_21 = x_34;
goto block_30;
}
block_30:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_22 = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__7;
x_23 = l_Nat_reprFast(x_19);
if (lean_is_scalar(x_20)) {
 x_24 = lean_alloc_ctor(3, 1, 0);
} else {
 x_24 = x_20;
 lean_ctor_set_tag(x_24, 3);
}
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_25);
x_27 = 0;
x_28 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_29 = l_Repr_addAppParen(x_28, x_2);
return x_29;
}
}
case 2:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_52; 
x_35 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_35);
x_36 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_36);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_37 = x_1;
} else {
 lean_dec_ref(x_1);
 x_37 = lean_box(0);
}
x_38 = lean_unsigned_to_nat(1024u);
x_52 = lean_nat_dec_le(x_38, x_2);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3;
x_39 = x_53;
goto block_51;
}
else
{
lean_object* x_54; 
x_54 = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4;
x_39 = x_54;
goto block_51;
}
block_51:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; 
x_40 = lean_box(1);
x_41 = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__10;
x_42 = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(x_35, x_38);
if (lean_is_scalar(x_37)) {
 x_43 = lean_alloc_ctor(5, 2, 0);
} else {
 x_43 = x_37;
 lean_ctor_set_tag(x_43, 5);
}
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
x_45 = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(x_36, x_38);
x_46 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_47, 0, x_39);
lean_ctor_set(x_47, 1, x_46);
x_48 = 0;
x_49 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_48);
x_50 = l_Repr_addAppParen(x_49, x_2);
return x_50;
}
}
case 3:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_73; 
x_55 = lean_ctor_get(x_1, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_56);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_57 = x_1;
} else {
 lean_dec_ref(x_1);
 x_57 = lean_box(0);
}
x_58 = lean_unsigned_to_nat(1024u);
x_73 = lean_nat_dec_le(x_58, x_2);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3;
x_59 = x_74;
goto block_72;
}
else
{
lean_object* x_75; 
x_75 = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4;
x_59 = x_75;
goto block_72;
}
block_72:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; 
x_60 = lean_box(1);
x_61 = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__13;
x_62 = l_Nat_reprFast(x_55);
x_63 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_63, 0, x_62);
if (lean_is_scalar(x_57)) {
 x_64 = lean_alloc_ctor(5, 2, 0);
} else {
 x_64 = x_57;
 lean_ctor_set_tag(x_64, 5);
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_60);
x_66 = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(x_56, x_58);
x_67 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_68, 0, x_59);
lean_ctor_set(x_68, 1, x_67);
x_69 = 0;
x_70 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set_uint8(x_70, sizeof(void*)*1, x_69);
x_71 = l_Repr_addAppParen(x_70, x_2);
return x_71;
}
}
default: 
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_94; 
x_76 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_76);
x_77 = lean_ctor_get(x_1, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_78 = x_1;
} else {
 lean_dec_ref(x_1);
 x_78 = lean_box(0);
}
x_79 = lean_unsigned_to_nat(1024u);
x_94 = lean_nat_dec_le(x_79, x_2);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3;
x_80 = x_95;
goto block_93;
}
else
{
lean_object* x_96; 
x_96 = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4;
x_80 = x_96;
goto block_93;
}
block_93:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; 
x_81 = lean_box(1);
x_82 = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__16;
x_83 = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(x_76, x_79);
if (lean_is_scalar(x_78)) {
 x_84 = lean_alloc_ctor(5, 2, 0);
} else {
 x_84 = x_78;
 lean_ctor_set_tag(x_84, 5);
}
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_81);
x_86 = l_Nat_reprFast(x_77);
x_87 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_87, 0, x_86);
x_88 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_89, 0, x_80);
lean_ctor_set(x_89, 1, x_88);
x_90 = 0;
x_91 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set_uint8(x_91, sizeof(void*)*1, x_90);
x_92 = l_Repr_addAppParen(x_91, x_2);
return x_92;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("{ ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__2;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" := ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__5;
x_2 = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__3;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(6u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lhs", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__10;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rhs", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__13;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" }", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__0;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__16;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__15;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__5;
x_6 = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__6;
x_7 = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7;
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Bool_repr___redArg(x_2);
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = 0;
x_12 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_11);
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__9;
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_box(1);
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__11;
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_5);
x_21 = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12;
x_22 = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(x_3, x_8);
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_11);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_14);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_16);
x_28 = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__14;
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_5);
x_31 = l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr(x_4, x_8);
x_32 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_32, 0, x_21);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_11);
x_34 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17;
x_36 = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__18;
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
x_38 = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__19;
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_11);
return x_41;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 0, x_2);
x_7 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
x_2 = x_7;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
lean_inc(x_1);
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_1);
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
x_2 = x_12;
x_3 = x_10;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec_ref(x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_4);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0_spec__1_spec__2(x_2, x_6, x_4);
return x_7;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__9;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__0;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__3;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Nat_reprFast(x_3);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_box(0);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_6);
x_8 = l_Nat_reprFast(x_4);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_1);
x_11 = l_List_reverse___redArg(x_10);
x_12 = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__1;
x_13 = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0_spec__1(x_11, x_12);
x_14 = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__4;
x_15 = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__5;
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
x_17 = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__6;
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_18);
x_20 = 0;
x_21 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_24 = l_Nat_reprFast(x_22);
x_25 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Nat_reprFast(x_23);
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
x_31 = l_List_reverse___redArg(x_30);
x_32 = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__1;
x_33 = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0_spec__1(x_31, x_32);
x_34 = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__4;
x_35 = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__5;
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
x_37 = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__6;
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_38);
x_40 = 0;
x_41 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_40);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__1_spec__3_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 0, x_2);
x_7 = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg(x_5);
x_8 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
x_2 = x_8;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
lean_inc(x_1);
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_1);
x_13 = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg(x_10);
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_2 = x_14;
x_3 = x_11;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__1_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 0, x_2);
x_7 = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg(x_5);
x_8 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__1_spec__3_spec__5(x_1, x_8, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
lean_inc(x_1);
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_1);
x_13 = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg(x_10);
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__1_spec__3_spec__5(x_1, x_14, x_11);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg(x_7);
x_9 = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__1_spec__3(x_2, x_8, x_4);
return x_9;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[]", 2, 2);
return x_1;
}
}
static lean_object* _init_l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__2;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__4;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__1;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_3 = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__1;
x_4 = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__1(x_1, x_3);
x_5 = l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__5;
x_6 = l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__6;
x_7 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
x_8 = l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__7;
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_9);
x_11 = 0;
x_12 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__5;
x_6 = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__6;
x_7 = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7;
x_8 = l_Bool_repr___redArg(x_2);
x_9 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = 0;
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_10);
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__9;
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_box(1);
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__11;
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_5);
x_20 = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12;
x_21 = l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg(x_3);
x_22 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_10);
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_13);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_15);
x_27 = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__14;
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_5);
x_30 = l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg(x_4);
x_31 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_31, 0, x_20);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_10);
x_33 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17;
x_35 = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__18;
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
x_37 = l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__19;
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_10);
return x_40;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Linear", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Expr", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("num", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__3;
x_2 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2;
x_3 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1;
x_4 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("var", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__6;
x_2 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2;
x_3 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1;
x_4 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("add", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__9;
x_2 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2;
x_3 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1;
x_4 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mulL", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__12;
x_2 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2;
x_3 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1;
x_4 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mulR", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__15;
x_2 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2;
x_3 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1;
x_4 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__5;
x_4 = l_Lean_mkNatLit(x_2);
x_5 = l_Lean_Expr_app___override(x_3, x_4);
return x_5;
}
case 1:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__8;
x_8 = l_Lean_mkNatLit(x_6);
x_9 = l_Lean_Expr_app___override(x_7, x_8);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_11);
lean_dec_ref(x_1);
x_12 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__11;
x_13 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(x_10);
x_14 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(x_11);
x_15 = l_Lean_mkAppB(x_12, x_13, x_14);
return x_15;
}
case 3:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_17);
lean_dec_ref(x_1);
x_18 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__14;
x_19 = l_Lean_mkNatLit(x_16);
x_20 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(x_17);
x_21 = l_Lean_mkAppB(x_18, x_19, x_20);
return x_21;
}
default: 
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_dec_ref(x_1);
x_24 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__17;
x_25 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(x_22);
x_26 = l_Lean_mkNatLit(x_23);
x_27 = l_Lean_mkAppB(x_24, x_25, x_26);
return x_27;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2;
x_2 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1;
x_3 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__2;
x_2 = l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ExprCnstr", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mk", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__1;
x_2 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__0;
x_3 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1;
x_4 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Bool", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__5;
x_2 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__4;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__6;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__8;
x_2 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__4;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__9;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__3;
if (x_2 == 0)
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__7;
x_6 = x_11;
goto block_10;
}
else
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__10;
x_6 = x_12;
goto block_10;
}
block_10:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(x_3);
x_8 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(x_4);
x_9 = l_Lean_mkApp3(x_5, x_6, x_7, x_8);
return x_9;
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__0;
x_2 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1;
x_3 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__2;
x_2 = l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = l_Lean_mkNatLit(x_5);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_Lean_mkNatLit(x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
case 1:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = l_Lean_instInhabitedExpr;
x_13 = lean_array_get_borrowed(x_12, x_1, x_11);
lean_dec(x_11);
lean_inc(x_13);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_13);
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_Lean_instInhabitedExpr;
x_16 = lean_array_get_borrowed(x_15, x_1, x_14);
lean_dec(x_14);
lean_inc(x_16);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
case 2:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_18);
x_19 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_19);
lean_dec_ref(x_2);
x_20 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_1, x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_1, x_19);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = l_Lean_mkNatAdd(x_21, x_24);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
x_27 = l_Lean_mkNatAdd(x_21, x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
case 3:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_30);
lean_dec_ref(x_2);
x_31 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_1, x_30);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = l_Lean_mkNatLit(x_29);
x_35 = l_Lean_mkNatMul(x_34, x_33);
lean_ctor_set(x_31, 0, x_35);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
lean_dec(x_31);
x_37 = l_Lean_mkNatLit(x_29);
x_38 = l_Lean_mkNatMul(x_37, x_36);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
default: 
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_40);
x_41 = lean_ctor_get(x_2, 1);
lean_inc(x_41);
lean_dec_ref(x_2);
x_42 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_1, x_40);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = l_Lean_mkNatLit(x_41);
x_46 = l_Lean_mkNatMul(x_44, x_45);
lean_ctor_set(x_42, 0, x_46);
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_42, 0);
lean_inc(x_47);
lean_dec(x_42);
x_48 = l_Lean_mkNatLit(x_41);
x_49 = l_Lean_mkNatMul(x_47, x_48);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_1, x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_6);
lean_dec_ref(x_2);
x_7 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_1, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_1, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_mkNatLE(x_8, x_11);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = l_Lean_mkNatLE(x_8, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_17);
lean_dec_ref(x_2);
x_18 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_1, x_16);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_1, x_17);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = l_Lean_mkNatEq(x_19, x_22);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_25 = l_Lean_mkNatEq(x_19, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(x_1, x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_st_ref_get(x_2);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
lean_dec(x_8);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_10 = l_Lean_Meta_KExprMap_find_x3f___redArg(x_9, x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
if (lean_obj_tag(x_12) == 1)
{
uint8_t x_13; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_free_object(x_10);
lean_dec(x_12);
x_16 = lean_st_ref_get(x_2);
x_17 = lean_st_ref_get(x_2);
x_18 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_18);
lean_dec(x_16);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
x_22 = lean_array_get_size(x_18);
lean_dec_ref(x_18);
lean_inc_ref(x_1);
x_23 = l_Lean_Meta_KExprMap_insert___redArg(x_20, x_1, x_22, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_array_push(x_21, x_1);
lean_ctor_set(x_17, 1, x_26);
lean_ctor_set(x_17, 0, x_25);
x_27 = lean_st_ref_set(x_2, x_17);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_23, 0, x_28);
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_23, 0);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_array_push(x_21, x_1);
lean_ctor_set(x_17, 1, x_30);
lean_ctor_set(x_17, 0, x_29);
x_31 = lean_st_ref_set(x_2, x_17);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_22);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_free_object(x_17);
lean_dec_ref(x_21);
lean_dec_ref(x_1);
x_34 = !lean_is_exclusive(x_23);
if (x_34 == 0)
{
return x_23;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_23, 0);
lean_inc(x_35);
lean_dec(x_23);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_17, 0);
x_38 = lean_ctor_get(x_17, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_17);
x_39 = lean_array_get_size(x_18);
lean_dec_ref(x_18);
lean_inc_ref(x_1);
x_40 = l_Lean_Meta_KExprMap_insert___redArg(x_37, x_1, x_39, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_42 = x_40;
} else {
 lean_dec_ref(x_40);
 x_42 = lean_box(0);
}
x_43 = lean_array_push(x_38, x_1);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_st_ref_set(x_2, x_44);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_39);
if (lean_is_scalar(x_42)) {
 x_47 = lean_alloc_ctor(0, 1, 0);
} else {
 x_47 = x_42;
}
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec_ref(x_38);
lean_dec_ref(x_1);
x_48 = lean_ctor_get(x_40, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_49 = x_40;
} else {
 lean_dec_ref(x_40);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 1, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_48);
return x_50;
}
}
}
}
else
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_10, 0);
lean_inc(x_51);
lean_dec(x_10);
if (lean_obj_tag(x_51) == 1)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 1, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_52);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_51);
x_56 = lean_st_ref_get(x_2);
x_57 = lean_st_ref_get(x_2);
x_58 = lean_ctor_get(x_56, 1);
lean_inc_ref(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_57, 0);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc_ref(x_60);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_61 = x_57;
} else {
 lean_dec_ref(x_57);
 x_61 = lean_box(0);
}
x_62 = lean_array_get_size(x_58);
lean_dec_ref(x_58);
lean_inc_ref(x_1);
x_63 = l_Lean_Meta_KExprMap_insert___redArg(x_59, x_1, x_62, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_65 = x_63;
} else {
 lean_dec_ref(x_63);
 x_65 = lean_box(0);
}
x_66 = lean_array_push(x_60, x_1);
if (lean_is_scalar(x_61)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_61;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_st_ref_set(x_2, x_67);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_62);
if (lean_is_scalar(x_65)) {
 x_70 = lean_alloc_ctor(0, 1, 0);
} else {
 x_70 = x_65;
}
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_61);
lean_dec_ref(x_60);
lean_dec_ref(x_1);
x_71 = lean_ctor_get(x_63, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_72 = x_63;
} else {
 lean_dec_ref(x_63);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 1, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_71);
return x_73;
}
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_74 = !lean_is_exclusive(x_10);
if (x_74 == 0)
{
return x_10;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_10, 0);
lean_inc(x_75);
lean_dec(x_10);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("zero", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("succ", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__0;
x_2 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mul", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__2;
x_2 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__9;
x_2 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ofNat", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("OfNat", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__6;
x_2 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__5;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Mul", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__2;
x_2 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__8;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Add", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__9;
x_2 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__10;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hMul", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HMul", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__13;
x_2 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__12;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hAdd", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HAdd", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__16;
x_2 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__15;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
lean_inc_ref(x_1);
x_8 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = l_Lean_Expr_cleanupAnnotations(x_9);
x_11 = l_Lean_Expr_isApp(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec_ref(x_10);
x_12 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc_ref(x_13);
x_14 = l_Lean_Expr_appFnCleanup___redArg(x_10);
x_15 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__1;
x_16 = l_Lean_Expr_isConstOf(x_14, x_15);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = l_Lean_Expr_isApp(x_14);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec_ref(x_14);
lean_dec_ref(x_13);
x_18 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_19);
x_55 = l_Lean_Expr_appFnCleanup___redArg(x_14);
x_56 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__3;
x_57 = l_Lean_Expr_isConstOf(x_55, x_56);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__4;
x_59 = l_Lean_Expr_isConstOf(x_55, x_58);
if (x_59 == 0)
{
uint8_t x_60; 
x_60 = l_Lean_Expr_isApp(x_55);
if (x_60 == 0)
{
lean_object* x_61; 
lean_dec_ref(x_55);
lean_dec_ref(x_19);
lean_dec_ref(x_13);
x_61 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_62 = lean_ctor_get(x_55, 1);
lean_inc_ref(x_62);
x_63 = l_Lean_Expr_appFnCleanup___redArg(x_55);
x_64 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__7;
x_65 = l_Lean_Expr_isConstOf(x_63, x_64);
if (x_65 == 0)
{
uint8_t x_66; 
x_66 = l_Lean_Expr_isApp(x_63);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec_ref(x_63);
lean_dec_ref(x_62);
lean_dec_ref(x_19);
lean_dec_ref(x_13);
x_67 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = l_Lean_Expr_appFnCleanup___redArg(x_63);
x_69 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__9;
x_70 = l_Lean_Expr_isConstOf(x_68, x_69);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__11;
x_72 = l_Lean_Expr_isConstOf(x_68, x_71);
if (x_72 == 0)
{
uint8_t x_73; 
x_73 = l_Lean_Expr_isApp(x_68);
if (x_73 == 0)
{
lean_object* x_74; 
lean_dec_ref(x_68);
lean_dec_ref(x_62);
lean_dec_ref(x_19);
lean_dec_ref(x_13);
x_74 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6);
return x_74;
}
else
{
lean_object* x_75; uint8_t x_76; 
x_75 = l_Lean_Expr_appFnCleanup___redArg(x_68);
x_76 = l_Lean_Expr_isApp(x_75);
if (x_76 == 0)
{
lean_object* x_77; 
lean_dec_ref(x_75);
lean_dec_ref(x_62);
lean_dec_ref(x_19);
lean_dec_ref(x_13);
x_77 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = l_Lean_Expr_appFnCleanup___redArg(x_75);
x_79 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__14;
x_80 = l_Lean_Expr_isConstOf(x_78, x_79);
if (x_80 == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__17;
x_82 = l_Lean_Expr_isConstOf(x_78, x_81);
lean_dec_ref(x_78);
if (x_82 == 0)
{
lean_object* x_83; 
lean_dec_ref(x_62);
lean_dec_ref(x_19);
lean_dec_ref(x_13);
x_83 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6);
return x_83;
}
else
{
lean_object* x_84; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_84 = l_Lean_Meta_DefEq_isInstHAddNat(x_62, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec_ref(x_84);
x_86 = lean_unbox(x_85);
lean_dec(x_85);
if (x_86 == 0)
{
lean_object* x_87; 
lean_dec_ref(x_19);
lean_dec_ref(x_13);
x_87 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6);
return x_87;
}
else
{
lean_object* x_88; 
lean_dec_ref(x_1);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_88 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_dec_ref(x_88);
x_90 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_13, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_90) == 0)
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_90, 0);
x_93 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_93, 0, x_89);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set(x_90, 0, x_93);
return x_90;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_90, 0);
lean_inc(x_94);
lean_dec(x_90);
x_95 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_95, 0, x_89);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_96, 0, x_95);
return x_96;
}
}
else
{
lean_dec(x_89);
return x_90;
}
}
else
{
lean_dec_ref(x_13);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_88;
}
}
}
else
{
uint8_t x_97; 
lean_dec_ref(x_19);
lean_dec_ref(x_13);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_97 = !lean_is_exclusive(x_84);
if (x_97 == 0)
{
return x_84;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_84, 0);
lean_inc(x_98);
lean_dec(x_84);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_98);
return x_99;
}
}
}
}
else
{
lean_object* x_100; 
lean_dec_ref(x_78);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_100 = l_Lean_Meta_DefEq_isInstHMulNat(x_62, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec_ref(x_100);
x_102 = lean_unbox(x_101);
lean_dec(x_101);
if (x_102 == 0)
{
lean_object* x_103; 
lean_dec_ref(x_19);
lean_dec_ref(x_13);
x_103 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6);
return x_103;
}
else
{
x_20 = x_13;
x_21 = x_2;
x_22 = x_3;
x_23 = x_4;
x_24 = x_5;
x_25 = x_6;
x_26 = lean_box(0);
goto block_54;
}
}
else
{
uint8_t x_104; 
lean_dec_ref(x_19);
lean_dec_ref(x_13);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_104 = !lean_is_exclusive(x_100);
if (x_104 == 0)
{
return x_100;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_100, 0);
lean_inc(x_105);
lean_dec(x_100);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
}
}
}
}
}
else
{
lean_object* x_107; 
lean_dec_ref(x_68);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_107 = l_Lean_Meta_DefEq_isInstAddNat(x_62, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec_ref(x_107);
x_109 = lean_unbox(x_108);
lean_dec(x_108);
if (x_109 == 0)
{
lean_object* x_110; 
lean_dec_ref(x_19);
lean_dec_ref(x_13);
x_110 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6);
return x_110;
}
else
{
lean_object* x_111; 
lean_dec_ref(x_1);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_111 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_dec_ref(x_111);
x_113 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_13, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_113) == 0)
{
uint8_t x_114; 
x_114 = !lean_is_exclusive(x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_113, 0);
x_116 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_116, 0, x_112);
lean_ctor_set(x_116, 1, x_115);
lean_ctor_set(x_113, 0, x_116);
return x_113;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_113, 0);
lean_inc(x_117);
lean_dec(x_113);
x_118 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_118, 0, x_112);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_119, 0, x_118);
return x_119;
}
}
else
{
lean_dec(x_112);
return x_113;
}
}
else
{
lean_dec_ref(x_13);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_111;
}
}
}
else
{
uint8_t x_120; 
lean_dec_ref(x_19);
lean_dec_ref(x_13);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_120 = !lean_is_exclusive(x_107);
if (x_120 == 0)
{
return x_107;
}
else
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_107, 0);
lean_inc(x_121);
lean_dec(x_107);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_121);
return x_122;
}
}
}
}
else
{
lean_object* x_123; 
lean_dec_ref(x_68);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_123 = l_Lean_Meta_DefEq_isInstMulNat(x_62, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; uint8_t x_125; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
lean_dec_ref(x_123);
x_125 = lean_unbox(x_124);
lean_dec(x_124);
if (x_125 == 0)
{
lean_object* x_126; 
lean_dec_ref(x_19);
lean_dec_ref(x_13);
x_126 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6);
return x_126;
}
else
{
x_20 = x_13;
x_21 = x_2;
x_22 = x_3;
x_23 = x_4;
x_24 = x_5;
x_25 = x_6;
x_26 = lean_box(0);
goto block_54;
}
}
else
{
uint8_t x_127; 
lean_dec_ref(x_19);
lean_dec_ref(x_13);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_127 = !lean_is_exclusive(x_123);
if (x_127 == 0)
{
return x_123;
}
else
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_123, 0);
lean_inc(x_128);
lean_dec(x_123);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_128);
return x_129;
}
}
}
}
}
else
{
lean_object* x_130; 
lean_dec_ref(x_63);
lean_dec_ref(x_62);
lean_inc_ref(x_13);
x_130 = l_Lean_Meta_Structural_isInstOfNatNat___redArg(x_13, x_4);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; uint8_t x_132; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
lean_dec_ref(x_130);
x_132 = lean_unbox(x_131);
lean_dec(x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; 
lean_inc_ref(x_19);
x_133 = l_Lean_mkInstOfNatNat(x_19);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_134 = l_Lean_Meta_isDefEqI(x_13, x_133, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; uint8_t x_136; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
lean_dec_ref(x_134);
x_136 = lean_unbox(x_135);
lean_dec(x_135);
if (x_136 == 0)
{
lean_object* x_137; 
lean_dec_ref(x_19);
x_137 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6);
return x_137;
}
else
{
lean_object* x_138; 
lean_dec_ref(x_1);
x_138 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6);
return x_138;
}
}
else
{
uint8_t x_139; 
lean_dec_ref(x_19);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_139 = !lean_is_exclusive(x_134);
if (x_139 == 0)
{
return x_134;
}
else
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_134, 0);
lean_inc(x_140);
lean_dec(x_134);
x_141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_141, 0, x_140);
return x_141;
}
}
}
else
{
lean_object* x_142; 
lean_dec_ref(x_13);
lean_dec_ref(x_1);
x_142 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6);
return x_142;
}
}
else
{
uint8_t x_143; 
lean_dec_ref(x_19);
lean_dec_ref(x_13);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_143 = !lean_is_exclusive(x_130);
if (x_143 == 0)
{
return x_130;
}
else
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_130, 0);
lean_inc(x_144);
lean_dec(x_130);
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_144);
return x_145;
}
}
}
}
}
else
{
lean_object* x_146; 
lean_dec_ref(x_55);
lean_dec_ref(x_1);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_146 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
lean_dec_ref(x_146);
x_148 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_13, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_148) == 0)
{
uint8_t x_149; 
x_149 = !lean_is_exclusive(x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_148, 0);
x_151 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_151, 0, x_147);
lean_ctor_set(x_151, 1, x_150);
lean_ctor_set(x_148, 0, x_151);
return x_148;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_148, 0);
lean_inc(x_152);
lean_dec(x_148);
x_153 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_153, 0, x_147);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_154, 0, x_153);
return x_154;
}
}
else
{
lean_dec(x_147);
return x_148;
}
}
else
{
lean_dec_ref(x_13);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_146;
}
}
}
else
{
lean_dec_ref(x_55);
x_20 = x_13;
x_21 = x_2;
x_22 = x_3;
x_23 = x_4;
x_24 = x_5;
x_25 = x_6;
x_26 = lean_box(0);
goto block_54;
}
block_54:
{
lean_object* x_27; 
lean_inc_ref(x_24);
lean_inc_ref(x_19);
x_27 = l_Lean_Meta_evalNat(x_19, x_22, x_23, x_24, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
lean_inc_ref(x_24);
x_29 = l_Lean_Meta_evalNat(x_20, x_22, x_23, x_24, x_25);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
lean_dec_ref(x_19);
x_31 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_21, x_22, x_23, x_24, x_25);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec_ref(x_1);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_19, x_21, x_22, x_23, x_24, x_25);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
lean_ctor_set(x_33, 0, x_36);
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 0);
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_32);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
else
{
lean_dec(x_32);
return x_33;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec_ref(x_1);
x_40 = !lean_is_exclusive(x_29);
if (x_40 == 0)
{
return x_29;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_29, 0);
lean_inc(x_41);
lean_dec(x_29);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec_ref(x_19);
lean_dec_ref(x_1);
x_43 = lean_ctor_get(x_28, 0);
lean_inc(x_43);
lean_dec_ref(x_28);
x_44 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_20, x_21, x_22, x_23, x_24, x_25);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_44, 0, x_47);
return x_44;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_44, 0);
lean_inc(x_48);
lean_dec(x_44);
x_49 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
else
{
lean_dec(x_43);
return x_44;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_1);
x_51 = !lean_is_exclusive(x_27);
if (x_51 == 0)
{
return x_27;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_27, 0);
lean_inc(x_52);
lean_dec(x_27);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
}
}
else
{
lean_object* x_155; 
lean_dec_ref(x_14);
lean_dec_ref(x_1);
x_155 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_13, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_155) == 0)
{
uint8_t x_156; 
x_156 = !lean_is_exclusive(x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_155, 0);
x_158 = l_Nat_Linear_Expr_inc(x_157);
lean_ctor_set(x_155, 0, x_158);
return x_155;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_155, 0);
lean_inc(x_159);
lean_dec(x_155);
x_160 = l_Nat_Linear_Expr_inc(x_159);
x_161 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_161, 0, x_160);
return x_161;
}
}
else
{
return x_155;
}
}
}
}
else
{
uint8_t x_162; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_162 = !lean_is_exclusive(x_8);
if (x_162 == 0)
{
return x_8;
}
else
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_8, 0);
lean_inc(x_163);
lean_dec(x_8);
x_164 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_164, 0, x_163);
return x_164;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 9:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
lean_object* x_14; 
lean_dec_ref(x_8);
x_14 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6);
return x_14;
}
}
case 10:
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_15);
lean_dec_ref(x_1);
x_1 = x_15;
goto _start;
}
case 4:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_ctor_get(x_18, 1);
x_22 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0;
x_23 = lean_string_dec_eq(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6);
return x_24;
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__0;
x_26 = lean_string_dec_eq(x_20, x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_28 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__1;
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; 
x_30 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6);
return x_30;
}
}
else
{
lean_object* x_31; 
x_31 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6);
return x_31;
}
}
else
{
lean_object* x_32; 
x_32 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6);
return x_32;
}
}
case 5:
{
lean_object* x_33; 
x_33 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit(x_1, x_2, x_3, x_4, x_5, x_6);
return x_33;
}
case 2:
{
lean_object* x_34; 
x_34 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit(x_1, x_2, x_3, x_4, x_5, x_6);
return x_34;
}
default: 
{
lean_object* x_35; 
x_35 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lt", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__0;
x_2 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("le", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__2;
x_2 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("GT", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("gt", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__7;
x_2 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__6;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("GE", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ge", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__10;
x_2 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__9;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LT", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__0;
x_2 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__12;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LE", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__2;
x_2 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__14;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_10 = x_8;
} else {
 lean_dec_ref(x_8);
 x_10 = lean_box(0);
}
x_14 = l_Lean_Expr_cleanupAnnotations(x_9);
x_15 = l_Lean_Expr_isApp(x_14);
if (x_15 == 0)
{
lean_dec_ref(x_14);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
goto block_13;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_16);
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_14);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
goto block_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_19);
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_21 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__1;
x_22 = l_Lean_Expr_isConstOf(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__3;
x_24 = l_Lean_Expr_isConstOf(x_20, x_23);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = l_Lean_Expr_isApp(x_20);
if (x_25 == 0)
{
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
goto block_13;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_26);
x_27 = l_Lean_Expr_appFnCleanup___redArg(x_20);
x_28 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__5;
x_29 = l_Lean_Expr_isConstOf(x_27, x_28);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = l_Lean_Expr_isApp(x_27);
if (x_30 == 0)
{
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
goto block_13;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = l_Lean_Expr_appFnCleanup___redArg(x_27);
x_32 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__8;
x_33 = l_Lean_Expr_isConstOf(x_31, x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__11;
x_35 = l_Lean_Expr_isConstOf(x_31, x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__13;
x_37 = l_Lean_Expr_isConstOf(x_31, x_36);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__15;
x_39 = l_Lean_Expr_isConstOf(x_31, x_38);
lean_dec_ref(x_31);
if (x_39 == 0)
{
lean_dec_ref(x_26);
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
goto block_13;
}
else
{
lean_object* x_40; 
lean_dec(x_10);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_40 = l_Lean_Meta_DefEq_isInstLENat(x_26, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_44 = lean_box(0);
lean_ctor_set(x_40, 0, x_44);
return x_40;
}
else
{
lean_object* x_45; 
lean_free_object(x_40);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_45 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_16, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_37);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_47, 0, x_51);
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_47, 0);
lean_inc(x_52);
lean_dec(x_47);
x_53 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_53, 0, x_46);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*2, x_37);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec(x_46);
x_56 = !lean_is_exclusive(x_47);
if (x_56 == 0)
{
return x_47;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_47, 0);
lean_inc(x_57);
lean_dec(x_47);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_59 = !lean_is_exclusive(x_45);
if (x_59 == 0)
{
return x_45;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_45, 0);
lean_inc(x_60);
lean_dec(x_45);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
}
else
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_40, 0);
lean_inc(x_62);
lean_dec(x_40);
x_63 = lean_unbox(x_62);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
else
{
lean_object* x_66; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_66 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec_ref(x_66);
x_68 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_16, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 x_70 = x_68;
} else {
 lean_dec_ref(x_68);
 x_70 = lean_box(0);
}
x_71 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_71, 0, x_67);
lean_ctor_set(x_71, 1, x_69);
lean_ctor_set_uint8(x_71, sizeof(void*)*2, x_37);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
if (lean_is_scalar(x_70)) {
 x_73 = lean_alloc_ctor(0, 1, 0);
} else {
 x_73 = x_70;
}
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_67);
x_74 = lean_ctor_get(x_68, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 x_75 = x_68;
} else {
 lean_dec_ref(x_68);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_74);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_77 = lean_ctor_get(x_66, 0);
lean_inc(x_77);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_78 = x_66;
} else {
 lean_dec_ref(x_66);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 1, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_77);
return x_79;
}
}
}
}
else
{
uint8_t x_80; 
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_80 = !lean_is_exclusive(x_40);
if (x_80 == 0)
{
return x_40;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_40, 0);
lean_inc(x_81);
lean_dec(x_40);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
}
}
else
{
lean_object* x_83; 
lean_dec_ref(x_31);
lean_dec(x_10);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_83 = l_Lean_Meta_DefEq_isInstLTNat(x_26, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_ctor_get(x_83, 0);
x_86 = lean_unbox(x_85);
lean_dec(x_85);
if (x_86 == 0)
{
lean_object* x_87; 
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_87 = lean_box(0);
lean_ctor_set(x_83, 0, x_87);
return x_83;
}
else
{
lean_object* x_88; 
lean_free_object(x_83);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_88 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_dec_ref(x_88);
x_90 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_16, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_90) == 0)
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_90, 0);
x_93 = l_Nat_Linear_Expr_inc(x_89);
x_94 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
lean_ctor_set_uint8(x_94, sizeof(void*)*2, x_35);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_90, 0, x_95);
return x_90;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_ctor_get(x_90, 0);
lean_inc(x_96);
lean_dec(x_90);
x_97 = l_Nat_Linear_Expr_inc(x_89);
x_98 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
lean_ctor_set_uint8(x_98, sizeof(void*)*2, x_35);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_98);
x_100 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_100, 0, x_99);
return x_100;
}
}
else
{
uint8_t x_101; 
lean_dec(x_89);
x_101 = !lean_is_exclusive(x_90);
if (x_101 == 0)
{
return x_90;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_90, 0);
lean_inc(x_102);
lean_dec(x_90);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
return x_103;
}
}
}
else
{
uint8_t x_104; 
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_104 = !lean_is_exclusive(x_88);
if (x_104 == 0)
{
return x_88;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_88, 0);
lean_inc(x_105);
lean_dec(x_88);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
}
}
}
else
{
lean_object* x_107; uint8_t x_108; 
x_107 = lean_ctor_get(x_83, 0);
lean_inc(x_107);
lean_dec(x_83);
x_108 = lean_unbox(x_107);
lean_dec(x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_109 = lean_box(0);
x_110 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_110, 0, x_109);
return x_110;
}
else
{
lean_object* x_111; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_111 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_dec_ref(x_111);
x_113 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_16, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 x_115 = x_113;
} else {
 lean_dec_ref(x_113);
 x_115 = lean_box(0);
}
x_116 = l_Nat_Linear_Expr_inc(x_112);
x_117 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_114);
lean_ctor_set_uint8(x_117, sizeof(void*)*2, x_35);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_117);
if (lean_is_scalar(x_115)) {
 x_119 = lean_alloc_ctor(0, 1, 0);
} else {
 x_119 = x_115;
}
lean_ctor_set(x_119, 0, x_118);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_112);
x_120 = lean_ctor_get(x_113, 0);
lean_inc(x_120);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 x_121 = x_113;
} else {
 lean_dec_ref(x_113);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 1, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_120);
return x_122;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_123 = lean_ctor_get(x_111, 0);
lean_inc(x_123);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 x_124 = x_111;
} else {
 lean_dec_ref(x_111);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 1, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_123);
return x_125;
}
}
}
}
else
{
uint8_t x_126; 
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_126 = !lean_is_exclusive(x_83);
if (x_126 == 0)
{
return x_83;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_83, 0);
lean_inc(x_127);
lean_dec(x_83);
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_127);
return x_128;
}
}
}
}
else
{
lean_object* x_129; 
lean_dec_ref(x_31);
lean_dec(x_10);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_129 = l_Lean_Meta_DefEq_isInstLENat(x_26, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_129) == 0)
{
uint8_t x_130; 
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
lean_object* x_131; uint8_t x_132; 
x_131 = lean_ctor_get(x_129, 0);
x_132 = lean_unbox(x_131);
lean_dec(x_131);
if (x_132 == 0)
{
lean_object* x_133; 
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_133 = lean_box(0);
lean_ctor_set(x_129, 0, x_133);
return x_129;
}
else
{
lean_object* x_134; 
lean_free_object(x_129);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_134 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_16, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
lean_dec_ref(x_134);
x_136 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_136) == 0)
{
uint8_t x_137; 
x_137 = !lean_is_exclusive(x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_136, 0);
x_139 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_139, 0, x_135);
lean_ctor_set(x_139, 1, x_138);
lean_ctor_set_uint8(x_139, sizeof(void*)*2, x_33);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_136, 0, x_140);
return x_136;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_141 = lean_ctor_get(x_136, 0);
lean_inc(x_141);
lean_dec(x_136);
x_142 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_142, 0, x_135);
lean_ctor_set(x_142, 1, x_141);
lean_ctor_set_uint8(x_142, sizeof(void*)*2, x_33);
x_143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_143, 0, x_142);
x_144 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_144, 0, x_143);
return x_144;
}
}
else
{
uint8_t x_145; 
lean_dec(x_135);
x_145 = !lean_is_exclusive(x_136);
if (x_145 == 0)
{
return x_136;
}
else
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_136, 0);
lean_inc(x_146);
lean_dec(x_136);
x_147 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_147, 0, x_146);
return x_147;
}
}
}
else
{
uint8_t x_148; 
lean_dec_ref(x_19);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_148 = !lean_is_exclusive(x_134);
if (x_148 == 0)
{
return x_134;
}
else
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_134, 0);
lean_inc(x_149);
lean_dec(x_134);
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_149);
return x_150;
}
}
}
}
else
{
lean_object* x_151; uint8_t x_152; 
x_151 = lean_ctor_get(x_129, 0);
lean_inc(x_151);
lean_dec(x_129);
x_152 = lean_unbox(x_151);
lean_dec(x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_153 = lean_box(0);
x_154 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_154, 0, x_153);
return x_154;
}
else
{
lean_object* x_155; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_155 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_16, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
lean_dec_ref(x_155);
x_157 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 x_159 = x_157;
} else {
 lean_dec_ref(x_157);
 x_159 = lean_box(0);
}
x_160 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_160, 0, x_156);
lean_ctor_set(x_160, 1, x_158);
lean_ctor_set_uint8(x_160, sizeof(void*)*2, x_33);
x_161 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_161, 0, x_160);
if (lean_is_scalar(x_159)) {
 x_162 = lean_alloc_ctor(0, 1, 0);
} else {
 x_162 = x_159;
}
lean_ctor_set(x_162, 0, x_161);
return x_162;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_156);
x_163 = lean_ctor_get(x_157, 0);
lean_inc(x_163);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 x_164 = x_157;
} else {
 lean_dec_ref(x_157);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 1, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_163);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec_ref(x_19);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_166 = lean_ctor_get(x_155, 0);
lean_inc(x_166);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 x_167 = x_155;
} else {
 lean_dec_ref(x_155);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 1, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_166);
return x_168;
}
}
}
}
else
{
uint8_t x_169; 
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_169 = !lean_is_exclusive(x_129);
if (x_169 == 0)
{
return x_129;
}
else
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_ctor_get(x_129, 0);
lean_inc(x_170);
lean_dec(x_129);
x_171 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_171, 0, x_170);
return x_171;
}
}
}
}
else
{
lean_object* x_172; 
lean_dec_ref(x_31);
lean_dec(x_10);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_172 = l_Lean_Meta_DefEq_isInstLTNat(x_26, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_172) == 0)
{
uint8_t x_173; 
x_173 = !lean_is_exclusive(x_172);
if (x_173 == 0)
{
lean_object* x_174; uint8_t x_175; 
x_174 = lean_ctor_get(x_172, 0);
x_175 = lean_unbox(x_174);
lean_dec(x_174);
if (x_175 == 0)
{
lean_object* x_176; 
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_176 = lean_box(0);
lean_ctor_set(x_172, 0, x_176);
return x_172;
}
else
{
lean_object* x_177; 
lean_free_object(x_172);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_177 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_16, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
lean_dec_ref(x_177);
x_179 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_179) == 0)
{
uint8_t x_180; 
x_180 = !lean_is_exclusive(x_179);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_181 = lean_ctor_get(x_179, 0);
x_182 = l_Nat_Linear_Expr_inc(x_178);
x_183 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_181);
lean_ctor_set_uint8(x_183, sizeof(void*)*2, x_29);
x_184 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_179, 0, x_184);
return x_179;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_185 = lean_ctor_get(x_179, 0);
lean_inc(x_185);
lean_dec(x_179);
x_186 = l_Nat_Linear_Expr_inc(x_178);
x_187 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_185);
lean_ctor_set_uint8(x_187, sizeof(void*)*2, x_29);
x_188 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_188, 0, x_187);
x_189 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_189, 0, x_188);
return x_189;
}
}
else
{
uint8_t x_190; 
lean_dec(x_178);
x_190 = !lean_is_exclusive(x_179);
if (x_190 == 0)
{
return x_179;
}
else
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_ctor_get(x_179, 0);
lean_inc(x_191);
lean_dec(x_179);
x_192 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_192, 0, x_191);
return x_192;
}
}
}
else
{
uint8_t x_193; 
lean_dec_ref(x_19);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_193 = !lean_is_exclusive(x_177);
if (x_193 == 0)
{
return x_177;
}
else
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_ctor_get(x_177, 0);
lean_inc(x_194);
lean_dec(x_177);
x_195 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_195, 0, x_194);
return x_195;
}
}
}
}
else
{
lean_object* x_196; uint8_t x_197; 
x_196 = lean_ctor_get(x_172, 0);
lean_inc(x_196);
lean_dec(x_172);
x_197 = lean_unbox(x_196);
lean_dec(x_196);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; 
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_198 = lean_box(0);
x_199 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_199, 0, x_198);
return x_199;
}
else
{
lean_object* x_200; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_200 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_16, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
lean_dec_ref(x_200);
x_202 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 x_204 = x_202;
} else {
 lean_dec_ref(x_202);
 x_204 = lean_box(0);
}
x_205 = l_Nat_Linear_Expr_inc(x_201);
x_206 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_203);
lean_ctor_set_uint8(x_206, sizeof(void*)*2, x_29);
x_207 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_207, 0, x_206);
if (lean_is_scalar(x_204)) {
 x_208 = lean_alloc_ctor(0, 1, 0);
} else {
 x_208 = x_204;
}
lean_ctor_set(x_208, 0, x_207);
return x_208;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_201);
x_209 = lean_ctor_get(x_202, 0);
lean_inc(x_209);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 x_210 = x_202;
} else {
 lean_dec_ref(x_202);
 x_210 = lean_box(0);
}
if (lean_is_scalar(x_210)) {
 x_211 = lean_alloc_ctor(1, 1, 0);
} else {
 x_211 = x_210;
}
lean_ctor_set(x_211, 0, x_209);
return x_211;
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec_ref(x_19);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_212 = lean_ctor_get(x_200, 0);
lean_inc(x_212);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 x_213 = x_200;
} else {
 lean_dec_ref(x_200);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(1, 1, 0);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_212);
return x_214;
}
}
}
}
else
{
uint8_t x_215; 
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_215 = !lean_is_exclusive(x_172);
if (x_215 == 0)
{
return x_172;
}
else
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_ctor_get(x_172, 0);
lean_inc(x_216);
lean_dec(x_172);
x_217 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_217, 0, x_216);
return x_217;
}
}
}
}
}
else
{
lean_object* x_218; 
lean_dec_ref(x_27);
lean_dec(x_10);
x_218 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_26, x_4);
if (lean_obj_tag(x_218) == 0)
{
uint8_t x_219; 
x_219 = !lean_is_exclusive(x_218);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_220 = lean_ctor_get(x_218, 0);
x_221 = l_Lean_Expr_cleanupAnnotations(x_220);
x_222 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__16;
x_223 = l_Lean_Expr_isConstOf(x_221, x_222);
lean_dec_ref(x_221);
if (x_223 == 0)
{
lean_object* x_224; 
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_224 = lean_box(0);
lean_ctor_set(x_218, 0, x_224);
return x_218;
}
else
{
lean_object* x_225; 
lean_free_object(x_218);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_225 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
lean_dec_ref(x_225);
x_227 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_16, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_227) == 0)
{
uint8_t x_228; 
x_228 = !lean_is_exclusive(x_227);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_227, 0);
x_230 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_230, 0, x_226);
lean_ctor_set(x_230, 1, x_229);
lean_ctor_set_uint8(x_230, sizeof(void*)*2, x_223);
x_231 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_227, 0, x_231);
return x_227;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_232 = lean_ctor_get(x_227, 0);
lean_inc(x_232);
lean_dec(x_227);
x_233 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_233, 0, x_226);
lean_ctor_set(x_233, 1, x_232);
lean_ctor_set_uint8(x_233, sizeof(void*)*2, x_223);
x_234 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_234, 0, x_233);
x_235 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_235, 0, x_234);
return x_235;
}
}
else
{
uint8_t x_236; 
lean_dec(x_226);
x_236 = !lean_is_exclusive(x_227);
if (x_236 == 0)
{
return x_227;
}
else
{
lean_object* x_237; lean_object* x_238; 
x_237 = lean_ctor_get(x_227, 0);
lean_inc(x_237);
lean_dec(x_227);
x_238 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_238, 0, x_237);
return x_238;
}
}
}
else
{
uint8_t x_239; 
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_239 = !lean_is_exclusive(x_225);
if (x_239 == 0)
{
return x_225;
}
else
{
lean_object* x_240; lean_object* x_241; 
x_240 = lean_ctor_get(x_225, 0);
lean_inc(x_240);
lean_dec(x_225);
x_241 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_241, 0, x_240);
return x_241;
}
}
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; 
x_242 = lean_ctor_get(x_218, 0);
lean_inc(x_242);
lean_dec(x_218);
x_243 = l_Lean_Expr_cleanupAnnotations(x_242);
x_244 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__16;
x_245 = l_Lean_Expr_isConstOf(x_243, x_244);
lean_dec_ref(x_243);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; 
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_246 = lean_box(0);
x_247 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_247, 0, x_246);
return x_247;
}
else
{
lean_object* x_248; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_248 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; 
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
lean_dec_ref(x_248);
x_250 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_16, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 x_252 = x_250;
} else {
 lean_dec_ref(x_250);
 x_252 = lean_box(0);
}
x_253 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_253, 0, x_249);
lean_ctor_set(x_253, 1, x_251);
lean_ctor_set_uint8(x_253, sizeof(void*)*2, x_245);
x_254 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_254, 0, x_253);
if (lean_is_scalar(x_252)) {
 x_255 = lean_alloc_ctor(0, 1, 0);
} else {
 x_255 = x_252;
}
lean_ctor_set(x_255, 0, x_254);
return x_255;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_249);
x_256 = lean_ctor_get(x_250, 0);
lean_inc(x_256);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 x_257 = x_250;
} else {
 lean_dec_ref(x_250);
 x_257 = lean_box(0);
}
if (lean_is_scalar(x_257)) {
 x_258 = lean_alloc_ctor(1, 1, 0);
} else {
 x_258 = x_257;
}
lean_ctor_set(x_258, 0, x_256);
return x_258;
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_259 = lean_ctor_get(x_248, 0);
lean_inc(x_259);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 x_260 = x_248;
} else {
 lean_dec_ref(x_248);
 x_260 = lean_box(0);
}
if (lean_is_scalar(x_260)) {
 x_261 = lean_alloc_ctor(1, 1, 0);
} else {
 x_261 = x_260;
}
lean_ctor_set(x_261, 0, x_259);
return x_261;
}
}
}
}
else
{
uint8_t x_262; 
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_262 = !lean_is_exclusive(x_218);
if (x_262 == 0)
{
return x_218;
}
else
{
lean_object* x_263; lean_object* x_264; 
x_263 = lean_ctor_get(x_218, 0);
lean_inc(x_263);
lean_dec(x_218);
x_264 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_264, 0, x_263);
return x_264;
}
}
}
}
}
else
{
lean_object* x_265; 
lean_dec_ref(x_20);
lean_dec(x_10);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_265 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; 
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
lean_dec_ref(x_265);
x_267 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_16, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_267) == 0)
{
uint8_t x_268; 
x_268 = !lean_is_exclusive(x_267);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = lean_ctor_get(x_267, 0);
x_270 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_270, 0, x_266);
lean_ctor_set(x_270, 1, x_269);
lean_ctor_set_uint8(x_270, sizeof(void*)*2, x_22);
x_271 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_267, 0, x_271);
return x_267;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_272 = lean_ctor_get(x_267, 0);
lean_inc(x_272);
lean_dec(x_267);
x_273 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_273, 0, x_266);
lean_ctor_set(x_273, 1, x_272);
lean_ctor_set_uint8(x_273, sizeof(void*)*2, x_22);
x_274 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_274, 0, x_273);
x_275 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_275, 0, x_274);
return x_275;
}
}
else
{
uint8_t x_276; 
lean_dec(x_266);
x_276 = !lean_is_exclusive(x_267);
if (x_276 == 0)
{
return x_267;
}
else
{
lean_object* x_277; lean_object* x_278; 
x_277 = lean_ctor_get(x_267, 0);
lean_inc(x_277);
lean_dec(x_267);
x_278 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_278, 0, x_277);
return x_278;
}
}
}
else
{
uint8_t x_279; 
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_279 = !lean_is_exclusive(x_265);
if (x_279 == 0)
{
return x_265;
}
else
{
lean_object* x_280; lean_object* x_281; 
x_280 = lean_ctor_get(x_265, 0);
lean_inc(x_280);
lean_dec(x_265);
x_281 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_281, 0, x_280);
return x_281;
}
}
}
}
else
{
lean_object* x_282; 
lean_dec_ref(x_20);
lean_dec(x_10);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_282 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; 
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
lean_dec_ref(x_282);
x_284 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_16, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_284) == 0)
{
uint8_t x_285; 
x_285 = !lean_is_exclusive(x_284);
if (x_285 == 0)
{
lean_object* x_286; uint8_t x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_286 = lean_ctor_get(x_284, 0);
x_287 = 0;
x_288 = l_Nat_Linear_Expr_inc(x_283);
x_289 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_286);
lean_ctor_set_uint8(x_289, sizeof(void*)*2, x_287);
x_290 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_284, 0, x_290);
return x_284;
}
else
{
lean_object* x_291; uint8_t x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_291 = lean_ctor_get(x_284, 0);
lean_inc(x_291);
lean_dec(x_284);
x_292 = 0;
x_293 = l_Nat_Linear_Expr_inc(x_283);
x_294 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_291);
lean_ctor_set_uint8(x_294, sizeof(void*)*2, x_292);
x_295 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_295, 0, x_294);
x_296 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_296, 0, x_295);
return x_296;
}
}
else
{
uint8_t x_297; 
lean_dec(x_283);
x_297 = !lean_is_exclusive(x_284);
if (x_297 == 0)
{
return x_284;
}
else
{
lean_object* x_298; lean_object* x_299; 
x_298 = lean_ctor_get(x_284, 0);
lean_inc(x_298);
lean_dec(x_284);
x_299 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_299, 0, x_298);
return x_299;
}
}
}
else
{
uint8_t x_300; 
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_300 = !lean_is_exclusive(x_282);
if (x_300 == 0)
{
return x_282;
}
else
{
lean_object* x_301; lean_object* x_302; 
x_301 = lean_ctor_get(x_282, 0);
lean_inc(x_301);
lean_dec(x_282);
x_302 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_302, 0, x_301);
return x_302;
}
}
}
}
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
if (lean_is_scalar(x_10)) {
 x_12 = lean_alloc_ctor(0, 1, 0);
} else {
 x_12 = x_10;
}
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
uint8_t x_303; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_303 = !lean_is_exclusive(x_8);
if (x_303 == 0)
{
return x_8;
}
else
{
lean_object* x_304; lean_object* x_305; 
x_304 = lean_ctor_get(x_8, 0);
lean_inc(x_304);
lean_dec(x_8);
x_305 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_305, 0, x_304);
return x_305;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__2;
x_2 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__3;
x_8 = lean_st_mk_ref(x_7);
lean_inc(x_8);
x_9 = lean_apply_6(x_1, x_8, x_2, x_3, x_4, x_5, lean_box(0));
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_st_ref_get(x_8);
lean_dec(x_8);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_9, 0, x_16);
return x_9;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_st_ref_get(x_8);
lean_dec(x_8);
x_19 = lean_ctor_get(x_18, 1);
lean_inc_ref(x_19);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_20 = x_18;
} else {
 lean_dec_ref(x_18);
 x_20 = lean_box(0);
}
if (lean_is_scalar(x_20)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_20;
}
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_8);
x_23 = !lean_is_exclusive(x_9);
if (x_23 == 0)
{
return x_9;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_9, 0);
lean_inc(x_24);
lean_dec(x_9);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___boxed), 7, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(x_7, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_dec_eq(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_8, 0);
lean_dec(x_16);
x_17 = 1;
x_18 = l_Lean_sortExprs(x_11, x_17);
lean_dec(x_11);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(x_21, x_10);
lean_dec(x_21);
lean_ctor_set(x_18, 1, x_20);
lean_ctor_set(x_18, 0, x_22);
lean_ctor_set(x_8, 0, x_18);
return x_8;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_25 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(x_24, x_10);
lean_dec(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
lean_ctor_set(x_8, 0, x_26);
return x_8;
}
}
else
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_8);
x_27 = 1;
x_28 = l_Lean_sortExprs(x_11, x_27);
lean_dec(x_11);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_31 = x_28;
} else {
 lean_dec_ref(x_28);
 x_31 = lean_box(0);
}
x_32 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Nat_Linear_Expr_applyPerm_go(x_30, x_10);
lean_dec(x_30);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_29);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
else
{
lean_dec(x_11);
lean_dec(x_10);
return x_8;
}
}
else
{
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_Arith_Nat_toLinearExpr(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearCnstr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___boxed), 7, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(x_7, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 1)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_array_get_size(x_13);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_dec_le(x_17, x_18);
if (x_19 == 0)
{
uint8_t x_20; lean_object* x_21; uint8_t x_22; 
lean_free_object(x_10);
x_20 = 1;
x_21 = l_Lean_sortExprs(x_13, x_20);
lean_dec(x_13);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = l_Nat_Linear_ExprCnstr_applyPerm(x_24, x_16);
lean_dec(x_24);
lean_ctor_set(x_21, 1, x_23);
lean_ctor_set(x_21, 0, x_25);
lean_ctor_set(x_11, 0, x_21);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = l_Nat_Linear_ExprCnstr_applyPerm(x_27, x_16);
lean_dec(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_11, 0, x_29);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
}
else
{
lean_ctor_set(x_10, 0, x_16);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_11, 0);
lean_inc(x_30);
lean_dec(x_11);
x_31 = lean_array_get_size(x_13);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_dec_le(x_31, x_32);
if (x_33 == 0)
{
uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_free_object(x_10);
x_34 = 1;
x_35 = l_Lean_sortExprs(x_13, x_34);
lean_dec(x_13);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_38 = x_35;
} else {
 lean_dec_ref(x_35);
 x_38 = lean_box(0);
}
x_39 = l_Nat_Linear_ExprCnstr_applyPerm(x_37, x_30);
lean_dec(x_37);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_36);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_8, 0, x_41);
return x_8;
}
else
{
lean_object* x_42; 
lean_ctor_set(x_10, 0, x_30);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_10);
lean_ctor_set(x_8, 0, x_42);
return x_8;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_43 = lean_ctor_get(x_10, 1);
lean_inc(x_43);
lean_dec(x_10);
x_44 = lean_ctor_get(x_11, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_45 = x_11;
} else {
 lean_dec_ref(x_11);
 x_45 = lean_box(0);
}
x_46 = lean_array_get_size(x_43);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_dec_le(x_46, x_47);
if (x_48 == 0)
{
uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_49 = 1;
x_50 = l_Lean_sortExprs(x_43, x_49);
lean_dec(x_43);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
x_54 = l_Nat_Linear_ExprCnstr_applyPerm(x_52, x_44);
lean_dec(x_52);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_51);
if (lean_is_scalar(x_45)) {
 x_56 = lean_alloc_ctor(1, 1, 0);
} else {
 x_56 = x_45;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_8, 0, x_56);
return x_8;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_44);
lean_ctor_set(x_57, 1, x_43);
if (lean_is_scalar(x_45)) {
 x_58 = lean_alloc_ctor(1, 1, 0);
} else {
 x_58 = x_45;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_8, 0, x_58);
return x_8;
}
}
}
else
{
lean_object* x_59; 
lean_dec(x_11);
lean_dec(x_10);
x_59 = lean_box(0);
lean_ctor_set(x_8, 0, x_59);
return x_8;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_8, 0);
lean_inc(x_60);
lean_dec(x_8);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
if (lean_obj_tag(x_61) == 1)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
x_64 = lean_ctor_get(x_61, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_65 = x_61;
} else {
 lean_dec_ref(x_61);
 x_65 = lean_box(0);
}
x_66 = lean_array_get_size(x_62);
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_nat_dec_le(x_66, x_67);
if (x_68 == 0)
{
uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_63);
x_69 = 1;
x_70 = l_Lean_sortExprs(x_62, x_69);
lean_dec(x_62);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_73 = x_70;
} else {
 lean_dec_ref(x_70);
 x_73 = lean_box(0);
}
x_74 = l_Nat_Linear_ExprCnstr_applyPerm(x_72, x_64);
lean_dec(x_72);
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_73;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_71);
if (lean_is_scalar(x_65)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_65;
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
if (lean_is_scalar(x_63)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_63;
}
lean_ctor_set(x_78, 0, x_64);
lean_ctor_set(x_78, 1, x_62);
if (lean_is_scalar(x_65)) {
 x_79 = lean_alloc_ctor(1, 1, 0);
} else {
 x_79 = x_65;
}
lean_ctor_set(x_79, 0, x_78);
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_61);
lean_dec(x_60);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
}
else
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_8);
if (x_83 == 0)
{
return x_8;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_8, 0);
lean_inc(x_84);
lean_dec(x_8);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearCnstr_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_Arith_Nat_toLinearCnstr_x3f(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__16;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_mkNatLit(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_dec_lt(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_1);
x_10 = l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__0;
x_11 = l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1;
x_12 = l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__3;
x_13 = l_Lean_RArray_toExpr___redArg(x_11, x_10, x_12, x_2, x_3, x_4, x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__0;
x_15 = l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1;
x_16 = l_Lean_RArray_ofArray___redArg(x_1);
x_17 = l_Lean_RArray_toExpr___redArg(x_15, x_14, x_16, x_2, x_3, x_4, x_5);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* initialize_Lean_Util_SortExprs(uint8_t builtin);
lean_object* initialize_Lean_Meta_KExprMap(uint8_t builtin);
lean_object* initialize_Lean_Data_RArray(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
lean_object* initialize_Lean_Meta_Offset(uint8_t builtin);
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
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_NatInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Offset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__0 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__0);
l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__1 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__1);
l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__2 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__2);
l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__3);
l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__4);
l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__5 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__5);
l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__6 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__6);
l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__7 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__7();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__7);
l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__8 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__8();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__8);
l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__9 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__9();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__9);
l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__10 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__10();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__10);
l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__11 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__11();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__11);
l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__12 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__12();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__12);
l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__13 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__13();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__13);
l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__14 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__14();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__14);
l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__15 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__15();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__15);
l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__16 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__16();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean_repr___closed__16);
l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean___closed__0 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean___closed__0);
l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean);
l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__0 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__0);
l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__1 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__1);
l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__2 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__2);
l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__3 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__3);
l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__4 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__4);
l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__5 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__5);
l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__6 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__6);
l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__7);
l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__8 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__8();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__8);
l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__9 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__9();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__9);
l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__10 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__10();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__10);
l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__11 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__11();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__11);
l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__12);
l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__13 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__13();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__13);
l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__14 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__14();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__14);
l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__15 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__15();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__15);
l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__16 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__16();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__16);
l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__17);
l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__18 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__18();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__18);
l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__19 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__19();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean_repr___redArg___closed__19);
l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean___closed__0 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean___closed__0);
l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean);
l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__0 = _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__0();
lean_mark_persistent(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__0);
l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__1 = _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__1();
lean_mark_persistent(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__1);
l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__2 = _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__2();
lean_mark_persistent(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__2);
l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__3 = _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__3();
lean_mark_persistent(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__3);
l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__4 = _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__4();
lean_mark_persistent(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__4);
l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__5 = _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__5();
lean_mark_persistent(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__5);
l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__6 = _init_l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__6();
lean_mark_persistent(l_Prod_repr___at___00List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0_spec__0___redArg___closed__6);
l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__0 = _init_l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__0();
lean_mark_persistent(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__0);
l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__1 = _init_l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__1();
lean_mark_persistent(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__1);
l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__2 = _init_l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__2();
lean_mark_persistent(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__2);
l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__3 = _init_l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__3();
lean_mark_persistent(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__3);
l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__4 = _init_l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__4();
lean_mark_persistent(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__4);
l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__5 = _init_l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__5();
lean_mark_persistent(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__5);
l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__6 = _init_l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__6();
lean_mark_persistent(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__6);
l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__7 = _init_l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__7();
lean_mark_persistent(l_List_repr___at___00Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean_repr_spec__0___redArg___closed__7);
l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean___closed__0 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean___closed__0);
l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean = _init_l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean);
l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0 = _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0);
l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1 = _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1);
l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2 = _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2);
l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__3 = _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__3);
l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4 = _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4);
l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__5 = _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__5);
l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__6 = _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__6);
l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7 = _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7);
l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__8 = _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__8();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__8);
l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__9 = _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__9();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__9);
l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10 = _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10);
l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__11 = _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__11();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__11);
l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__12 = _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__12();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__12);
l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13 = _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13);
l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__14 = _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__14();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__14);
l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__15 = _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__15();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__15);
l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16 = _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16);
l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__17 = _init_l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__17();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__17);
l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__0 = _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__0);
l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1 = _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1);
l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__2 = _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__2);
l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__3 = _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__3);
l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr = _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr);
l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__0 = _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__0);
l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__1 = _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__1);
l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2 = _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2);
l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__3 = _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__3);
l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__4 = _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__4);
l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__5 = _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__5);
l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__6 = _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__6);
l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__7 = _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__7();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__7);
l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__8 = _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__8();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__8);
l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__9 = _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__9();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__9);
l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__10 = _init_l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__10();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__10);
l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__0 = _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__0);
l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1 = _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1);
l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__2 = _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__2);
l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__3 = _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__3);
l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr = _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__0 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__0);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__1 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__1);
l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__0 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__0);
l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__1);
l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__2);
l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__3 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__3);
l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__4 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__4);
l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__6 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__6);
l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__5 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__5);
l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__7 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__7);
l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__8 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__8);
l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__9 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__9);
l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__10 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__10);
l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__11 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__11();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__11);
l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__13 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__13();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__13);
l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__12 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__12();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__12);
l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__14 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__14();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__14);
l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__16 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__16();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__16);
l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__15 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__15();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__15);
l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__17 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__17();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__17);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__0 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__0);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__1 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__1);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__2 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__2);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__3 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__3);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__4 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__4);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__5 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__5);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__6 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__6);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__7 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__7();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__7);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__8 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__8();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__8);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__9 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__9();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__9);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__10 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__10();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__10);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__11 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__11();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__11);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__12 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__12();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__12);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__13 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__13();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__13);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__14 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__14();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__14);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__15 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__15();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__15);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__16 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__16();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__16);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__0 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__0);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__1 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__1);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__2 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__2);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__3 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__3);
l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__0 = _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__0);
l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1 = _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1);
l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__2 = _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__2);
l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__3 = _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
