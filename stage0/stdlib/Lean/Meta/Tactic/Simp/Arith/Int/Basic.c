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
static lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_adapter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_denoteExpr_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Int_Linear_instReprPoly__lean___closed__0;
lean_object* l_Lean_mkNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__20;
lean_object* l_Lean_Meta_DefEq_isInstMulInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_denoteExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__7;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__13;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__7;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__2;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___closed__1;
LEAN_EXPORT lean_object* l_Int_Linear_instReprPoly__lean_repr___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__18;
static lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__11;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__11;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__13;
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__0;
static lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1;
static lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__3;
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_mkIntSub(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__5;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__17;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__16;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__8;
static lean_object* l_Int_Linear_instReprPoly__lean_repr___closed__5;
LEAN_EXPORT lean_object* l_Int_Linear_Expr_denoteExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__2;
static lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__14;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr___redArg(lean_object*, lean_object*);
static lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__18;
static lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__20;
static lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_adapter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__18;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_Linear_instReprExpr__lean___closed__0;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__3;
lean_object* l_Lean_mkIntMul(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__6;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0;
lean_object* l_Lean_RArray_toExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_Linear_instReprPoly__lean_repr___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprPoly;
lean_object* l_Lean_Level_ofNat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_denoteExpr_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr___lam__0___boxed(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_Linear_instReprPoly__lean_repr___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DefEq_isInstLTInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__12;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__3;
static lean_object* l_Int_Linear_instReprPoly__lean_repr___closed__2;
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprExpr;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__15;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_sortExprs(lean_object*, uint8_t);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__11;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__10;
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_KExprMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__5;
lean_object* l_Lean_Meta_KExprMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14;
static lean_object* l_Int_Linear_instReprPoly__lean_repr___closed__0;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__5;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__7;
LEAN_EXPORT lean_object* l_Int_Linear_Expr_applyPerm___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__14;
lean_object* l_Lean_RArray_ofArray___redArg(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__2;
static lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__3;
lean_object* lean_st_mk_ref(lean_object*);
static lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__9;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0;
LEAN_EXPORT lean_object* l_Int_Linear_instReprExpr__lean_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__1;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__19;
static lean_object* l_Int_Linear_instReprPoly__lean_repr___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DefEq_isInstAddInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DefEq_isInstNegInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__8;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__12;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__3;
static lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__2;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__2;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr___lam__0(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__1;
lean_object* l_Lean_Meta_DefEq_isInstHAddInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_denoteExpr_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__0;
lean_object* l_Lean_Meta_DefEq_isInstHSubInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__7;
static lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__12;
static lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__13;
lean_object* l_Lean_Meta_DefEq_isInstHMulInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__9;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__13;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4;
lean_object* l_Lean_mkIntLit(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_instReprPoly__lean;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__5;
lean_object* l_Lean_mkIntAdd(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__3;
static lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_applyPerm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__18;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toLinearExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_instReprExpr__lean_repr___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__2;
static lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__3;
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__17;
LEAN_EXPORT lean_object* l_Int_Linear_instReprPoly__lean_repr(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__4;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__0;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__15;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__19;
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_denoteExpr_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__2;
static lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__19;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__9;
static lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__8;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__21;
size_t lean_usize_sub(size_t, size_t);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__4;
static lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__1;
lean_object* l_Lean_Meta_DefEq_isInstLEInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__0;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__10;
static lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__16;
LEAN_EXPORT lean_object* l_Int_Linear_instReprExpr__lean;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__8;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__22;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__6;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_denoteExpr___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__12;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DefEq_isInstDvdInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__15;
static lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__0;
static lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__1;
lean_object* l_Lean_Meta_DefEq_isInstSubInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__5;
LEAN_EXPORT lean_object* l_Int_Linear_Expr_denoteExpr___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__16;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__2;
static lean_object* l_Int_Linear_instReprPoly__lean_repr___closed__1;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__15;
lean_object* l_Lean_mkIntNeg(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__1;
static lean_object* l_Int_Linear_instReprExpr__lean_repr___closed__6;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__7;
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__9;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_8);
lean_dec_ref(x_2);
x_9 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0;
x_10 = lean_int_dec_eq(x_6, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_7);
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_1 = x_13;
x_2 = x_8;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_7);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_1 = x_16;
x_2 = x_8;
goto _start;
}
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec_ref(x_1);
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1;
x_22 = lean_int_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_2);
return x_23;
}
else
{
lean_free_object(x_2);
lean_dec(x_20);
return x_18;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_2, 0);
lean_inc(x_24);
lean_dec(x_2);
x_25 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1;
x_26 = lean_int_dec_eq(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
else
{
lean_dec(x_24);
return x_18;
}
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_1);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_ctor_get(x_1, 0);
x_31 = lean_ctor_get(x_2, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_2, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_33);
lean_dec_ref(x_2);
x_34 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0;
x_35 = lean_int_dec_eq(x_31, x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_32);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_38, 0, x_30);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_1, 0, x_38);
x_2 = x_33;
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_31);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_32);
x_41 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_41, 0, x_30);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_1, 0, x_41);
x_2 = x_33;
goto _start;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_43 = lean_ctor_get(x_1, 0);
lean_inc(x_43);
lean_dec(x_1);
x_44 = lean_ctor_get(x_2, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_2, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_46);
lean_dec_ref(x_2);
x_47 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0;
x_48 = lean_int_dec_eq(x_44, x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_45);
x_50 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_51, 0, x_43);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_1 = x_52;
x_2 = x_46;
goto _start;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_44);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_45);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_43);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_1 = x_56;
x_2 = x_46;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_toExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
x_18 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(x_2, x_17);
lean_dec(x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(lean_object* x_1, lean_object* x_2) {
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
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0___redArg(x_1, x_3);
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
x_13 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_1, x_11);
x_14 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_1, x_12);
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
x_17 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_1, x_15);
x_18 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_1, x_16);
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
x_23 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_1, x_21);
x_24 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_1, x_22);
lean_ctor_set(x_2, 1, x_24);
lean_ctor_set(x_2, 0, x_23);
return x_2;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_2);
x_27 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_1, x_25);
x_28 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_1, x_26);
x_29 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
case 4:
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_2);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_2, 0);
x_32 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_1, x_31);
lean_ctor_set(x_2, 0, x_32);
return x_2;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
lean_dec(x_2);
x_34 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_1, x_33);
x_35 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
case 5:
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_2);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_2, 1);
x_38 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_1, x_37);
lean_ctor_set(x_2, 1, x_38);
return x_2;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_2, 0);
x_40 = lean_ctor_get(x_2, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_2);
x_41 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_1, x_40);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
default: 
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_2);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_2, 0);
x_45 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_1, x_44);
lean_ctor_set(x_2, 0, x_45);
return x_2;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_2, 0);
x_47 = lean_ctor_get(x_2, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_2);
x_48 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_1, x_46);
x_49 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_applyPerm(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_applyPerm___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_Linear_Expr_applyPerm(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Int_Linear_instReprPoly__lean_repr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int.Linear.Poly.num", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Int_Linear_instReprPoly__lean_repr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Int_Linear_instReprPoly__lean_repr___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Int_Linear_instReprPoly__lean_repr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Int_Linear_instReprPoly__lean_repr___closed__1;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_Linear_instReprPoly__lean_repr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Int_Linear_instReprPoly__lean_repr___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int.Linear.Poly.add", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Int_Linear_instReprPoly__lean_repr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Int_Linear_instReprPoly__lean_repr___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Int_Linear_instReprPoly__lean_repr___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Int_Linear_instReprPoly__lean_repr___closed__5;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_instReprPoly__lean_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_25; uint8_t x_26; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_13 = x_1;
} else {
 lean_dec_ref(x_1);
 x_13 = lean_box(0);
}
x_25 = lean_unsigned_to_nat(1024u);
x_26 = lean_nat_dec_le(x_25, x_2);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = l_Int_Linear_instReprPoly__lean_repr___closed__3;
x_14 = x_27;
goto block_24;
}
else
{
lean_object* x_28; 
x_28 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0;
x_14 = x_28;
goto block_24;
}
block_24:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = l_Int_Linear_instReprPoly__lean_repr___closed__2;
x_16 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1;
x_17 = lean_int_dec_lt(x_12, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Int_repr(x_12);
lean_dec(x_12);
if (lean_is_scalar(x_13)) {
 x_19 = lean_alloc_ctor(3, 1, 0);
} else {
 x_19 = x_13;
 lean_ctor_set_tag(x_19, 3);
}
lean_ctor_set(x_19, 0, x_18);
x_3 = x_14;
x_4 = x_15;
x_5 = x_19;
goto block_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_unsigned_to_nat(1024u);
x_21 = l_Int_repr(x_12);
lean_dec(x_12);
if (lean_is_scalar(x_13)) {
 x_22 = lean_alloc_ctor(3, 1, 0);
} else {
 x_22 = x_13;
 lean_ctor_set_tag(x_22, 3);
}
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Repr_addAppParen(x_22, x_20);
x_3 = x_14;
x_4 = x_15;
x_5 = x_23;
goto block_11;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_50; uint8_t x_61; 
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_31);
lean_dec_ref(x_1);
x_32 = lean_unsigned_to_nat(1024u);
x_61 = lean_nat_dec_le(x_32, x_2);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = l_Int_Linear_instReprPoly__lean_repr___closed__3;
x_50 = x_62;
goto block_60;
}
else
{
lean_object* x_63; 
x_63 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0;
x_50 = x_63;
goto block_60;
}
block_49:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_36);
lean_inc(x_35);
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
x_39 = l_Nat_reprFast(x_30);
x_40 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_35);
x_43 = l_Int_Linear_instReprPoly__lean_repr(x_31, x_32);
x_44 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_45, 0, x_34);
lean_ctor_set(x_45, 1, x_44);
x_46 = 0;
x_47 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_46);
x_48 = l_Repr_addAppParen(x_47, x_2);
return x_48;
}
block_60:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_box(1);
x_52 = l_Int_Linear_instReprPoly__lean_repr___closed__6;
x_53 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1;
x_54 = lean_int_dec_lt(x_29, x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = l_Int_repr(x_29);
lean_dec(x_29);
x_56 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_33 = x_52;
x_34 = x_50;
x_35 = x_51;
x_36 = x_56;
goto block_49;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = l_Int_repr(x_29);
lean_dec(x_29);
x_58 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = l_Repr_addAppParen(x_58, x_32);
x_33 = x_52;
x_34 = x_50;
x_35 = x_51;
x_36 = x_59;
goto block_49;
}
}
}
block_11:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
x_8 = 0;
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_8);
x_10 = l_Repr_addAppParen(x_9, x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_instReprPoly__lean_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_Linear_instReprPoly__lean_repr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Int_Linear_instReprPoly__lean___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_Linear_instReprPoly__lean_repr___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Int_Linear_instReprPoly__lean() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_Linear_instReprPoly__lean___closed__0;
return x_1;
}
}
static lean_object* _init_l_Int_Linear_instReprExpr__lean_repr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int.Linear.Expr.num", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Int_Linear_instReprExpr__lean_repr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Int_Linear_instReprExpr__lean_repr___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Int_Linear_instReprExpr__lean_repr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Int_Linear_instReprExpr__lean_repr___closed__1;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_Linear_instReprExpr__lean_repr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int.Linear.Expr.var", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Int_Linear_instReprExpr__lean_repr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Int_Linear_instReprExpr__lean_repr___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Int_Linear_instReprExpr__lean_repr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Int_Linear_instReprExpr__lean_repr___closed__4;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_Linear_instReprExpr__lean_repr___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int.Linear.Expr.add", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Int_Linear_instReprExpr__lean_repr___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Int_Linear_instReprExpr__lean_repr___closed__6;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Int_Linear_instReprExpr__lean_repr___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Int_Linear_instReprExpr__lean_repr___closed__7;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_Linear_instReprExpr__lean_repr___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int.Linear.Expr.sub", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Int_Linear_instReprExpr__lean_repr___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Int_Linear_instReprExpr__lean_repr___closed__9;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Int_Linear_instReprExpr__lean_repr___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Int_Linear_instReprExpr__lean_repr___closed__10;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_Linear_instReprExpr__lean_repr___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int.Linear.Expr.neg", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Int_Linear_instReprExpr__lean_repr___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Int_Linear_instReprExpr__lean_repr___closed__12;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Int_Linear_instReprExpr__lean_repr___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Int_Linear_instReprExpr__lean_repr___closed__13;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_Linear_instReprExpr__lean_repr___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int.Linear.Expr.mulL", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Int_Linear_instReprExpr__lean_repr___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Int_Linear_instReprExpr__lean_repr___closed__15;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Int_Linear_instReprExpr__lean_repr___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Int_Linear_instReprExpr__lean_repr___closed__16;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_Linear_instReprExpr__lean_repr___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int.Linear.Expr.mulR", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Int_Linear_instReprExpr__lean_repr___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Int_Linear_instReprExpr__lean_repr___closed__18;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Int_Linear_instReprExpr__lean_repr___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Int_Linear_instReprExpr__lean_repr___closed__19;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_instReprExpr__lean_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_34; uint8_t x_35; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_22 = x_1;
} else {
 lean_dec_ref(x_1);
 x_22 = lean_box(0);
}
x_34 = lean_unsigned_to_nat(1024u);
x_35 = lean_nat_dec_le(x_34, x_2);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Int_Linear_instReprPoly__lean_repr___closed__3;
x_23 = x_36;
goto block_33;
}
else
{
lean_object* x_37; 
x_37 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0;
x_23 = x_37;
goto block_33;
}
block_33:
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = l_Int_Linear_instReprExpr__lean_repr___closed__2;
x_25 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1;
x_26 = lean_int_dec_lt(x_21, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Int_repr(x_21);
lean_dec(x_21);
if (lean_is_scalar(x_22)) {
 x_28 = lean_alloc_ctor(3, 1, 0);
} else {
 x_28 = x_22;
 lean_ctor_set_tag(x_28, 3);
}
lean_ctor_set(x_28, 0, x_27);
x_12 = x_23;
x_13 = x_24;
x_14 = x_28;
goto block_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_unsigned_to_nat(1024u);
x_30 = l_Int_repr(x_21);
lean_dec(x_21);
if (lean_is_scalar(x_22)) {
 x_31 = lean_alloc_ctor(3, 1, 0);
} else {
 x_31 = x_22;
 lean_ctor_set_tag(x_31, 3);
}
lean_ctor_set(x_31, 0, x_30);
x_32 = l_Repr_addAppParen(x_31, x_29);
x_12 = x_23;
x_13 = x_24;
x_14 = x_32;
goto block_20;
}
}
}
case 1:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_50; uint8_t x_51; 
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_39 = x_1;
} else {
 lean_dec_ref(x_1);
 x_39 = lean_box(0);
}
x_50 = lean_unsigned_to_nat(1024u);
x_51 = lean_nat_dec_le(x_50, x_2);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = l_Int_Linear_instReprPoly__lean_repr___closed__3;
x_40 = x_52;
goto block_49;
}
else
{
lean_object* x_53; 
x_53 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0;
x_40 = x_53;
goto block_49;
}
block_49:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_41 = l_Int_Linear_instReprExpr__lean_repr___closed__5;
x_42 = l_Nat_reprFast(x_38);
if (lean_is_scalar(x_39)) {
 x_43 = lean_alloc_ctor(3, 1, 0);
} else {
 x_43 = x_39;
 lean_ctor_set_tag(x_43, 3);
}
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_44);
x_46 = 0;
x_47 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_46);
x_48 = l_Repr_addAppParen(x_47, x_2);
return x_48;
}
}
case 2:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_71; 
x_54 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_54);
x_55 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_55);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_56 = x_1;
} else {
 lean_dec_ref(x_1);
 x_56 = lean_box(0);
}
x_57 = lean_unsigned_to_nat(1024u);
x_71 = lean_nat_dec_le(x_57, x_2);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = l_Int_Linear_instReprPoly__lean_repr___closed__3;
x_58 = x_72;
goto block_70;
}
else
{
lean_object* x_73; 
x_73 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0;
x_58 = x_73;
goto block_70;
}
block_70:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; 
x_59 = lean_box(1);
x_60 = l_Int_Linear_instReprExpr__lean_repr___closed__8;
x_61 = l_Int_Linear_instReprExpr__lean_repr(x_54, x_57);
if (lean_is_scalar(x_56)) {
 x_62 = lean_alloc_ctor(5, 2, 0);
} else {
 x_62 = x_56;
 lean_ctor_set_tag(x_62, 5);
}
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_59);
x_64 = l_Int_Linear_instReprExpr__lean_repr(x_55, x_57);
x_65 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_66, 0, x_58);
lean_ctor_set(x_66, 1, x_65);
x_67 = 0;
x_68 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set_uint8(x_68, sizeof(void*)*1, x_67);
x_69 = l_Repr_addAppParen(x_68, x_2);
return x_69;
}
}
case 3:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_91; 
x_74 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_74);
x_75 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_75);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_76 = x_1;
} else {
 lean_dec_ref(x_1);
 x_76 = lean_box(0);
}
x_77 = lean_unsigned_to_nat(1024u);
x_91 = lean_nat_dec_le(x_77, x_2);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = l_Int_Linear_instReprPoly__lean_repr___closed__3;
x_78 = x_92;
goto block_90;
}
else
{
lean_object* x_93; 
x_93 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0;
x_78 = x_93;
goto block_90;
}
block_90:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; 
x_79 = lean_box(1);
x_80 = l_Int_Linear_instReprExpr__lean_repr___closed__11;
x_81 = l_Int_Linear_instReprExpr__lean_repr(x_74, x_77);
if (lean_is_scalar(x_76)) {
 x_82 = lean_alloc_ctor(5, 2, 0);
} else {
 x_82 = x_76;
 lean_ctor_set_tag(x_82, 5);
}
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_79);
x_84 = l_Int_Linear_instReprExpr__lean_repr(x_75, x_77);
x_85 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_86, 0, x_78);
lean_ctor_set(x_86, 1, x_85);
x_87 = 0;
x_88 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set_uint8(x_88, sizeof(void*)*1, x_87);
x_89 = l_Repr_addAppParen(x_88, x_2);
return x_89;
}
}
case 4:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_105; 
x_94 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_94);
lean_dec_ref(x_1);
x_95 = lean_unsigned_to_nat(1024u);
x_105 = lean_nat_dec_le(x_95, x_2);
if (x_105 == 0)
{
lean_object* x_106; 
x_106 = l_Int_Linear_instReprPoly__lean_repr___closed__3;
x_96 = x_106;
goto block_104;
}
else
{
lean_object* x_107; 
x_107 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0;
x_96 = x_107;
goto block_104;
}
block_104:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; 
x_97 = l_Int_Linear_instReprExpr__lean_repr___closed__14;
x_98 = l_Int_Linear_instReprExpr__lean_repr(x_94, x_95);
x_99 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_100, 0, x_96);
lean_ctor_set(x_100, 1, x_99);
x_101 = 0;
x_102 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set_uint8(x_102, sizeof(void*)*1, x_101);
x_103 = l_Repr_addAppParen(x_102, x_2);
return x_103;
}
}
case 5:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_125; uint8_t x_136; 
x_108 = lean_ctor_get(x_1, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_109);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_110 = x_1;
} else {
 lean_dec_ref(x_1);
 x_110 = lean_box(0);
}
x_111 = lean_unsigned_to_nat(1024u);
x_136 = lean_nat_dec_le(x_111, x_2);
if (x_136 == 0)
{
lean_object* x_137; 
x_137 = l_Int_Linear_instReprPoly__lean_repr___closed__3;
x_125 = x_137;
goto block_135;
}
else
{
lean_object* x_138; 
x_138 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0;
x_125 = x_138;
goto block_135;
}
block_124:
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; 
if (lean_is_scalar(x_110)) {
 x_116 = lean_alloc_ctor(5, 2, 0);
} else {
 x_116 = x_110;
}
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_112);
x_118 = l_Int_Linear_instReprExpr__lean_repr(x_109, x_111);
x_119 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_120, 0, x_113);
lean_ctor_set(x_120, 1, x_119);
x_121 = 0;
x_122 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set_uint8(x_122, sizeof(void*)*1, x_121);
x_123 = l_Repr_addAppParen(x_122, x_2);
return x_123;
}
block_135:
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_126 = lean_box(1);
x_127 = l_Int_Linear_instReprExpr__lean_repr___closed__17;
x_128 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1;
x_129 = lean_int_dec_lt(x_108, x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = l_Int_repr(x_108);
lean_dec(x_108);
x_131 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_131, 0, x_130);
x_112 = x_126;
x_113 = x_125;
x_114 = x_127;
x_115 = x_131;
goto block_124;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = l_Int_repr(x_108);
lean_dec(x_108);
x_133 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_133, 0, x_132);
x_134 = l_Repr_addAppParen(x_133, x_111);
x_112 = x_126;
x_113 = x_125;
x_114 = x_127;
x_115 = x_134;
goto block_124;
}
}
}
default: 
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_157; 
x_139 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_139);
x_140 = lean_ctor_get(x_1, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_141 = x_1;
} else {
 lean_dec_ref(x_1);
 x_141 = lean_box(0);
}
x_142 = lean_unsigned_to_nat(1024u);
x_157 = lean_nat_dec_le(x_142, x_2);
if (x_157 == 0)
{
lean_object* x_158; 
x_158 = l_Int_Linear_instReprPoly__lean_repr___closed__3;
x_143 = x_158;
goto block_156;
}
else
{
lean_object* x_159; 
x_159 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0;
x_143 = x_159;
goto block_156;
}
block_156:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_144 = lean_box(1);
x_145 = l_Int_Linear_instReprExpr__lean_repr___closed__20;
x_146 = l_Int_Linear_instReprExpr__lean_repr(x_139, x_142);
if (lean_is_scalar(x_141)) {
 x_147 = lean_alloc_ctor(5, 2, 0);
} else {
 x_147 = x_141;
 lean_ctor_set_tag(x_147, 5);
}
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
x_148 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_144);
x_149 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1;
x_150 = lean_int_dec_lt(x_140, x_149);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = l_Int_repr(x_140);
lean_dec(x_140);
x_152 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_152, 0, x_151);
x_3 = x_143;
x_4 = x_148;
x_5 = x_152;
goto block_11;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = l_Int_repr(x_140);
lean_dec(x_140);
x_154 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_154, 0, x_153);
x_155 = l_Repr_addAppParen(x_154, x_142);
x_3 = x_143;
x_4 = x_148;
x_5 = x_155;
goto block_11;
}
}
}
}
block_11:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
x_8 = 0;
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_8);
x_10 = l_Repr_addAppParen(x_9, x_2);
return x_10;
}
block_20:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
x_17 = 0;
x_18 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_17);
x_19 = l_Repr_addAppParen(x_18, x_2);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_instReprExpr__lean_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_Linear_instReprExpr__lean_repr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Int_Linear_instReprExpr__lean___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_Linear_instReprExpr__lean_repr___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Int_Linear_instReprExpr__lean() {
_start:
{
lean_object* x_1; 
x_1 = l_Int_Linear_instReprExpr__lean___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Linear", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Poly", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("num", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__3;
x_2 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__2;
x_3 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1;
x_4 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__4;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Neg", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("neg", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__7;
x_2 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__6;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Level_ofNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__10;
x_2 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__8;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instNegInt", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14;
x_2 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__15;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("add", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17;
x_2 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__2;
x_3 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1;
x_4 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__18;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__5;
x_4 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1;
x_5 = lean_int_dec_le(x_4, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11;
x_7 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13;
x_8 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16;
x_9 = lean_int_neg(x_2);
lean_dec(x_2);
x_10 = l_Int_toNat(x_9);
lean_dec(x_9);
x_11 = l_Lean_instToExprInt_mkNat(x_10);
x_12 = l_Lean_mkApp3(x_6, x_7, x_8, x_11);
x_13 = l_Lean_Expr_app___override(x_3, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Int_toNat(x_2);
lean_dec(x_2);
x_15 = l_Lean_instToExprInt_mkNat(x_14);
x_16 = l_Lean_Expr_app___override(x_3, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_26; uint8_t x_27; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_19);
lean_dec_ref(x_1);
x_20 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__19;
x_26 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1;
x_27 = lean_int_dec_le(x_26, x_17);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11;
x_29 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13;
x_30 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16;
x_31 = lean_int_neg(x_17);
lean_dec(x_17);
x_32 = l_Int_toNat(x_31);
lean_dec(x_31);
x_33 = l_Lean_instToExprInt_mkNat(x_32);
x_34 = l_Lean_mkApp3(x_28, x_29, x_30, x_33);
x_21 = x_34;
goto block_25;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Int_toNat(x_17);
lean_dec(x_17);
x_36 = l_Lean_instToExprInt_mkNat(x_35);
x_21 = x_36;
goto block_25;
}
block_25:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = l_Lean_mkNatLit(x_18);
x_23 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_19);
x_24 = l_Lean_mkApp3(x_20, x_21, x_22, x_23);
return x_24;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_ofPoly), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__2;
x_2 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1;
x_3 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__1;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__2;
x_2 = l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_instToExprPoly() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Expr", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__3;
x_2 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0;
x_3 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1;
x_4 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("var", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__3;
x_2 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0;
x_3 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1;
x_4 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17;
x_2 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0;
x_3 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1;
x_4 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sub", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__8;
x_2 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0;
x_3 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1;
x_4 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__7;
x_2 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0;
x_3 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1;
x_4 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mulL", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__13;
x_2 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0;
x_3 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1;
x_4 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mulR", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__16;
x_2 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0;
x_3 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1;
x_4 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__2;
x_4 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1;
x_5 = lean_int_dec_le(x_4, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11;
x_7 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13;
x_8 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16;
x_9 = lean_int_neg(x_2);
lean_dec(x_2);
x_10 = l_Int_toNat(x_9);
lean_dec(x_9);
x_11 = l_Lean_instToExprInt_mkNat(x_10);
x_12 = l_Lean_mkApp3(x_6, x_7, x_8, x_11);
x_13 = l_Lean_Expr_app___override(x_3, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Int_toNat(x_2);
lean_dec(x_2);
x_15 = l_Lean_instToExprInt_mkNat(x_14);
x_16 = l_Lean_Expr_app___override(x_3, x_15);
return x_16;
}
}
case 1:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec_ref(x_1);
x_18 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__5;
x_19 = l_Lean_mkNatLit(x_17);
x_20 = l_Lean_Expr_app___override(x_18, x_19);
return x_20;
}
case 2:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_22);
lean_dec_ref(x_1);
x_23 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__7;
x_24 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_21);
x_25 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_22);
x_26 = l_Lean_mkAppB(x_23, x_24, x_25);
return x_26;
}
case 3:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_27);
x_28 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_28);
lean_dec_ref(x_1);
x_29 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__10;
x_30 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_27);
x_31 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_28);
x_32 = l_Lean_mkAppB(x_29, x_30, x_31);
return x_32;
}
case 4:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_33);
lean_dec_ref(x_1);
x_34 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__12;
x_35 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_33);
x_36 = l_Lean_Expr_app___override(x_34, x_35);
return x_36;
}
case 5:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_44; uint8_t x_45; 
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_38);
lean_dec_ref(x_1);
x_39 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__15;
x_44 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1;
x_45 = lean_int_dec_le(x_44, x_37);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_46 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11;
x_47 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13;
x_48 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16;
x_49 = lean_int_neg(x_37);
lean_dec(x_37);
x_50 = l_Int_toNat(x_49);
lean_dec(x_49);
x_51 = l_Lean_instToExprInt_mkNat(x_50);
x_52 = l_Lean_mkApp3(x_46, x_47, x_48, x_51);
x_40 = x_52;
goto block_43;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = l_Int_toNat(x_37);
lean_dec(x_37);
x_54 = l_Lean_instToExprInt_mkNat(x_53);
x_40 = x_54;
goto block_43;
}
block_43:
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_38);
x_42 = l_Lean_mkAppB(x_39, x_40, x_41);
return x_42;
}
}
default: 
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_55 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_55);
x_56 = lean_ctor_get(x_1, 1);
lean_inc(x_56);
lean_dec_ref(x_1);
x_57 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__18;
x_58 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_55);
x_59 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1;
x_60 = lean_int_dec_le(x_59, x_56);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_61 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11;
x_62 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13;
x_63 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16;
x_64 = lean_int_neg(x_56);
lean_dec(x_56);
x_65 = l_Int_toNat(x_64);
lean_dec(x_64);
x_66 = l_Lean_instToExprInt_mkNat(x_65);
x_67 = l_Lean_mkApp3(x_61, x_62, x_63, x_66);
x_68 = l_Lean_mkAppB(x_57, x_58, x_67);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = l_Int_toNat(x_56);
lean_dec(x_56);
x_70 = l_Lean_instToExprInt_mkNat(x_69);
x_71 = l_Lean_mkAppB(x_57, x_58, x_70);
return x_71;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0;
x_2 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1;
x_3 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__1;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__2;
x_2 = l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_instToExprExpr() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_denoteExpr___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_4; 
lean_dec_ref(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1;
x_7 = lean_int_dec_le(x_6, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11;
x_9 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13;
x_10 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16;
x_11 = lean_int_neg(x_5);
lean_dec(x_5);
x_12 = l_Int_toNat(x_11);
lean_dec(x_11);
x_13 = l_Lean_instToExprInt_mkNat(x_12);
x_14 = l_Lean_mkApp3(x_8, x_9, x_10, x_13);
lean_ctor_set(x_2, 0, x_14);
return x_2;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Int_toNat(x_5);
lean_dec(x_5);
x_16 = l_Lean_instToExprInt_mkNat(x_15);
lean_ctor_set(x_2, 0, x_16);
return x_2;
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec(x_2);
x_18 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1;
x_19 = lean_int_dec_le(x_18, x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11;
x_21 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13;
x_22 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16;
x_23 = lean_int_neg(x_17);
lean_dec(x_17);
x_24 = l_Int_toNat(x_23);
lean_dec(x_23);
x_25 = l_Lean_instToExprInt_mkNat(x_24);
x_26 = l_Lean_mkApp3(x_20, x_21, x_22, x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = l_Int_toNat(x_17);
lean_dec(x_17);
x_29 = l_Lean_instToExprInt_mkNat(x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
case 1:
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_2);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_2, 0);
x_33 = lean_apply_1(x_1, x_32);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_33);
return x_2;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
lean_dec(x_2);
x_35 = lean_apply_1(x_1, x_34);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
case 2:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_37 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_37);
x_38 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_38);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
x_39 = l_Int_Linear_Expr_denoteExpr___redArg(x_1, x_37);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = l_Int_Linear_Expr_denoteExpr___redArg(x_1, x_38);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = l_Lean_mkIntAdd(x_40, x_43);
lean_ctor_set(x_41, 0, x_44);
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_41, 0);
lean_inc(x_45);
lean_dec(x_41);
x_46 = l_Lean_mkIntAdd(x_40, x_45);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
case 3:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_48 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_49);
lean_dec_ref(x_2);
lean_inc_ref(x_1);
x_50 = l_Int_Linear_Expr_denoteExpr___redArg(x_1, x_48);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
x_52 = l_Int_Linear_Expr_denoteExpr___redArg(x_1, x_49);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = l_Lean_mkIntSub(x_51, x_54);
lean_ctor_set(x_52, 0, x_55);
return x_52;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_52, 0);
lean_inc(x_56);
lean_dec(x_52);
x_57 = l_Lean_mkIntSub(x_51, x_56);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
case 4:
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_59);
lean_dec_ref(x_2);
x_60 = l_Int_Linear_Expr_denoteExpr___redArg(x_1, x_59);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = l_Lean_mkIntNeg(x_62);
lean_ctor_set(x_60, 0, x_63);
return x_60;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_60, 0);
lean_inc(x_64);
lean_dec(x_60);
x_65 = l_Lean_mkIntNeg(x_64);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
case 5:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_76; uint8_t x_77; 
x_67 = lean_ctor_get(x_2, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_68);
lean_dec_ref(x_2);
x_69 = l_Int_Linear_Expr_denoteExpr___redArg(x_1, x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
x_76 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1;
x_77 = lean_int_dec_le(x_76, x_67);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_78 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11;
x_79 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13;
x_80 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16;
x_81 = lean_int_neg(x_67);
lean_dec(x_67);
x_82 = l_Int_toNat(x_81);
lean_dec(x_81);
x_83 = l_Lean_instToExprInt_mkNat(x_82);
x_84 = l_Lean_mkApp3(x_78, x_79, x_80, x_83);
x_72 = x_84;
goto block_75;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = l_Int_toNat(x_67);
lean_dec(x_67);
x_86 = l_Lean_instToExprInt_mkNat(x_85);
x_72 = x_86;
goto block_75;
}
block_75:
{
lean_object* x_73; lean_object* x_74; 
x_73 = l_Lean_mkIntMul(x_72, x_70);
if (lean_is_scalar(x_71)) {
 x_74 = lean_alloc_ctor(0, 1, 0);
} else {
 x_74 = x_71;
}
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
default: 
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_96; uint8_t x_97; 
x_87 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_87);
x_88 = lean_ctor_get(x_2, 1);
lean_inc(x_88);
lean_dec_ref(x_2);
x_89 = l_Int_Linear_Expr_denoteExpr___redArg(x_1, x_87);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 x_91 = x_89;
} else {
 lean_dec_ref(x_89);
 x_91 = lean_box(0);
}
x_96 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1;
x_97 = lean_int_dec_le(x_96, x_88);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_98 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11;
x_99 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13;
x_100 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16;
x_101 = lean_int_neg(x_88);
lean_dec(x_88);
x_102 = l_Int_toNat(x_101);
lean_dec(x_101);
x_103 = l_Lean_instToExprInt_mkNat(x_102);
x_104 = l_Lean_mkApp3(x_98, x_99, x_100, x_103);
x_92 = x_104;
goto block_95;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = l_Int_toNat(x_88);
lean_dec(x_88);
x_106 = l_Lean_instToExprInt_mkNat(x_105);
x_92 = x_106;
goto block_95;
}
block_95:
{
lean_object* x_93; lean_object* x_94; 
x_93 = l_Lean_mkIntMul(x_90, x_92);
if (lean_is_scalar(x_91)) {
 x_94 = lean_alloc_ctor(0, 1, 0);
} else {
 x_94 = x_91;
}
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_denoteExpr___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Int_Linear_Expr_denoteExpr___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_denoteExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Int_Linear_Expr_denoteExpr___redArg(x_1, x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_denoteExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Int_Linear_Expr_denoteExpr(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_denoteExpr_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_9; 
lean_dec_ref(x_1);
x_9 = !lean_is_exclusive(x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1;
x_12 = lean_int_dec_eq(x_10, x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_free_object(x_3);
x_13 = lean_int_dec_le(x_11, x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11;
x_15 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13;
x_16 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16;
x_17 = lean_int_neg(x_10);
lean_dec(x_10);
x_18 = l_Int_toNat(x_17);
lean_dec(x_17);
x_19 = l_Lean_instToExprInt_mkNat(x_18);
x_20 = l_Lean_mkApp3(x_14, x_15, x_16, x_19);
x_5 = x_20;
goto block_8;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Int_toNat(x_10);
lean_dec(x_10);
x_22 = l_Lean_instToExprInt_mkNat(x_21);
x_5 = x_22;
goto block_8;
}
}
else
{
lean_dec(x_10);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
lean_dec(x_3);
x_24 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1;
x_25 = lean_int_dec_eq(x_23, x_24);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = lean_int_dec_le(x_24, x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11;
x_28 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13;
x_29 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16;
x_30 = lean_int_neg(x_23);
lean_dec(x_23);
x_31 = l_Int_toNat(x_30);
lean_dec(x_30);
x_32 = l_Lean_instToExprInt_mkNat(x_31);
x_33 = l_Lean_mkApp3(x_27, x_28, x_29, x_32);
x_5 = x_33;
goto block_8;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = l_Int_toNat(x_23);
lean_dec(x_23);
x_35 = l_Lean_instToExprInt_mkNat(x_34);
x_5 = x_35;
goto block_8;
}
}
else
{
lean_object* x_36; 
lean_dec(x_23);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_2);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_46; uint8_t x_47; 
x_37 = lean_ctor_get(x_3, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_3, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_3, 2);
lean_inc_ref(x_39);
lean_dec_ref(x_3);
x_46 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0;
x_47 = lean_int_dec_eq(x_37, x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1;
x_49 = lean_int_dec_le(x_48, x_37);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11;
x_51 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13;
x_52 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16;
x_53 = lean_int_neg(x_37);
lean_dec(x_37);
x_54 = l_Int_toNat(x_53);
lean_dec(x_53);
x_55 = l_Lean_instToExprInt_mkNat(x_54);
x_56 = l_Lean_mkApp3(x_50, x_51, x_52, x_55);
x_40 = x_56;
goto block_45;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = l_Int_toNat(x_37);
lean_dec(x_37);
x_58 = l_Lean_instToExprInt_mkNat(x_57);
x_40 = x_58;
goto block_45;
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_37);
lean_inc_ref(x_1);
x_59 = lean_apply_1(x_1, x_38);
x_60 = l_Lean_mkIntAdd(x_2, x_59);
x_2 = x_60;
x_3 = x_39;
goto _start;
}
block_45:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_inc_ref(x_1);
x_41 = lean_apply_1(x_1, x_38);
x_42 = l_Lean_mkIntMul(x_40, x_41);
x_43 = l_Lean_mkIntAdd(x_2, x_42);
x_2 = x_43;
x_3 = x_39;
goto _start;
}
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_mkIntAdd(x_2, x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_denoteExpr_go___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_denoteExpr_go___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_denoteExpr_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_denoteExpr_go___redArg(x_1, x_2, x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_denoteExpr_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_denoteExpr_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
lean_dec_ref(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1;
x_7 = lean_int_dec_le(x_6, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11;
x_9 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13;
x_10 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16;
x_11 = lean_int_neg(x_5);
lean_dec(x_5);
x_12 = l_Int_toNat(x_11);
lean_dec(x_11);
x_13 = l_Lean_instToExprInt_mkNat(x_12);
x_14 = l_Lean_mkApp3(x_8, x_9, x_10, x_13);
lean_ctor_set(x_2, 0, x_14);
return x_2;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Int_toNat(x_5);
lean_dec(x_5);
x_16 = l_Lean_instToExprInt_mkNat(x_15);
lean_ctor_set(x_2, 0, x_16);
return x_2;
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec(x_2);
x_18 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1;
x_19 = lean_int_dec_le(x_18, x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11;
x_21 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13;
x_22 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16;
x_23 = lean_int_neg(x_17);
lean_dec(x_17);
x_24 = l_Int_toNat(x_23);
lean_dec(x_23);
x_25 = l_Lean_instToExprInt_mkNat(x_24);
x_26 = l_Lean_mkApp3(x_20, x_21, x_22, x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = l_Int_toNat(x_17);
lean_dec(x_17);
x_29 = l_Lean_instToExprInt_mkNat(x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_39; uint8_t x_40; 
x_31 = lean_ctor_get(x_2, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_2, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_33);
lean_dec_ref(x_2);
x_39 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0;
x_40 = lean_int_dec_eq(x_31, x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1;
x_42 = lean_int_dec_le(x_41, x_31);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_43 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11;
x_44 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13;
x_45 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16;
x_46 = lean_int_neg(x_31);
lean_dec(x_31);
x_47 = l_Int_toNat(x_46);
lean_dec(x_46);
x_48 = l_Lean_instToExprInt_mkNat(x_47);
x_49 = l_Lean_mkApp3(x_43, x_44, x_45, x_48);
x_34 = x_49;
goto block_38;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = l_Int_toNat(x_31);
lean_dec(x_31);
x_51 = l_Lean_instToExprInt_mkNat(x_50);
x_34 = x_51;
goto block_38;
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_31);
lean_inc_ref(x_1);
x_52 = lean_apply_1(x_1, x_32);
x_53 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_denoteExpr_go___redArg(x_1, x_52, x_33);
return x_53;
}
block_38:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_inc_ref(x_1);
x_35 = lean_apply_1(x_1, x_32);
x_36 = l_Lean_mkIntMul(x_34, x_35);
x_37 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_denoteExpr_go___redArg(x_1, x_36, x_33);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Int_Linear_Poly_denoteExpr___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Int_Linear_Poly_denoteExpr___redArg(x_1, x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Int_Linear_Poly_denoteExpr(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__7;
x_2 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mul", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__1;
x_2 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__8;
x_2 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17;
x_2 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ofNat", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("OfNat", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__6;
x_2 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__5;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Mul", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__8;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Sub", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__8;
x_2 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__10;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Add", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17;
x_2 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__12;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hMul", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HMul", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__15;
x_2 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__14;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hSub", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HSub", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__18;
x_2 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__17;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hAdd", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HAdd", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__21;
x_2 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__20;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_12 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc_ref(x_13);
x_14 = l_Lean_Expr_appFnCleanup___redArg(x_10);
x_15 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__0;
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
x_18 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_19);
x_55 = l_Lean_Expr_appFnCleanup___redArg(x_14);
x_56 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__2;
x_57 = l_Lean_Expr_isConstOf(x_55, x_56);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__3;
x_59 = l_Lean_Expr_isConstOf(x_55, x_58);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__4;
x_61 = l_Lean_Expr_isConstOf(x_55, x_60);
if (x_61 == 0)
{
uint8_t x_62; 
x_62 = l_Lean_Expr_isApp(x_55);
if (x_62 == 0)
{
lean_object* x_63; 
lean_dec_ref(x_55);
lean_dec_ref(x_19);
lean_dec_ref(x_13);
x_63 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_64 = lean_ctor_get(x_55, 1);
lean_inc_ref(x_64);
x_65 = l_Lean_Expr_appFnCleanup___redArg(x_55);
x_66 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__8;
x_67 = l_Lean_Expr_isConstOf(x_65, x_66);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__7;
x_69 = l_Lean_Expr_isConstOf(x_65, x_68);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = l_Lean_Expr_isApp(x_65);
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec_ref(x_65);
lean_dec_ref(x_64);
lean_dec_ref(x_19);
lean_dec_ref(x_13);
x_71 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = l_Lean_Expr_appFnCleanup___redArg(x_65);
x_73 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__9;
x_74 = l_Lean_Expr_isConstOf(x_72, x_73);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__11;
x_76 = l_Lean_Expr_isConstOf(x_72, x_75);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__13;
x_78 = l_Lean_Expr_isConstOf(x_72, x_77);
if (x_78 == 0)
{
uint8_t x_79; 
x_79 = l_Lean_Expr_isApp(x_72);
if (x_79 == 0)
{
lean_object* x_80; 
lean_dec_ref(x_72);
lean_dec_ref(x_64);
lean_dec_ref(x_19);
lean_dec_ref(x_13);
x_80 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6);
return x_80;
}
else
{
lean_object* x_81; uint8_t x_82; 
x_81 = l_Lean_Expr_appFnCleanup___redArg(x_72);
x_82 = l_Lean_Expr_isApp(x_81);
if (x_82 == 0)
{
lean_object* x_83; 
lean_dec_ref(x_81);
lean_dec_ref(x_64);
lean_dec_ref(x_19);
lean_dec_ref(x_13);
x_83 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = l_Lean_Expr_appFnCleanup___redArg(x_81);
x_85 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__16;
x_86 = l_Lean_Expr_isConstOf(x_84, x_85);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__19;
x_88 = l_Lean_Expr_isConstOf(x_84, x_87);
if (x_88 == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__22;
x_90 = l_Lean_Expr_isConstOf(x_84, x_89);
lean_dec_ref(x_84);
if (x_90 == 0)
{
lean_object* x_91; 
lean_dec_ref(x_64);
lean_dec_ref(x_19);
lean_dec_ref(x_13);
x_91 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6);
return x_91;
}
else
{
lean_object* x_92; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_92 = l_Lean_Meta_DefEq_isInstHAddInt(x_64, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
lean_dec_ref(x_92);
x_94 = lean_unbox(x_93);
lean_dec(x_93);
if (x_94 == 0)
{
lean_object* x_95; 
lean_dec_ref(x_19);
lean_dec_ref(x_13);
x_95 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6);
return x_95;
}
else
{
lean_object* x_96; 
lean_dec_ref(x_1);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_96 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
lean_dec_ref(x_96);
x_98 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_13, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_98) == 0)
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_98, 0);
x_101 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_101, 0, x_97);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set(x_98, 0, x_101);
return x_98;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_98, 0);
lean_inc(x_102);
lean_dec(x_98);
x_103 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_103, 0, x_97);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_104, 0, x_103);
return x_104;
}
}
else
{
lean_dec(x_97);
return x_98;
}
}
else
{
lean_dec_ref(x_13);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_96;
}
}
}
else
{
uint8_t x_105; 
lean_dec_ref(x_19);
lean_dec_ref(x_13);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_105 = !lean_is_exclusive(x_92);
if (x_105 == 0)
{
return x_92;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_92, 0);
lean_inc(x_106);
lean_dec(x_92);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
return x_107;
}
}
}
}
else
{
lean_object* x_108; 
lean_dec_ref(x_84);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_108 = l_Lean_Meta_DefEq_isInstHSubInt(x_64, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; uint8_t x_110; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
lean_dec_ref(x_108);
x_110 = lean_unbox(x_109);
lean_dec(x_109);
if (x_110 == 0)
{
lean_object* x_111; 
lean_dec_ref(x_19);
lean_dec_ref(x_13);
x_111 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6);
return x_111;
}
else
{
lean_object* x_112; 
lean_dec_ref(x_1);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_112 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
lean_dec_ref(x_112);
x_114 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_13, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_114) == 0)
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_114, 0);
x_117 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_117, 0, x_113);
lean_ctor_set(x_117, 1, x_116);
lean_ctor_set(x_114, 0, x_117);
return x_114;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_114, 0);
lean_inc(x_118);
lean_dec(x_114);
x_119 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_119, 0, x_113);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_120, 0, x_119);
return x_120;
}
}
else
{
lean_dec(x_113);
return x_114;
}
}
else
{
lean_dec_ref(x_13);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_112;
}
}
}
else
{
uint8_t x_121; 
lean_dec_ref(x_19);
lean_dec_ref(x_13);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_121 = !lean_is_exclusive(x_108);
if (x_121 == 0)
{
return x_108;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_108, 0);
lean_inc(x_122);
lean_dec(x_108);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
}
}
}
else
{
lean_object* x_124; 
lean_dec_ref(x_84);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_124 = l_Lean_Meta_DefEq_isInstHMulInt(x_64, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; uint8_t x_126; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
lean_dec_ref(x_124);
x_126 = lean_unbox(x_125);
lean_dec(x_125);
if (x_126 == 0)
{
lean_object* x_127; 
lean_dec_ref(x_19);
lean_dec_ref(x_13);
x_127 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6);
return x_127;
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
uint8_t x_128; 
lean_dec_ref(x_19);
lean_dec_ref(x_13);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_128 = !lean_is_exclusive(x_124);
if (x_128 == 0)
{
return x_124;
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_124, 0);
lean_inc(x_129);
lean_dec(x_124);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_129);
return x_130;
}
}
}
}
}
}
else
{
lean_object* x_131; 
lean_dec_ref(x_72);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_131 = l_Lean_Meta_DefEq_isInstAddInt(x_64, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; uint8_t x_133; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
lean_dec_ref(x_131);
x_133 = lean_unbox(x_132);
lean_dec(x_132);
if (x_133 == 0)
{
lean_object* x_134; 
lean_dec_ref(x_19);
lean_dec_ref(x_13);
x_134 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6);
return x_134;
}
else
{
lean_object* x_135; 
lean_dec_ref(x_1);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_135 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
lean_dec_ref(x_135);
x_137 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_13, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_137) == 0)
{
uint8_t x_138; 
x_138 = !lean_is_exclusive(x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_137, 0);
x_140 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_140, 0, x_136);
lean_ctor_set(x_140, 1, x_139);
lean_ctor_set(x_137, 0, x_140);
return x_137;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_137, 0);
lean_inc(x_141);
lean_dec(x_137);
x_142 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_142, 0, x_136);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_143, 0, x_142);
return x_143;
}
}
else
{
lean_dec(x_136);
return x_137;
}
}
else
{
lean_dec_ref(x_13);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_135;
}
}
}
else
{
uint8_t x_144; 
lean_dec_ref(x_19);
lean_dec_ref(x_13);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_144 = !lean_is_exclusive(x_131);
if (x_144 == 0)
{
return x_131;
}
else
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_ctor_get(x_131, 0);
lean_inc(x_145);
lean_dec(x_131);
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_145);
return x_146;
}
}
}
}
else
{
lean_object* x_147; 
lean_dec_ref(x_72);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_147 = l_Lean_Meta_DefEq_isInstSubInt(x_64, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; uint8_t x_149; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
lean_dec_ref(x_147);
x_149 = lean_unbox(x_148);
lean_dec(x_148);
if (x_149 == 0)
{
lean_object* x_150; 
lean_dec_ref(x_19);
lean_dec_ref(x_13);
x_150 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6);
return x_150;
}
else
{
lean_object* x_151; 
lean_dec_ref(x_1);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_151 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
lean_dec_ref(x_151);
x_153 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_13, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_153) == 0)
{
uint8_t x_154; 
x_154 = !lean_is_exclusive(x_153);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_153, 0);
x_156 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_156, 0, x_152);
lean_ctor_set(x_156, 1, x_155);
lean_ctor_set(x_153, 0, x_156);
return x_153;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_153, 0);
lean_inc(x_157);
lean_dec(x_153);
x_158 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_158, 0, x_152);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_159, 0, x_158);
return x_159;
}
}
else
{
lean_dec(x_152);
return x_153;
}
}
else
{
lean_dec_ref(x_13);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_151;
}
}
}
else
{
uint8_t x_160; 
lean_dec_ref(x_19);
lean_dec_ref(x_13);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_160 = !lean_is_exclusive(x_147);
if (x_160 == 0)
{
return x_147;
}
else
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_147, 0);
lean_inc(x_161);
lean_dec(x_147);
x_162 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_162, 0, x_161);
return x_162;
}
}
}
}
else
{
lean_object* x_163; 
lean_dec_ref(x_72);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_163 = l_Lean_Meta_DefEq_isInstMulInt(x_64, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; uint8_t x_165; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
lean_dec_ref(x_163);
x_165 = lean_unbox(x_164);
lean_dec(x_164);
if (x_165 == 0)
{
lean_object* x_166; 
lean_dec_ref(x_19);
lean_dec_ref(x_13);
x_166 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6);
return x_166;
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
uint8_t x_167; 
lean_dec_ref(x_19);
lean_dec_ref(x_13);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_167 = !lean_is_exclusive(x_163);
if (x_167 == 0)
{
return x_163;
}
else
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_163, 0);
lean_inc(x_168);
lean_dec(x_163);
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_168);
return x_169;
}
}
}
}
}
else
{
lean_object* x_170; 
lean_dec_ref(x_65);
lean_dec_ref(x_64);
lean_dec_ref(x_19);
lean_dec_ref(x_13);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_170 = l_Lean_Meta_getIntValue_x3f(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_170) == 0)
{
uint8_t x_171; 
x_171 = !lean_is_exclusive(x_170);
if (x_171 == 0)
{
lean_object* x_172; 
x_172 = lean_ctor_get(x_170, 0);
if (lean_obj_tag(x_172) == 1)
{
uint8_t x_173; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_173 = !lean_is_exclusive(x_172);
if (x_173 == 0)
{
lean_ctor_set_tag(x_172, 0);
return x_170;
}
else
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_172, 0);
lean_inc(x_174);
lean_dec(x_172);
x_175 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_170, 0, x_175);
return x_170;
}
}
else
{
lean_object* x_176; 
lean_free_object(x_170);
lean_dec(x_172);
x_176 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6);
return x_176;
}
}
else
{
lean_object* x_177; 
x_177 = lean_ctor_get(x_170, 0);
lean_inc(x_177);
lean_dec(x_170);
if (lean_obj_tag(x_177) == 1)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 x_179 = x_177;
} else {
 lean_dec_ref(x_177);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(0, 1, 0);
} else {
 x_180 = x_179;
 lean_ctor_set_tag(x_180, 0);
}
lean_ctor_set(x_180, 0, x_178);
x_181 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_181, 0, x_180);
return x_181;
}
else
{
lean_object* x_182; 
lean_dec(x_177);
x_182 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6);
return x_182;
}
}
}
else
{
uint8_t x_183; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_183 = !lean_is_exclusive(x_170);
if (x_183 == 0)
{
return x_170;
}
else
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_ctor_get(x_170, 0);
lean_inc(x_184);
lean_dec(x_170);
x_185 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_185, 0, x_184);
return x_185;
}
}
}
}
else
{
lean_object* x_186; 
lean_dec_ref(x_65);
lean_dec_ref(x_64);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_186 = l_Lean_Meta_DefEq_isInstNegInt(x_19, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; uint8_t x_188; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
lean_dec_ref(x_186);
x_188 = lean_unbox(x_187);
lean_dec(x_187);
if (x_188 == 0)
{
lean_object* x_189; 
lean_dec_ref(x_13);
x_189 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6);
return x_189;
}
else
{
lean_object* x_190; 
lean_dec_ref(x_1);
x_190 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_13, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_190) == 0)
{
uint8_t x_191; 
x_191 = !lean_is_exclusive(x_190);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_190, 0);
x_193 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_190, 0, x_193);
return x_190;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_190, 0);
lean_inc(x_194);
lean_dec(x_190);
x_195 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_195, 0, x_194);
x_196 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_196, 0, x_195);
return x_196;
}
}
else
{
return x_190;
}
}
}
else
{
uint8_t x_197; 
lean_dec_ref(x_13);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_197 = !lean_is_exclusive(x_186);
if (x_197 == 0)
{
return x_186;
}
else
{
lean_object* x_198; lean_object* x_199; 
x_198 = lean_ctor_get(x_186, 0);
lean_inc(x_198);
lean_dec(x_186);
x_199 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_199, 0, x_198);
return x_199;
}
}
}
}
}
else
{
lean_object* x_200; 
lean_dec_ref(x_55);
lean_dec_ref(x_1);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_200 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
lean_dec_ref(x_200);
x_202 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_13, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_202) == 0)
{
uint8_t x_203; 
x_203 = !lean_is_exclusive(x_202);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_ctor_get(x_202, 0);
x_205 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_205, 0, x_201);
lean_ctor_set(x_205, 1, x_204);
lean_ctor_set(x_202, 0, x_205);
return x_202;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_202, 0);
lean_inc(x_206);
lean_dec(x_202);
x_207 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_207, 0, x_201);
lean_ctor_set(x_207, 1, x_206);
x_208 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_208, 0, x_207);
return x_208;
}
}
else
{
lean_dec(x_201);
return x_202;
}
}
else
{
lean_dec_ref(x_13);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_200;
}
}
}
else
{
lean_object* x_209; 
lean_dec_ref(x_55);
lean_dec_ref(x_1);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_209 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
lean_dec_ref(x_209);
x_211 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_13, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_211) == 0)
{
uint8_t x_212; 
x_212 = !lean_is_exclusive(x_211);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_ctor_get(x_211, 0);
x_214 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_214, 0, x_210);
lean_ctor_set(x_214, 1, x_213);
lean_ctor_set(x_211, 0, x_214);
return x_211;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_211, 0);
lean_inc(x_215);
lean_dec(x_211);
x_216 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_216, 0, x_210);
lean_ctor_set(x_216, 1, x_215);
x_217 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_217, 0, x_216);
return x_217;
}
}
else
{
lean_dec(x_210);
return x_211;
}
}
else
{
lean_dec_ref(x_13);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_209;
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
lean_inc(x_25);
lean_inc_ref(x_24);
lean_inc(x_23);
lean_inc_ref(x_22);
lean_inc_ref(x_19);
x_27 = l_Lean_Meta_getIntValue_x3f(x_19, x_22, x_23, x_24, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
lean_inc(x_25);
lean_inc_ref(x_24);
lean_inc(x_23);
lean_inc_ref(x_22);
x_29 = l_Lean_Meta_getIntValue_x3f(x_20, x_22, x_23, x_24, x_25);
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
x_31 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_21, x_22, x_23, x_24, x_25);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec_ref(x_1);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_19, x_21, x_22, x_23, x_24, x_25);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_alloc_ctor(6, 2, 0);
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
x_38 = lean_alloc_ctor(6, 2, 0);
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
x_44 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_20, x_21, x_22, x_23, x_24, x_25);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_alloc_ctor(5, 2, 0);
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
x_49 = lean_alloc_ctor(5, 2, 0);
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
lean_object* x_218; 
lean_dec_ref(x_14);
lean_dec_ref(x_1);
x_218 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_13, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_218) == 0)
{
uint8_t x_219; 
x_219 = !lean_is_exclusive(x_218);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; 
x_220 = lean_ctor_get(x_218, 0);
x_221 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_218, 0, x_221);
return x_218;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_218, 0);
lean_inc(x_222);
lean_dec(x_218);
x_223 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_223, 0, x_222);
x_224 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_224, 0, x_223);
return x_224;
}
}
else
{
return x_218;
}
}
}
}
else
{
uint8_t x_225; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_225 = !lean_is_exclusive(x_8);
if (x_225 == 0)
{
return x_8;
}
else
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_ctor_get(x_8, 0);
lean_inc(x_226);
lean_dec(x_8);
x_227 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_227, 0, x_226);
return x_227;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 10:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_8);
lean_dec_ref(x_1);
x_1 = x_8;
goto _start;
}
case 5:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit(x_1, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
case 2:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit(x_1, x_2, x_3, x_4, x_5, x_6);
return x_11;
}
default: 
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_19);
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
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
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_22);
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_20);
x_24 = l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___closed__1;
x_25 = l_Lean_Expr_isConstOf(x_23, x_24);
lean_dec_ref(x_23);
if (x_25 == 0)
{
lean_dec_ref(x_22);
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
lean_object* x_26; 
lean_dec(x_10);
x_26 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_22, x_4);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = l_Lean_Expr_cleanupAnnotations(x_28);
x_30 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12;
x_31 = l_Lean_Expr_isConstOf(x_29, x_30);
lean_dec_ref(x_29);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_32 = lean_box(0);
lean_ctor_set(x_26, 0, x_32);
return x_26;
}
else
{
lean_object* x_33; 
lean_free_object(x_26);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_33 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_16, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
switch (lean_obj_tag(x_35)) {
case 1:
{
switch (lean_obj_tag(x_37)) {
case 1:
{
lean_object* x_43; 
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_35);
x_43 = lean_box(0);
lean_ctor_set(x_33, 0, x_43);
return x_33;
}
case 0:
{
lean_object* x_44; 
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_35);
x_44 = lean_box(0);
lean_ctor_set(x_33, 0, x_44);
return x_33;
}
default: 
{
lean_free_object(x_33);
goto block_42;
}
}
}
case 0:
{
if (lean_obj_tag(x_37) == 1)
{
lean_object* x_45; 
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_35);
x_45 = lean_box(0);
lean_ctor_set(x_33, 0, x_45);
return x_33;
}
else
{
lean_free_object(x_33);
goto block_42;
}
}
default: 
{
lean_free_object(x_33);
goto block_42;
}
}
block_42:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_37);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
if (lean_is_scalar(x_38)) {
 x_41 = lean_alloc_ctor(0, 1, 0);
} else {
 x_41 = x_38;
}
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
else
{
uint8_t x_46; 
lean_free_object(x_33);
lean_dec(x_35);
x_46 = !lean_is_exclusive(x_36);
if (x_46 == 0)
{
return x_36;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_36, 0);
lean_inc(x_47);
lean_dec(x_36);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_33, 0);
lean_inc(x_49);
lean_dec(x_33);
x_50 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_16, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 x_52 = x_50;
} else {
 lean_dec_ref(x_50);
 x_52 = lean_box(0);
}
switch (lean_obj_tag(x_49)) {
case 1:
{
switch (lean_obj_tag(x_51)) {
case 1:
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_49);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
case 0:
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_49);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
default: 
{
goto block_56;
}
}
}
case 0:
{
if (lean_obj_tag(x_51) == 1)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_49);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
else
{
goto block_56;
}
}
default: 
{
goto block_56;
}
}
block_56:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_49);
lean_ctor_set(x_53, 1, x_51);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
if (lean_is_scalar(x_52)) {
 x_55 = lean_alloc_ctor(0, 1, 0);
} else {
 x_55 = x_52;
}
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_49);
x_63 = lean_ctor_get(x_50, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 x_64 = x_50;
} else {
 lean_dec_ref(x_50);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 1, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_63);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_66 = !lean_is_exclusive(x_33);
if (x_66 == 0)
{
return x_33;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_33, 0);
lean_inc(x_67);
lean_dec(x_33);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_26, 0);
lean_inc(x_69);
lean_dec(x_26);
x_70 = l_Lean_Expr_cleanupAnnotations(x_69);
x_71 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12;
x_72 = l_Lean_Expr_isConstOf(x_70, x_71);
lean_dec_ref(x_70);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
else
{
lean_object* x_75; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_75 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
x_78 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_16, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 x_80 = x_78;
} else {
 lean_dec_ref(x_78);
 x_80 = lean_box(0);
}
switch (lean_obj_tag(x_76)) {
case 1:
{
switch (lean_obj_tag(x_79)) {
case 1:
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec_ref(x_76);
x_85 = lean_box(0);
if (lean_is_scalar(x_77)) {
 x_86 = lean_alloc_ctor(0, 1, 0);
} else {
 x_86 = x_77;
}
lean_ctor_set(x_86, 0, x_85);
return x_86;
}
case 0:
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec_ref(x_76);
x_87 = lean_box(0);
if (lean_is_scalar(x_77)) {
 x_88 = lean_alloc_ctor(0, 1, 0);
} else {
 x_88 = x_77;
}
lean_ctor_set(x_88, 0, x_87);
return x_88;
}
default: 
{
lean_dec(x_77);
goto block_84;
}
}
}
case 0:
{
if (lean_obj_tag(x_79) == 1)
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec_ref(x_76);
x_89 = lean_box(0);
if (lean_is_scalar(x_77)) {
 x_90 = lean_alloc_ctor(0, 1, 0);
} else {
 x_90 = x_77;
}
lean_ctor_set(x_90, 0, x_89);
return x_90;
}
else
{
lean_dec(x_77);
goto block_84;
}
}
default: 
{
lean_dec(x_77);
goto block_84;
}
}
block_84:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_76);
lean_ctor_set(x_81, 1, x_79);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
if (lean_is_scalar(x_80)) {
 x_83 = lean_alloc_ctor(0, 1, 0);
} else {
 x_83 = x_80;
}
lean_ctor_set(x_83, 0, x_82);
return x_83;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_77);
lean_dec(x_76);
x_91 = lean_ctor_get(x_78, 0);
lean_inc(x_91);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 x_92 = x_78;
} else {
 lean_dec_ref(x_78);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 1, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_91);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_94 = lean_ctor_get(x_75, 0);
lean_inc(x_94);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_95 = x_75;
} else {
 lean_dec_ref(x_75);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 1, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_94);
return x_96;
}
}
}
}
else
{
uint8_t x_97; 
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_97 = !lean_is_exclusive(x_26);
if (x_97 == 0)
{
return x_26;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_26, 0);
lean_inc(x_98);
lean_dec(x_26);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_98);
return x_99;
}
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
uint8_t x_100; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_100 = !lean_is_exclusive(x_8);
if (x_100 == 0)
{
return x_8;
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_8, 0);
lean_inc(x_101);
lean_dec(x_8);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
return x_102;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lt", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__0;
x_2 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("le", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__2;
x_2 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("GT", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("gt", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__5;
x_2 = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__4;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("GE", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ge", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__8;
x_2 = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__7;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LT", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__0;
x_2 = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__10;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LE", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__2;
x_2 = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__12;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_21 = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__1;
x_22 = l_Lean_Expr_isConstOf(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__3;
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
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_26);
x_27 = l_Lean_Expr_appFnCleanup___redArg(x_20);
x_28 = l_Lean_Expr_isApp(x_27);
if (x_28 == 0)
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
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = l_Lean_Expr_appFnCleanup___redArg(x_27);
x_30 = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__6;
x_31 = l_Lean_Expr_isConstOf(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__9;
x_33 = l_Lean_Expr_isConstOf(x_29, x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__11;
x_35 = l_Lean_Expr_isConstOf(x_29, x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__13;
x_37 = l_Lean_Expr_isConstOf(x_29, x_36);
lean_dec_ref(x_29);
if (x_37 == 0)
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
lean_object* x_38; 
lean_dec(x_10);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_38 = l_Lean_Meta_DefEq_isInstLEInt(x_26, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_42 = lean_box(0);
lean_ctor_set(x_38, 0, x_42);
return x_38;
}
else
{
lean_object* x_43; 
lean_free_object(x_38);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_43 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_16, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_45, 0, x_49);
return x_45;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_45, 0);
lean_inc(x_50);
lean_dec(x_45);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_44);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_44);
x_54 = !lean_is_exclusive(x_45);
if (x_54 == 0)
{
return x_45;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_45, 0);
lean_inc(x_55);
lean_dec(x_45);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_57 = !lean_is_exclusive(x_43);
if (x_57 == 0)
{
return x_43;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_43, 0);
lean_inc(x_58);
lean_dec(x_43);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
}
else
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_38, 0);
lean_inc(x_60);
lean_dec(x_38);
x_61 = lean_unbox(x_60);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
else
{
lean_object* x_64; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_64 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
x_66 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_16, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_68 = x_66;
} else {
 lean_dec_ref(x_66);
 x_68 = lean_box(0);
}
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_65);
lean_ctor_set(x_69, 1, x_67);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
if (lean_is_scalar(x_68)) {
 x_71 = lean_alloc_ctor(0, 1, 0);
} else {
 x_71 = x_68;
}
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_65);
x_72 = lean_ctor_get(x_66, 0);
lean_inc(x_72);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_73 = x_66;
} else {
 lean_dec_ref(x_66);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 1, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_72);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_75 = lean_ctor_get(x_64, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 x_76 = x_64;
} else {
 lean_dec_ref(x_64);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 1, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_75);
return x_77;
}
}
}
}
else
{
uint8_t x_78; 
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_78 = !lean_is_exclusive(x_38);
if (x_78 == 0)
{
return x_38;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_38, 0);
lean_inc(x_79);
lean_dec(x_38);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
}
}
else
{
lean_object* x_81; 
lean_dec_ref(x_29);
lean_dec(x_10);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_81 = l_Lean_Meta_DefEq_isInstLTInt(x_26, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_81) == 0)
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_ctor_get(x_81, 0);
x_84 = lean_unbox(x_83);
lean_dec(x_83);
if (x_84 == 0)
{
lean_object* x_85; 
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_85 = lean_box(0);
lean_ctor_set(x_81, 0, x_85);
return x_81;
}
else
{
lean_object* x_86; 
lean_free_object(x_81);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_86 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec_ref(x_86);
x_88 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_16, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_88) == 0)
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_88, 0);
x_91 = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14;
x_92 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_92, 0, x_87);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_90);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_88, 0, x_94);
return x_88;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_95 = lean_ctor_get(x_88, 0);
lean_inc(x_95);
lean_dec(x_88);
x_96 = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14;
x_97 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_97, 0, x_87);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_95);
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
lean_dec(x_87);
x_101 = !lean_is_exclusive(x_88);
if (x_101 == 0)
{
return x_88;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_88, 0);
lean_inc(x_102);
lean_dec(x_88);
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
x_104 = !lean_is_exclusive(x_86);
if (x_104 == 0)
{
return x_86;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_86, 0);
lean_inc(x_105);
lean_dec(x_86);
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
x_107 = lean_ctor_get(x_81, 0);
lean_inc(x_107);
lean_dec(x_81);
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
x_111 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_dec_ref(x_111);
x_113 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_16, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 x_115 = x_113;
} else {
 lean_dec_ref(x_113);
 x_115 = lean_box(0);
}
x_116 = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14;
x_117 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_117, 0, x_112);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_114);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_118);
if (lean_is_scalar(x_115)) {
 x_120 = lean_alloc_ctor(0, 1, 0);
} else {
 x_120 = x_115;
}
lean_ctor_set(x_120, 0, x_119);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_112);
x_121 = lean_ctor_get(x_113, 0);
lean_inc(x_121);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 x_122 = x_113;
} else {
 lean_dec_ref(x_113);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 1, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_121);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_124 = lean_ctor_get(x_111, 0);
lean_inc(x_124);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 x_125 = x_111;
} else {
 lean_dec_ref(x_111);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 1, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_124);
return x_126;
}
}
}
}
else
{
uint8_t x_127; 
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_127 = !lean_is_exclusive(x_81);
if (x_127 == 0)
{
return x_81;
}
else
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_81, 0);
lean_inc(x_128);
lean_dec(x_81);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_128);
return x_129;
}
}
}
}
else
{
lean_object* x_130; 
lean_dec_ref(x_29);
lean_dec(x_10);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_130 = l_Lean_Meta_DefEq_isInstLEInt(x_26, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_130) == 0)
{
uint8_t x_131; 
x_131 = !lean_is_exclusive(x_130);
if (x_131 == 0)
{
lean_object* x_132; uint8_t x_133; 
x_132 = lean_ctor_get(x_130, 0);
x_133 = lean_unbox(x_132);
lean_dec(x_132);
if (x_133 == 0)
{
lean_object* x_134; 
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_134 = lean_box(0);
lean_ctor_set(x_130, 0, x_134);
return x_130;
}
else
{
lean_object* x_135; 
lean_free_object(x_130);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_135 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_16, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
lean_dec_ref(x_135);
x_137 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_137) == 0)
{
uint8_t x_138; 
x_138 = !lean_is_exclusive(x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_137, 0);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_136);
lean_ctor_set(x_140, 1, x_139);
x_141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_137, 0, x_141);
return x_137;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_142 = lean_ctor_get(x_137, 0);
lean_inc(x_142);
lean_dec(x_137);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_136);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_143);
x_145 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_145, 0, x_144);
return x_145;
}
}
else
{
uint8_t x_146; 
lean_dec(x_136);
x_146 = !lean_is_exclusive(x_137);
if (x_146 == 0)
{
return x_137;
}
else
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_137, 0);
lean_inc(x_147);
lean_dec(x_137);
x_148 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_148, 0, x_147);
return x_148;
}
}
}
else
{
uint8_t x_149; 
lean_dec_ref(x_19);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_149 = !lean_is_exclusive(x_135);
if (x_149 == 0)
{
return x_135;
}
else
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_135, 0);
lean_inc(x_150);
lean_dec(x_135);
x_151 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_151, 0, x_150);
return x_151;
}
}
}
}
else
{
lean_object* x_152; uint8_t x_153; 
x_152 = lean_ctor_get(x_130, 0);
lean_inc(x_152);
lean_dec(x_130);
x_153 = lean_unbox(x_152);
lean_dec(x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; 
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_154 = lean_box(0);
x_155 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_155, 0, x_154);
return x_155;
}
else
{
lean_object* x_156; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_156 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_16, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
lean_dec_ref(x_156);
x_158 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 x_160 = x_158;
} else {
 lean_dec_ref(x_158);
 x_160 = lean_box(0);
}
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_157);
lean_ctor_set(x_161, 1, x_159);
x_162 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_162, 0, x_161);
if (lean_is_scalar(x_160)) {
 x_163 = lean_alloc_ctor(0, 1, 0);
} else {
 x_163 = x_160;
}
lean_ctor_set(x_163, 0, x_162);
return x_163;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_157);
x_164 = lean_ctor_get(x_158, 0);
lean_inc(x_164);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 x_165 = x_158;
} else {
 lean_dec_ref(x_158);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 1, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_164);
return x_166;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec_ref(x_19);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_167 = lean_ctor_get(x_156, 0);
lean_inc(x_167);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 x_168 = x_156;
} else {
 lean_dec_ref(x_156);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 1, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_167);
return x_169;
}
}
}
}
else
{
uint8_t x_170; 
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_170 = !lean_is_exclusive(x_130);
if (x_170 == 0)
{
return x_130;
}
else
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_130, 0);
lean_inc(x_171);
lean_dec(x_130);
x_172 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_172, 0, x_171);
return x_172;
}
}
}
}
else
{
lean_object* x_173; 
lean_dec_ref(x_29);
lean_dec(x_10);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_173 = l_Lean_Meta_DefEq_isInstLTInt(x_26, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_173) == 0)
{
uint8_t x_174; 
x_174 = !lean_is_exclusive(x_173);
if (x_174 == 0)
{
lean_object* x_175; uint8_t x_176; 
x_175 = lean_ctor_get(x_173, 0);
x_176 = lean_unbox(x_175);
lean_dec(x_175);
if (x_176 == 0)
{
lean_object* x_177; 
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_177 = lean_box(0);
lean_ctor_set(x_173, 0, x_177);
return x_173;
}
else
{
lean_object* x_178; 
lean_free_object(x_173);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_178 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_16, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
lean_dec_ref(x_178);
x_180 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_180) == 0)
{
uint8_t x_181; 
x_181 = !lean_is_exclusive(x_180);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_182 = lean_ctor_get(x_180, 0);
x_183 = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14;
x_184 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_184, 0, x_179);
lean_ctor_set(x_184, 1, x_183);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_182);
x_186 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_180, 0, x_186);
return x_180;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_187 = lean_ctor_get(x_180, 0);
lean_inc(x_187);
lean_dec(x_180);
x_188 = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14;
x_189 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_189, 0, x_179);
lean_ctor_set(x_189, 1, x_188);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_187);
x_191 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_191, 0, x_190);
x_192 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_192, 0, x_191);
return x_192;
}
}
else
{
uint8_t x_193; 
lean_dec(x_179);
x_193 = !lean_is_exclusive(x_180);
if (x_193 == 0)
{
return x_180;
}
else
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_ctor_get(x_180, 0);
lean_inc(x_194);
lean_dec(x_180);
x_195 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_195, 0, x_194);
return x_195;
}
}
}
else
{
uint8_t x_196; 
lean_dec_ref(x_19);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_196 = !lean_is_exclusive(x_178);
if (x_196 == 0)
{
return x_178;
}
else
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_178, 0);
lean_inc(x_197);
lean_dec(x_178);
x_198 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_198, 0, x_197);
return x_198;
}
}
}
}
else
{
lean_object* x_199; uint8_t x_200; 
x_199 = lean_ctor_get(x_173, 0);
lean_inc(x_199);
lean_dec(x_173);
x_200 = lean_unbox(x_199);
lean_dec(x_199);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; 
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_201 = lean_box(0);
x_202 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_202, 0, x_201);
return x_202;
}
else
{
lean_object* x_203; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_203 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_16, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
lean_dec_ref(x_203);
x_205 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 x_207 = x_205;
} else {
 lean_dec_ref(x_205);
 x_207 = lean_box(0);
}
x_208 = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14;
x_209 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_209, 0, x_204);
lean_ctor_set(x_209, 1, x_208);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_206);
x_211 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_211, 0, x_210);
if (lean_is_scalar(x_207)) {
 x_212 = lean_alloc_ctor(0, 1, 0);
} else {
 x_212 = x_207;
}
lean_ctor_set(x_212, 0, x_211);
return x_212;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_204);
x_213 = lean_ctor_get(x_205, 0);
lean_inc(x_213);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 x_214 = x_205;
} else {
 lean_dec_ref(x_205);
 x_214 = lean_box(0);
}
if (lean_is_scalar(x_214)) {
 x_215 = lean_alloc_ctor(1, 1, 0);
} else {
 x_215 = x_214;
}
lean_ctor_set(x_215, 0, x_213);
return x_215;
}
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec_ref(x_19);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_216 = lean_ctor_get(x_203, 0);
lean_inc(x_216);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 x_217 = x_203;
} else {
 lean_dec_ref(x_203);
 x_217 = lean_box(0);
}
if (lean_is_scalar(x_217)) {
 x_218 = lean_alloc_ctor(1, 1, 0);
} else {
 x_218 = x_217;
}
lean_ctor_set(x_218, 0, x_216);
return x_218;
}
}
}
}
else
{
uint8_t x_219; 
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_219 = !lean_is_exclusive(x_173);
if (x_219 == 0)
{
return x_173;
}
else
{
lean_object* x_220; lean_object* x_221; 
x_220 = lean_ctor_get(x_173, 0);
lean_inc(x_220);
lean_dec(x_173);
x_221 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_221, 0, x_220);
return x_221;
}
}
}
}
}
}
else
{
lean_object* x_222; 
lean_dec_ref(x_20);
lean_dec(x_10);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_222 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
lean_dec_ref(x_222);
x_224 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_16, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_224) == 0)
{
uint8_t x_225; 
x_225 = !lean_is_exclusive(x_224);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_ctor_get(x_224, 0);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_223);
lean_ctor_set(x_227, 1, x_226);
x_228 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_224, 0, x_228);
return x_224;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_229 = lean_ctor_get(x_224, 0);
lean_inc(x_229);
lean_dec(x_224);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_223);
lean_ctor_set(x_230, 1, x_229);
x_231 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_231, 0, x_230);
x_232 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_232, 0, x_231);
return x_232;
}
}
else
{
uint8_t x_233; 
lean_dec(x_223);
x_233 = !lean_is_exclusive(x_224);
if (x_233 == 0)
{
return x_224;
}
else
{
lean_object* x_234; lean_object* x_235; 
x_234 = lean_ctor_get(x_224, 0);
lean_inc(x_234);
lean_dec(x_224);
x_235 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_235, 0, x_234);
return x_235;
}
}
}
else
{
uint8_t x_236; 
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_236 = !lean_is_exclusive(x_222);
if (x_236 == 0)
{
return x_222;
}
else
{
lean_object* x_237; lean_object* x_238; 
x_237 = lean_ctor_get(x_222, 0);
lean_inc(x_237);
lean_dec(x_222);
x_238 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_238, 0, x_237);
return x_238;
}
}
}
}
else
{
lean_object* x_239; 
lean_dec_ref(x_20);
lean_dec(x_10);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_239 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
lean_dec_ref(x_239);
x_241 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_16, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_241) == 0)
{
uint8_t x_242; 
x_242 = !lean_is_exclusive(x_241);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_243 = lean_ctor_get(x_241, 0);
x_244 = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14;
x_245 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_245, 0, x_240);
lean_ctor_set(x_245, 1, x_244);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_243);
x_247 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_241, 0, x_247);
return x_241;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_248 = lean_ctor_get(x_241, 0);
lean_inc(x_248);
lean_dec(x_241);
x_249 = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14;
x_250 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_250, 0, x_240);
lean_ctor_set(x_250, 1, x_249);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_248);
x_252 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_252, 0, x_251);
x_253 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_253, 0, x_252);
return x_253;
}
}
else
{
uint8_t x_254; 
lean_dec(x_240);
x_254 = !lean_is_exclusive(x_241);
if (x_254 == 0)
{
return x_241;
}
else
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_ctor_get(x_241, 0);
lean_inc(x_255);
lean_dec(x_241);
x_256 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_256, 0, x_255);
return x_256;
}
}
}
else
{
uint8_t x_257; 
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_257 = !lean_is_exclusive(x_239);
if (x_257 == 0)
{
return x_239;
}
else
{
lean_object* x_258; lean_object* x_259; 
x_258 = lean_ctor_get(x_239, 0);
lean_inc(x_258);
lean_dec(x_239);
x_259 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_259, 0, x_258);
return x_259;
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
uint8_t x_260; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_260 = !lean_is_exclusive(x_8);
if (x_260 == 0)
{
return x_8;
}
else
{
lean_object* x_261; lean_object* x_262; 
x_261 = lean_ctor_get(x_8, 0);
lean_inc(x_261);
lean_dec(x_8);
x_262 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_262, 0, x_261);
return x_262;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Dvd", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dvd", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__1;
x_2 = l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_19);
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
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
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_22);
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_20);
x_24 = l_Lean_Expr_isApp(x_23);
if (x_24 == 0)
{
lean_dec_ref(x_23);
lean_dec_ref(x_22);
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
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_23);
x_26 = l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__2;
x_27 = l_Lean_Expr_isConstOf(x_25, x_26);
lean_dec_ref(x_25);
if (x_27 == 0)
{
lean_dec_ref(x_22);
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
lean_object* x_28; 
lean_dec(x_10);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_28 = l_Lean_Meta_DefEq_isInstDvdInt(x_22, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_32 = lean_box(0);
lean_ctor_set(x_28, 0, x_32);
return x_28;
}
else
{
lean_object* x_33; 
lean_free_object(x_28);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_33 = l_Lean_Meta_getIntValue_x3f(x_19, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
if (lean_obj_tag(x_35) == 1)
{
uint8_t x_36; 
lean_free_object(x_33);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_16, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_35, 0, x_41);
lean_ctor_set(x_38, 0, x_35);
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
lean_dec(x_38);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_35, 0, x_43);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_35);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_free_object(x_35);
lean_dec(x_37);
x_45 = !lean_is_exclusive(x_38);
if (x_45 == 0)
{
return x_38;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_38, 0);
lean_inc(x_46);
lean_dec(x_38);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_35, 0);
lean_inc(x_48);
lean_dec(x_35);
x_49 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_16, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 x_51 = x_49;
} else {
 lean_dec_ref(x_49);
 x_51 = lean_box(0);
}
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_50);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
if (lean_is_scalar(x_51)) {
 x_54 = lean_alloc_ctor(0, 1, 0);
} else {
 x_54 = x_51;
}
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_48);
x_55 = lean_ctor_get(x_49, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 x_56 = x_49;
} else {
 lean_dec_ref(x_49);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 1, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_55);
return x_57;
}
}
}
else
{
lean_object* x_58; 
lean_dec(x_35);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_58 = lean_box(0);
lean_ctor_set(x_33, 0, x_58);
return x_33;
}
}
else
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_33, 0);
lean_inc(x_59);
lean_dec(x_33);
if (lean_obj_tag(x_59) == 1)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
x_62 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_16, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_60);
lean_ctor_set(x_65, 1, x_63);
if (lean_is_scalar(x_61)) {
 x_66 = lean_alloc_ctor(1, 1, 0);
} else {
 x_66 = x_61;
}
lean_ctor_set(x_66, 0, x_65);
if (lean_is_scalar(x_64)) {
 x_67 = lean_alloc_ctor(0, 1, 0);
} else {
 x_67 = x_64;
}
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_61);
lean_dec(x_60);
x_68 = lean_ctor_get(x_62, 0);
lean_inc(x_68);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 x_69 = x_62;
} else {
 lean_dec_ref(x_62);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 1, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_68);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_59);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_73 = !lean_is_exclusive(x_33);
if (x_73 == 0)
{
return x_33;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_33, 0);
lean_inc(x_74);
lean_dec(x_33);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
}
}
else
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_28, 0);
lean_inc(x_76);
lean_dec(x_28);
x_77 = lean_unbox(x_76);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
else
{
lean_object* x_80; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_80 = l_Lean_Meta_getIntValue_x3f(x_19, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 x_82 = x_80;
} else {
 lean_dec_ref(x_80);
 x_82 = lean_box(0);
}
if (lean_obj_tag(x_81) == 1)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_82);
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 x_84 = x_81;
} else {
 lean_dec_ref(x_81);
 x_84 = lean_box(0);
}
x_85 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_16, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 x_87 = x_85;
} else {
 lean_dec_ref(x_85);
 x_87 = lean_box(0);
}
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_83);
lean_ctor_set(x_88, 1, x_86);
if (lean_is_scalar(x_84)) {
 x_89 = lean_alloc_ctor(1, 1, 0);
} else {
 x_89 = x_84;
}
lean_ctor_set(x_89, 0, x_88);
if (lean_is_scalar(x_87)) {
 x_90 = lean_alloc_ctor(0, 1, 0);
} else {
 x_90 = x_87;
}
lean_ctor_set(x_90, 0, x_89);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_84);
lean_dec(x_83);
x_91 = lean_ctor_get(x_85, 0);
lean_inc(x_91);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 x_92 = x_85;
} else {
 lean_dec_ref(x_85);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 1, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_91);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_81);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_94 = lean_box(0);
if (lean_is_scalar(x_82)) {
 x_95 = lean_alloc_ctor(0, 1, 0);
} else {
 x_95 = x_82;
}
lean_ctor_set(x_95, 0, x_94);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_96 = lean_ctor_get(x_80, 0);
lean_inc(x_96);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 x_97 = x_80;
} else {
 lean_dec_ref(x_80);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 1, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_96);
return x_98;
}
}
}
}
else
{
uint8_t x_99; 
lean_dec_ref(x_19);
lean_dec_ref(x_16);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_99 = !lean_is_exclusive(x_28);
if (x_99 == 0)
{
return x_28;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_28, 0);
lean_inc(x_100);
lean_dec(x_28);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
return x_101;
}
}
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
uint8_t x_102; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_102 = !lean_is_exclusive(x_8);
if (x_102 == 0)
{
return x_8;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_8, 0);
lean_inc(x_103);
lean_dec(x_8);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_103);
return x_104;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__2;
x_2 = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__3;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Int_ToLinear_run(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toLinearExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr___boxed), 7, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(x_7, x_2, x_3, x_4, x_5);
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
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_8, 0);
lean_dec(x_16);
x_17 = l_Lean_sortExprs(x_11, x_14);
lean_dec(x_11);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_20, x_10);
lean_dec(x_20);
lean_ctor_set(x_17, 1, x_19);
lean_ctor_set(x_17, 0, x_21);
lean_ctor_set(x_8, 0, x_17);
return x_8;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_17);
x_24 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_23, x_10);
lean_dec(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_8, 0, x_25);
return x_8;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_8);
x_26 = l_Lean_sortExprs(x_11, x_14);
lean_dec(x_11);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_29 = x_26;
} else {
 lean_dec_ref(x_26);
 x_29 = lean_box(0);
}
x_30 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_28, x_10);
lean_dec(x_28);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toLinearExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_Arith_Int_toLinearExpr(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_adapter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_apply_1(x_2, x_1);
x_9 = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(x_8, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 1)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_array_get_size(x_16);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_dec_le(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
lean_free_object(x_11);
x_24 = l_Lean_sortExprs(x_16, x_23);
lean_dec(x_16);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
x_28 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_27, x_19);
x_29 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_27, x_20);
lean_dec(x_27);
lean_ctor_set(x_24, 1, x_26);
lean_ctor_set(x_24, 0, x_29);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_28);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_24, 0);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_24);
x_32 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_31, x_19);
x_33 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_31, x_20);
lean_dec(x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
lean_ctor_set(x_15, 1, x_34);
lean_ctor_set(x_15, 0, x_32);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
}
else
{
lean_ctor_set(x_15, 1, x_16);
lean_ctor_set(x_15, 0, x_20);
lean_ctor_set(x_11, 1, x_15);
lean_ctor_set(x_11, 0, x_19);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_ctor_get(x_15, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_15);
x_37 = lean_array_get_size(x_16);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_dec_le(x_37, x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_free_object(x_11);
x_40 = l_Lean_sortExprs(x_16, x_39);
lean_dec(x_16);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
x_44 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_42, x_35);
x_45 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_42, x_36);
lean_dec(x_42);
if (lean_is_scalar(x_43)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_43;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_41);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_12, 0, x_47);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_36);
lean_ctor_set(x_48, 1, x_16);
lean_ctor_set(x_11, 1, x_48);
lean_ctor_set(x_11, 0, x_35);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_49 = lean_ctor_get(x_12, 0);
x_50 = lean_ctor_get(x_11, 1);
lean_inc(x_50);
lean_dec(x_11);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_53 = x_49;
} else {
 lean_dec_ref(x_49);
 x_53 = lean_box(0);
}
x_54 = lean_array_get_size(x_50);
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_dec_le(x_54, x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = l_Lean_sortExprs(x_50, x_56);
lean_dec(x_50);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_60 = x_57;
} else {
 lean_dec_ref(x_57);
 x_60 = lean_box(0);
}
x_61 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_59, x_51);
x_62 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_59, x_52);
lean_dec(x_59);
if (lean_is_scalar(x_60)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_60;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_58);
if (lean_is_scalar(x_53)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_53;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_12, 0, x_64);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_65; lean_object* x_66; 
if (lean_is_scalar(x_53)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_53;
}
lean_ctor_set(x_65, 0, x_52);
lean_ctor_set(x_65, 1, x_50);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_51);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_12, 0, x_66);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_67 = lean_ctor_get(x_12, 0);
lean_inc(x_67);
lean_dec(x_12);
x_68 = lean_ctor_get(x_11, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_69 = x_11;
} else {
 lean_dec_ref(x_11);
 x_69 = lean_box(0);
}
x_70 = lean_ctor_get(x_67, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_67, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_72 = x_67;
} else {
 lean_dec_ref(x_67);
 x_72 = lean_box(0);
}
x_73 = lean_array_get_size(x_68);
x_74 = lean_unsigned_to_nat(1u);
x_75 = lean_nat_dec_le(x_73, x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_69);
x_76 = l_Lean_sortExprs(x_68, x_75);
lean_dec(x_68);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_79 = x_76;
} else {
 lean_dec_ref(x_76);
 x_79 = lean_box(0);
}
x_80 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_78, x_70);
x_81 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_78, x_71);
lean_dec(x_78);
if (lean_is_scalar(x_79)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_79;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_77);
if (lean_is_scalar(x_72)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_72;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_9, 0, x_84);
return x_9;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
if (lean_is_scalar(x_72)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_72;
}
lean_ctor_set(x_85, 0, x_71);
lean_ctor_set(x_85, 1, x_68);
if (lean_is_scalar(x_69)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_69;
}
lean_ctor_set(x_86, 0, x_70);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_9, 0, x_87);
return x_9;
}
}
}
else
{
lean_object* x_88; 
lean_dec(x_12);
lean_dec(x_11);
x_88 = lean_box(0);
lean_ctor_set(x_9, 0, x_88);
return x_9;
}
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_9, 0);
lean_inc(x_89);
lean_dec(x_9);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
if (lean_obj_tag(x_90) == 1)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 x_92 = x_90;
} else {
 lean_dec_ref(x_90);
 x_92 = lean_box(0);
}
x_93 = lean_ctor_get(x_89, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_94 = x_89;
} else {
 lean_dec_ref(x_89);
 x_94 = lean_box(0);
}
x_95 = lean_ctor_get(x_91, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_91, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_97 = x_91;
} else {
 lean_dec_ref(x_91);
 x_97 = lean_box(0);
}
x_98 = lean_array_get_size(x_93);
x_99 = lean_unsigned_to_nat(1u);
x_100 = lean_nat_dec_le(x_98, x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_94);
x_101 = l_Lean_sortExprs(x_93, x_100);
lean_dec(x_93);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_104 = x_101;
} else {
 lean_dec_ref(x_101);
 x_104 = lean_box(0);
}
x_105 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_103, x_95);
x_106 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_103, x_96);
lean_dec(x_103);
if (lean_is_scalar(x_104)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_104;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_102);
if (lean_is_scalar(x_97)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_97;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_107);
if (lean_is_scalar(x_92)) {
 x_109 = lean_alloc_ctor(1, 1, 0);
} else {
 x_109 = x_92;
}
lean_ctor_set(x_109, 0, x_108);
x_110 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_110, 0, x_109);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
if (lean_is_scalar(x_97)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_97;
}
lean_ctor_set(x_111, 0, x_96);
lean_ctor_set(x_111, 1, x_93);
if (lean_is_scalar(x_94)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_94;
}
lean_ctor_set(x_112, 0, x_95);
lean_ctor_set(x_112, 1, x_111);
if (lean_is_scalar(x_92)) {
 x_113 = lean_alloc_ctor(1, 1, 0);
} else {
 x_113 = x_92;
}
lean_ctor_set(x_113, 0, x_112);
x_114 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_114, 0, x_113);
return x_114;
}
}
else
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_90);
lean_dec(x_89);
x_115 = lean_box(0);
x_116 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_116, 0, x_115);
return x_116;
}
}
}
else
{
uint8_t x_117; 
x_117 = !lean_is_exclusive(x_9);
if (x_117 == 0)
{
return x_9;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_9, 0);
lean_inc(x_118);
lean_dec(x_9);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_118);
return x_119;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_adapter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_adapter(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___boxed), 7, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(x_7, x_2, x_3, x_4, x_5);
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
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_10, 1);
x_16 = lean_ctor_get(x_10, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
x_20 = lean_array_get_size(x_15);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_dec_le(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
lean_free_object(x_10);
x_23 = l_Lean_sortExprs(x_15, x_22);
lean_dec(x_15);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_26, x_18);
x_28 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_26, x_19);
lean_dec(x_26);
lean_ctor_set(x_23, 1, x_25);
lean_ctor_set(x_23, 0, x_28);
lean_ctor_set(x_14, 1, x_23);
lean_ctor_set(x_14, 0, x_27);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_23, 0);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_23);
x_31 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_30, x_18);
x_32 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_30, x_19);
lean_dec(x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set(x_14, 1, x_33);
lean_ctor_set(x_14, 0, x_31);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
}
else
{
lean_ctor_set(x_14, 1, x_15);
lean_ctor_set(x_14, 0, x_19);
lean_ctor_set(x_10, 1, x_14);
lean_ctor_set(x_10, 0, x_18);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_14, 0);
x_35 = lean_ctor_get(x_14, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_14);
x_36 = lean_array_get_size(x_15);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_dec_le(x_36, x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_free_object(x_10);
x_39 = l_Lean_sortExprs(x_15, x_38);
lean_dec(x_15);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
x_43 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_41, x_34);
x_44 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_41, x_35);
lean_dec(x_41);
if (lean_is_scalar(x_42)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_42;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_11, 0, x_46);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_35);
lean_ctor_set(x_47, 1, x_15);
lean_ctor_set(x_10, 1, x_47);
lean_ctor_set(x_10, 0, x_34);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_11, 0);
x_49 = lean_ctor_get(x_10, 1);
lean_inc(x_49);
lean_dec(x_10);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_52 = x_48;
} else {
 lean_dec_ref(x_48);
 x_52 = lean_box(0);
}
x_53 = lean_array_get_size(x_49);
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_dec_le(x_53, x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_56 = l_Lean_sortExprs(x_49, x_55);
lean_dec(x_49);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_59 = x_56;
} else {
 lean_dec_ref(x_56);
 x_59 = lean_box(0);
}
x_60 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_58, x_50);
x_61 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_58, x_51);
lean_dec(x_58);
if (lean_is_scalar(x_59)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_59;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_57);
if (lean_is_scalar(x_52)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_52;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_11, 0, x_63);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_64; lean_object* x_65; 
if (lean_is_scalar(x_52)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_52;
}
lean_ctor_set(x_64, 0, x_51);
lean_ctor_set(x_64, 1, x_49);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_50);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_11, 0, x_65);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_66 = lean_ctor_get(x_11, 0);
lean_inc(x_66);
lean_dec(x_11);
x_67 = lean_ctor_get(x_10, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_68 = x_10;
} else {
 lean_dec_ref(x_10);
 x_68 = lean_box(0);
}
x_69 = lean_ctor_get(x_66, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_66, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_71 = x_66;
} else {
 lean_dec_ref(x_66);
 x_71 = lean_box(0);
}
x_72 = lean_array_get_size(x_67);
x_73 = lean_unsigned_to_nat(1u);
x_74 = lean_nat_dec_le(x_72, x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_68);
x_75 = l_Lean_sortExprs(x_67, x_74);
lean_dec(x_67);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_78 = x_75;
} else {
 lean_dec_ref(x_75);
 x_78 = lean_box(0);
}
x_79 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_77, x_69);
x_80 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_77, x_70);
lean_dec(x_77);
if (lean_is_scalar(x_78)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_78;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_76);
if (lean_is_scalar(x_71)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_71;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_8, 0, x_83);
return x_8;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
if (lean_is_scalar(x_71)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_71;
}
lean_ctor_set(x_84, 0, x_70);
lean_ctor_set(x_84, 1, x_67);
if (lean_is_scalar(x_68)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_68;
}
lean_ctor_set(x_85, 0, x_69);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_8, 0, x_86);
return x_8;
}
}
}
else
{
lean_object* x_87; 
lean_dec(x_11);
lean_dec(x_10);
x_87 = lean_box(0);
lean_ctor_set(x_8, 0, x_87);
return x_8;
}
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_8, 0);
lean_inc(x_88);
lean_dec(x_8);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
if (lean_obj_tag(x_89) == 1)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 x_91 = x_89;
} else {
 lean_dec_ref(x_89);
 x_91 = lean_box(0);
}
x_92 = lean_ctor_get(x_88, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_93 = x_88;
} else {
 lean_dec_ref(x_88);
 x_93 = lean_box(0);
}
x_94 = lean_ctor_get(x_90, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_90, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_96 = x_90;
} else {
 lean_dec_ref(x_90);
 x_96 = lean_box(0);
}
x_97 = lean_array_get_size(x_92);
x_98 = lean_unsigned_to_nat(1u);
x_99 = lean_nat_dec_le(x_97, x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_93);
x_100 = l_Lean_sortExprs(x_92, x_99);
lean_dec(x_92);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_103 = x_100;
} else {
 lean_dec_ref(x_100);
 x_103 = lean_box(0);
}
x_104 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_102, x_94);
x_105 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_102, x_95);
lean_dec(x_102);
if (lean_is_scalar(x_103)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_103;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_101);
if (lean_is_scalar(x_96)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_96;
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_106);
if (lean_is_scalar(x_91)) {
 x_108 = lean_alloc_ctor(1, 1, 0);
} else {
 x_108 = x_91;
}
lean_ctor_set(x_108, 0, x_107);
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_108);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
if (lean_is_scalar(x_96)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_96;
}
lean_ctor_set(x_110, 0, x_95);
lean_ctor_set(x_110, 1, x_92);
if (lean_is_scalar(x_93)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_93;
}
lean_ctor_set(x_111, 0, x_94);
lean_ctor_set(x_111, 1, x_110);
if (lean_is_scalar(x_91)) {
 x_112 = lean_alloc_ctor(1, 1, 0);
} else {
 x_112 = x_91;
}
lean_ctor_set(x_112, 0, x_111);
x_113 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_113, 0, x_112);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_89);
lean_dec(x_88);
x_114 = lean_box(0);
x_115 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_115, 0, x_114);
return x_115;
}
}
}
else
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_8);
if (x_116 == 0)
{
return x_8;
}
else
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_8, 0);
lean_inc(x_117);
lean_dec(x_8);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_117);
return x_118;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___boxed), 7, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(x_7, x_2, x_3, x_4, x_5);
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
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_10, 1);
x_16 = lean_ctor_get(x_10, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
x_20 = lean_array_get_size(x_15);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_dec_le(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
lean_free_object(x_10);
x_23 = l_Lean_sortExprs(x_15, x_22);
lean_dec(x_15);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_26, x_18);
x_28 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_26, x_19);
lean_dec(x_26);
lean_ctor_set(x_23, 1, x_25);
lean_ctor_set(x_23, 0, x_28);
lean_ctor_set(x_14, 1, x_23);
lean_ctor_set(x_14, 0, x_27);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_23, 0);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_23);
x_31 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_30, x_18);
x_32 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_30, x_19);
lean_dec(x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set(x_14, 1, x_33);
lean_ctor_set(x_14, 0, x_31);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
}
else
{
lean_ctor_set(x_14, 1, x_15);
lean_ctor_set(x_14, 0, x_19);
lean_ctor_set(x_10, 1, x_14);
lean_ctor_set(x_10, 0, x_18);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_14, 0);
x_35 = lean_ctor_get(x_14, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_14);
x_36 = lean_array_get_size(x_15);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_dec_le(x_36, x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_free_object(x_10);
x_39 = l_Lean_sortExprs(x_15, x_38);
lean_dec(x_15);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
x_43 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_41, x_34);
x_44 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_41, x_35);
lean_dec(x_41);
if (lean_is_scalar(x_42)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_42;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_11, 0, x_46);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_35);
lean_ctor_set(x_47, 1, x_15);
lean_ctor_set(x_10, 1, x_47);
lean_ctor_set(x_10, 0, x_34);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_11, 0);
x_49 = lean_ctor_get(x_10, 1);
lean_inc(x_49);
lean_dec(x_10);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_52 = x_48;
} else {
 lean_dec_ref(x_48);
 x_52 = lean_box(0);
}
x_53 = lean_array_get_size(x_49);
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_dec_le(x_53, x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_56 = l_Lean_sortExprs(x_49, x_55);
lean_dec(x_49);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_59 = x_56;
} else {
 lean_dec_ref(x_56);
 x_59 = lean_box(0);
}
x_60 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_58, x_50);
x_61 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_58, x_51);
lean_dec(x_58);
if (lean_is_scalar(x_59)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_59;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_57);
if (lean_is_scalar(x_52)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_52;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_11, 0, x_63);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_64; lean_object* x_65; 
if (lean_is_scalar(x_52)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_52;
}
lean_ctor_set(x_64, 0, x_51);
lean_ctor_set(x_64, 1, x_49);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_50);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_11, 0, x_65);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_66 = lean_ctor_get(x_11, 0);
lean_inc(x_66);
lean_dec(x_11);
x_67 = lean_ctor_get(x_10, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_68 = x_10;
} else {
 lean_dec_ref(x_10);
 x_68 = lean_box(0);
}
x_69 = lean_ctor_get(x_66, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_66, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_71 = x_66;
} else {
 lean_dec_ref(x_66);
 x_71 = lean_box(0);
}
x_72 = lean_array_get_size(x_67);
x_73 = lean_unsigned_to_nat(1u);
x_74 = lean_nat_dec_le(x_72, x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_68);
x_75 = l_Lean_sortExprs(x_67, x_74);
lean_dec(x_67);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_78 = x_75;
} else {
 lean_dec_ref(x_75);
 x_78 = lean_box(0);
}
x_79 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_77, x_69);
x_80 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_77, x_70);
lean_dec(x_77);
if (lean_is_scalar(x_78)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_78;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_76);
if (lean_is_scalar(x_71)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_71;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_8, 0, x_83);
return x_8;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
if (lean_is_scalar(x_71)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_71;
}
lean_ctor_set(x_84, 0, x_70);
lean_ctor_set(x_84, 1, x_67);
if (lean_is_scalar(x_68)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_68;
}
lean_ctor_set(x_85, 0, x_69);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_8, 0, x_86);
return x_8;
}
}
}
else
{
lean_object* x_87; 
lean_dec(x_11);
lean_dec(x_10);
x_87 = lean_box(0);
lean_ctor_set(x_8, 0, x_87);
return x_8;
}
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_8, 0);
lean_inc(x_88);
lean_dec(x_8);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
if (lean_obj_tag(x_89) == 1)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 x_91 = x_89;
} else {
 lean_dec_ref(x_89);
 x_91 = lean_box(0);
}
x_92 = lean_ctor_get(x_88, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_93 = x_88;
} else {
 lean_dec_ref(x_88);
 x_93 = lean_box(0);
}
x_94 = lean_ctor_get(x_90, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_90, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_96 = x_90;
} else {
 lean_dec_ref(x_90);
 x_96 = lean_box(0);
}
x_97 = lean_array_get_size(x_92);
x_98 = lean_unsigned_to_nat(1u);
x_99 = lean_nat_dec_le(x_97, x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_93);
x_100 = l_Lean_sortExprs(x_92, x_99);
lean_dec(x_92);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_103 = x_100;
} else {
 lean_dec_ref(x_100);
 x_103 = lean_box(0);
}
x_104 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_102, x_94);
x_105 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_102, x_95);
lean_dec(x_102);
if (lean_is_scalar(x_103)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_103;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_101);
if (lean_is_scalar(x_96)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_96;
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_106);
if (lean_is_scalar(x_91)) {
 x_108 = lean_alloc_ctor(1, 1, 0);
} else {
 x_108 = x_91;
}
lean_ctor_set(x_108, 0, x_107);
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_108);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
if (lean_is_scalar(x_96)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_96;
}
lean_ctor_set(x_110, 0, x_95);
lean_ctor_set(x_110, 1, x_92);
if (lean_is_scalar(x_93)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_93;
}
lean_ctor_set(x_111, 0, x_94);
lean_ctor_set(x_111, 1, x_110);
if (lean_is_scalar(x_91)) {
 x_112 = lean_alloc_ctor(1, 1, 0);
} else {
 x_112 = x_91;
}
lean_ctor_set(x_112, 0, x_111);
x_113 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_113, 0, x_112);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_89);
lean_dec(x_88);
x_114 = lean_box(0);
x_115 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_115, 0, x_114);
return x_115;
}
}
}
else
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_8);
if (x_116 == 0)
{
return x_8;
}
else
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_8, 0);
lean_inc(x_117);
lean_dec(x_8);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_117);
return x_118;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___boxed), 7, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(x_7, x_2, x_3, x_4, x_5);
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
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_10, 1);
x_16 = lean_ctor_get(x_10, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
x_20 = lean_array_get_size(x_15);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_dec_le(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
lean_free_object(x_10);
x_23 = l_Lean_sortExprs(x_15, x_22);
lean_dec(x_15);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_26, x_19);
lean_dec(x_26);
lean_ctor_set(x_23, 1, x_25);
lean_ctor_set(x_23, 0, x_27);
lean_ctor_set(x_14, 1, x_23);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_23, 0);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_23);
x_30 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_29, x_19);
lean_dec(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
lean_ctor_set(x_14, 1, x_31);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
}
else
{
lean_ctor_set(x_14, 1, x_15);
lean_ctor_set(x_14, 0, x_19);
lean_ctor_set(x_10, 1, x_14);
lean_ctor_set(x_10, 0, x_18);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_14, 0);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_14);
x_34 = lean_array_get_size(x_15);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_dec_le(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_free_object(x_10);
x_37 = l_Lean_sortExprs(x_15, x_36);
lean_dec(x_15);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_39, x_33);
lean_dec(x_39);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_38);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_32);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_11, 0, x_43);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_33);
lean_ctor_set(x_44, 1, x_15);
lean_ctor_set(x_10, 1, x_44);
lean_ctor_set(x_10, 0, x_32);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_45 = lean_ctor_get(x_11, 0);
x_46 = lean_ctor_get(x_10, 1);
lean_inc(x_46);
lean_dec(x_10);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_49 = x_45;
} else {
 lean_dec_ref(x_45);
 x_49 = lean_box(0);
}
x_50 = lean_array_get_size(x_46);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_dec_le(x_50, x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_53 = l_Lean_sortExprs(x_46, x_52);
lean_dec(x_46);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_56 = x_53;
} else {
 lean_dec_ref(x_53);
 x_56 = lean_box(0);
}
x_57 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_55, x_48);
lean_dec(x_55);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_54);
if (lean_is_scalar(x_49)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_49;
}
lean_ctor_set(x_59, 0, x_47);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_11, 0, x_59);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_60; lean_object* x_61; 
if (lean_is_scalar(x_49)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_49;
}
lean_ctor_set(x_60, 0, x_48);
lean_ctor_set(x_60, 1, x_46);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_47);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set(x_11, 0, x_61);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_62 = lean_ctor_get(x_11, 0);
lean_inc(x_62);
lean_dec(x_11);
x_63 = lean_ctor_get(x_10, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_64 = x_10;
} else {
 lean_dec_ref(x_10);
 x_64 = lean_box(0);
}
x_65 = lean_ctor_get(x_62, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_62, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_67 = x_62;
} else {
 lean_dec_ref(x_62);
 x_67 = lean_box(0);
}
x_68 = lean_array_get_size(x_63);
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_nat_dec_le(x_68, x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_64);
x_71 = l_Lean_sortExprs(x_63, x_70);
lean_dec(x_63);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_74 = x_71;
} else {
 lean_dec_ref(x_71);
 x_74 = lean_box(0);
}
x_75 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_73, x_66);
lean_dec(x_73);
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_72);
if (lean_is_scalar(x_67)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_67;
}
lean_ctor_set(x_77, 0, x_65);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_8, 0, x_78);
return x_8;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
if (lean_is_scalar(x_67)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_67;
}
lean_ctor_set(x_79, 0, x_66);
lean_ctor_set(x_79, 1, x_63);
if (lean_is_scalar(x_64)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_64;
}
lean_ctor_set(x_80, 0, x_65);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_8, 0, x_81);
return x_8;
}
}
}
else
{
lean_object* x_82; 
lean_dec(x_11);
lean_dec(x_10);
x_82 = lean_box(0);
lean_ctor_set(x_8, 0, x_82);
return x_8;
}
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_8, 0);
lean_inc(x_83);
lean_dec(x_8);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
if (lean_obj_tag(x_84) == 1)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 x_86 = x_84;
} else {
 lean_dec_ref(x_84);
 x_86 = lean_box(0);
}
x_87 = lean_ctor_get(x_83, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_88 = x_83;
} else {
 lean_dec_ref(x_83);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get(x_85, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_85, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_91 = x_85;
} else {
 lean_dec_ref(x_85);
 x_91 = lean_box(0);
}
x_92 = lean_array_get_size(x_87);
x_93 = lean_unsigned_to_nat(1u);
x_94 = lean_nat_dec_le(x_92, x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_88);
x_95 = l_Lean_sortExprs(x_87, x_94);
lean_dec(x_87);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_98 = x_95;
} else {
 lean_dec_ref(x_95);
 x_98 = lean_box(0);
}
x_99 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Expr_applyPerm_go(x_97, x_90);
lean_dec(x_97);
if (lean_is_scalar(x_98)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_98;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_96);
if (lean_is_scalar(x_91)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_91;
}
lean_ctor_set(x_101, 0, x_89);
lean_ctor_set(x_101, 1, x_100);
if (lean_is_scalar(x_86)) {
 x_102 = lean_alloc_ctor(1, 1, 0);
} else {
 x_102 = x_86;
}
lean_ctor_set(x_102, 0, x_101);
x_103 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_103, 0, x_102);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
if (lean_is_scalar(x_91)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_91;
}
lean_ctor_set(x_104, 0, x_90);
lean_ctor_set(x_104, 1, x_87);
if (lean_is_scalar(x_88)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_88;
}
lean_ctor_set(x_105, 0, x_89);
lean_ctor_set(x_105, 1, x_104);
if (lean_is_scalar(x_86)) {
 x_106 = lean_alloc_ctor(1, 1, 0);
} else {
 x_106 = x_86;
}
lean_ctor_set(x_106, 0, x_105);
x_107 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_107, 0, x_106);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_84);
lean_dec(x_83);
x_108 = lean_box(0);
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_108);
return x_109;
}
}
}
else
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_8);
if (x_110 == 0)
{
return x_8;
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_8, 0);
lean_inc(x_111);
lean_dec(x_8);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_111);
return x_112;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr___lam__0(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_Arith_Int_toContextExpr___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_toContextExpr___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1;
x_2 = l_Lean_mkIntLit(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__0;
x_11 = l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1;
x_12 = l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__3;
x_13 = l_Lean_RArray_toExpr___redArg(x_11, x_10, x_12, x_2, x_3, x_4, x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__0;
x_15 = l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1;
x_16 = l_Lean_RArray_ofArray___redArg(x_1);
x_17 = l_Lean_RArray_toExpr___redArg(x_15, x_14, x_16, x_2, x_3, x_4, x_5);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
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
l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__0);
l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_Poly_toExpr_go___closed__1);
l_Int_Linear_instReprPoly__lean_repr___closed__0 = _init_l_Int_Linear_instReprPoly__lean_repr___closed__0();
lean_mark_persistent(l_Int_Linear_instReprPoly__lean_repr___closed__0);
l_Int_Linear_instReprPoly__lean_repr___closed__1 = _init_l_Int_Linear_instReprPoly__lean_repr___closed__1();
lean_mark_persistent(l_Int_Linear_instReprPoly__lean_repr___closed__1);
l_Int_Linear_instReprPoly__lean_repr___closed__2 = _init_l_Int_Linear_instReprPoly__lean_repr___closed__2();
lean_mark_persistent(l_Int_Linear_instReprPoly__lean_repr___closed__2);
l_Int_Linear_instReprPoly__lean_repr___closed__3 = _init_l_Int_Linear_instReprPoly__lean_repr___closed__3();
lean_mark_persistent(l_Int_Linear_instReprPoly__lean_repr___closed__3);
l_Int_Linear_instReprPoly__lean_repr___closed__4 = _init_l_Int_Linear_instReprPoly__lean_repr___closed__4();
lean_mark_persistent(l_Int_Linear_instReprPoly__lean_repr___closed__4);
l_Int_Linear_instReprPoly__lean_repr___closed__5 = _init_l_Int_Linear_instReprPoly__lean_repr___closed__5();
lean_mark_persistent(l_Int_Linear_instReprPoly__lean_repr___closed__5);
l_Int_Linear_instReprPoly__lean_repr___closed__6 = _init_l_Int_Linear_instReprPoly__lean_repr___closed__6();
lean_mark_persistent(l_Int_Linear_instReprPoly__lean_repr___closed__6);
l_Int_Linear_instReprPoly__lean___closed__0 = _init_l_Int_Linear_instReprPoly__lean___closed__0();
lean_mark_persistent(l_Int_Linear_instReprPoly__lean___closed__0);
l_Int_Linear_instReprPoly__lean = _init_l_Int_Linear_instReprPoly__lean();
lean_mark_persistent(l_Int_Linear_instReprPoly__lean);
l_Int_Linear_instReprExpr__lean_repr___closed__0 = _init_l_Int_Linear_instReprExpr__lean_repr___closed__0();
lean_mark_persistent(l_Int_Linear_instReprExpr__lean_repr___closed__0);
l_Int_Linear_instReprExpr__lean_repr___closed__1 = _init_l_Int_Linear_instReprExpr__lean_repr___closed__1();
lean_mark_persistent(l_Int_Linear_instReprExpr__lean_repr___closed__1);
l_Int_Linear_instReprExpr__lean_repr___closed__2 = _init_l_Int_Linear_instReprExpr__lean_repr___closed__2();
lean_mark_persistent(l_Int_Linear_instReprExpr__lean_repr___closed__2);
l_Int_Linear_instReprExpr__lean_repr___closed__3 = _init_l_Int_Linear_instReprExpr__lean_repr___closed__3();
lean_mark_persistent(l_Int_Linear_instReprExpr__lean_repr___closed__3);
l_Int_Linear_instReprExpr__lean_repr___closed__4 = _init_l_Int_Linear_instReprExpr__lean_repr___closed__4();
lean_mark_persistent(l_Int_Linear_instReprExpr__lean_repr___closed__4);
l_Int_Linear_instReprExpr__lean_repr___closed__5 = _init_l_Int_Linear_instReprExpr__lean_repr___closed__5();
lean_mark_persistent(l_Int_Linear_instReprExpr__lean_repr___closed__5);
l_Int_Linear_instReprExpr__lean_repr___closed__6 = _init_l_Int_Linear_instReprExpr__lean_repr___closed__6();
lean_mark_persistent(l_Int_Linear_instReprExpr__lean_repr___closed__6);
l_Int_Linear_instReprExpr__lean_repr___closed__7 = _init_l_Int_Linear_instReprExpr__lean_repr___closed__7();
lean_mark_persistent(l_Int_Linear_instReprExpr__lean_repr___closed__7);
l_Int_Linear_instReprExpr__lean_repr___closed__8 = _init_l_Int_Linear_instReprExpr__lean_repr___closed__8();
lean_mark_persistent(l_Int_Linear_instReprExpr__lean_repr___closed__8);
l_Int_Linear_instReprExpr__lean_repr___closed__9 = _init_l_Int_Linear_instReprExpr__lean_repr___closed__9();
lean_mark_persistent(l_Int_Linear_instReprExpr__lean_repr___closed__9);
l_Int_Linear_instReprExpr__lean_repr___closed__10 = _init_l_Int_Linear_instReprExpr__lean_repr___closed__10();
lean_mark_persistent(l_Int_Linear_instReprExpr__lean_repr___closed__10);
l_Int_Linear_instReprExpr__lean_repr___closed__11 = _init_l_Int_Linear_instReprExpr__lean_repr___closed__11();
lean_mark_persistent(l_Int_Linear_instReprExpr__lean_repr___closed__11);
l_Int_Linear_instReprExpr__lean_repr___closed__12 = _init_l_Int_Linear_instReprExpr__lean_repr___closed__12();
lean_mark_persistent(l_Int_Linear_instReprExpr__lean_repr___closed__12);
l_Int_Linear_instReprExpr__lean_repr___closed__13 = _init_l_Int_Linear_instReprExpr__lean_repr___closed__13();
lean_mark_persistent(l_Int_Linear_instReprExpr__lean_repr___closed__13);
l_Int_Linear_instReprExpr__lean_repr___closed__14 = _init_l_Int_Linear_instReprExpr__lean_repr___closed__14();
lean_mark_persistent(l_Int_Linear_instReprExpr__lean_repr___closed__14);
l_Int_Linear_instReprExpr__lean_repr___closed__15 = _init_l_Int_Linear_instReprExpr__lean_repr___closed__15();
lean_mark_persistent(l_Int_Linear_instReprExpr__lean_repr___closed__15);
l_Int_Linear_instReprExpr__lean_repr___closed__16 = _init_l_Int_Linear_instReprExpr__lean_repr___closed__16();
lean_mark_persistent(l_Int_Linear_instReprExpr__lean_repr___closed__16);
l_Int_Linear_instReprExpr__lean_repr___closed__17 = _init_l_Int_Linear_instReprExpr__lean_repr___closed__17();
lean_mark_persistent(l_Int_Linear_instReprExpr__lean_repr___closed__17);
l_Int_Linear_instReprExpr__lean_repr___closed__18 = _init_l_Int_Linear_instReprExpr__lean_repr___closed__18();
lean_mark_persistent(l_Int_Linear_instReprExpr__lean_repr___closed__18);
l_Int_Linear_instReprExpr__lean_repr___closed__19 = _init_l_Int_Linear_instReprExpr__lean_repr___closed__19();
lean_mark_persistent(l_Int_Linear_instReprExpr__lean_repr___closed__19);
l_Int_Linear_instReprExpr__lean_repr___closed__20 = _init_l_Int_Linear_instReprExpr__lean_repr___closed__20();
lean_mark_persistent(l_Int_Linear_instReprExpr__lean_repr___closed__20);
l_Int_Linear_instReprExpr__lean___closed__0 = _init_l_Int_Linear_instReprExpr__lean___closed__0();
lean_mark_persistent(l_Int_Linear_instReprExpr__lean___closed__0);
l_Int_Linear_instReprExpr__lean = _init_l_Int_Linear_instReprExpr__lean();
lean_mark_persistent(l_Int_Linear_instReprExpr__lean);
l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0 = _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0);
l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1 = _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1);
l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__2 = _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__2);
l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__3 = _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__3);
l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__4 = _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__4);
l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__5 = _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__5);
l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__6 = _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__6);
l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__7 = _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__7();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__7);
l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__8 = _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__8();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__8);
l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__9 = _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__9();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__9);
l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__10 = _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__10();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__10);
l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11 = _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11);
l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12 = _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12);
l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13 = _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13);
l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14 = _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14);
l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__15 = _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__15();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__15);
l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16 = _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16);
l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17 = _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17);
l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__18 = _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__18();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__18);
l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__19 = _init_l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__19();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__19);
l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__0 = _init_l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__0);
l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__1 = _init_l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__1);
l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__2 = _init_l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__2);
l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__3 = _init_l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__3);
l_Lean_Meta_Simp_Arith_Int_instToExprPoly = _init_l_Lean_Meta_Simp_Arith_Int_instToExprPoly();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_instToExprPoly);
l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0 = _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0);
l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1 = _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1);
l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__2 = _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__2);
l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__3 = _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__3);
l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4 = _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4);
l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__5 = _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__5);
l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6 = _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6);
l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__7 = _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__7();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__7);
l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__8 = _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__8();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__8);
l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9 = _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9);
l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__10 = _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__10();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__10);
l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11 = _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11);
l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__12 = _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__12();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__12);
l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__13 = _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__13();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__13);
l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14 = _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14);
l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__15 = _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__15();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__15);
l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__16 = _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__16();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__16);
l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17 = _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17);
l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__18 = _init_l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__18();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__18);
l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__0 = _init_l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__0);
l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__1 = _init_l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__1);
l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__2 = _init_l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__2);
l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__3 = _init_l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__3);
l_Lean_Meta_Simp_Arith_Int_instToExprExpr = _init_l_Lean_Meta_Simp_Arith_Int_instToExprExpr();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_instToExprExpr);
l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__0 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__0);
l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__1);
l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__2);
l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__3 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__3);
l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__4 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__4);
l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__6 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__6);
l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__5 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__5);
l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__7 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__7);
l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__8 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__8);
l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__9 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__9);
l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__10 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__10);
l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__11 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__11();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__11);
l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__12 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__12();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__12);
l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__13 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__13();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__13);
l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__15 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__15();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__15);
l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__14 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__14();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__14);
l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__16 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__16();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__16);
l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__18 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__18();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__18);
l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__17 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__17();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__17);
l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__19 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__19();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__19);
l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__21 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__21();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__21);
l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__20 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__20();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__20);
l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__22 = _init_l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__22();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__22);
l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___closed__0 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___closed__0);
l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___closed__1 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___closed__1);
l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__0 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__0);
l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__1 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__1);
l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__2 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__2);
l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__3 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__3);
l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__4 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__4);
l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__5 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__5);
l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__6 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__6);
l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__7 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__7();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__7);
l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__8 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__8();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__8);
l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__9 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__9();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__9);
l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__10 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__10();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__10);
l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__11 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__11();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__11);
l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__12 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__12();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__12);
l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__13 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__13();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__13);
l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14);
l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__0 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__0);
l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__1 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__1);
l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__2 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__2);
l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__0 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__0);
l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__1 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__1);
l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__2 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__2);
l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__3 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__3);
l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__0 = _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__0);
l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1 = _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1);
l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__2 = _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__2);
l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__3 = _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
