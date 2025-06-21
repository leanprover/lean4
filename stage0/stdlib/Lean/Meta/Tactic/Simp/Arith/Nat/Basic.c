// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Arith.Nat.Basic
// Imports: Lean.Util.SortExprs Lean.Meta.Check Lean.Meta.Offset Lean.Meta.AppBuilder Lean.Meta.KExprMap Lean.Data.RArray
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
static lean_object* l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg___closed__2;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__14;
lean_object* l_Lean_Meta_isInstHMulNat___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstAddNat___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__2;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__11;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__0;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__17____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
lean_object* l_Lean_mkNatLit(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__1;
static lean_object* l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___closed__4;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__13;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__15;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(lean_object*);
static lean_object* l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___closed__5;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__2;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__6;
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__16____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__4;
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_applyPerm(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__4;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__5;
uint8_t l_Lean_Expr_isApp(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__14____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__15;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523____boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__16;
lean_object* l_Lean_Meta_isInstMulNat___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__5____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__3;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__12;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___lam__0(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_Meta_evalNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__1____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__9;
lean_object* l_Lean_RArray_toExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__10;
LEAN_EXPORT lean_object* l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__7____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_applyPerm___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__2;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__15____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__9____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatAdd(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__9;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__14;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__6____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr;
lean_object* l_Lean_sortExprs(lean_object*, uint8_t);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_ExprCnstr_applyPerm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___lam__0(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__6;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Nat_Linear_Expr_applyPerm_go_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__0____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
lean_object* l_Lean_Meta_KExprMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__16;
lean_object* l_Lean_Meta_KExprMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__15____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__0;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__1;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__8____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444____boxed(lean_object*, lean_object*);
static lean_object* l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__8;
LEAN_EXPORT lean_object* l_List_foldl___at___Std_Format_joinSep___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__0____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__2;
lean_object* l_Lean_RArray_ofArray___redArg(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__5;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__0;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean___closed__0;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_reprPolyCnstr___redArg____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0___boxed(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__13____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__3____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_applyPerm_go(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLE(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__2____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
extern lean_object* l_Lean_instInhabitedExpr;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__9;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__9;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__15;
lean_object* l_Lean_Meta_isInstLENat___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__6____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
static lean_object* l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Nat_Linear_ExprCnstr_applyPerm___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__2;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Nat_Linear_Expr_applyPerm_go_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstLTNat___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Nat_Linear_Expr_applyPerm_go_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__3;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__13;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__1;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__12____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__11;
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstOfNatNat___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__0;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__5;
static lean_object* l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_applyPerm_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Nat_Linear_Expr_applyPerm_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523_(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__9____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__0;
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__3;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__6;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__12;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__17;
static lean_object* l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg___closed__1;
lean_object* l_Lean_Meta_isInstHAddNat___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__10;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__8____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__12;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__4;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__13____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__5;
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__11____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__10;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__1___lam__0(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__4;
LEAN_EXPORT lean_object* l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__1____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
lean_object* l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__11;
lean_object* l_Lean_mkNatMul(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__5____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__16;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__16____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__8;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__7;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__10____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__7____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__14____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__0;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__3____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__3;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__0;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___closed__0;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__14;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__2____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__17;
static lean_object* l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg___closed__3;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__11____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__10;
lean_object* l_Nat_Linear_Expr_inc(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr___closed__7;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__8;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__4____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
lean_object* l_Lean_mkNatEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___closed__2;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__10____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__4____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg(lean_object*);
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg___closed__4;
static lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__12____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Nat_Linear_Expr_applyPerm_go_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Nat_Linear_Expr_applyPerm_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Nat_Linear_Expr_applyPerm_go_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_applyPerm_go(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_array_get_size(x_4);
x_6 = lean_uint64_of_nat(x_3);
x_7 = 32;
x_8 = lean_uint64_shift_right(x_6, x_7);
x_9 = lean_uint64_xor(x_6, x_8);
x_10 = 16;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = lean_uint64_to_usize(x_12);
x_14 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_15 = 1;
x_16 = lean_usize_sub(x_14, x_15);
x_17 = lean_usize_land(x_13, x_16);
x_18 = lean_array_uget(x_4, x_17);
x_19 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Nat_Linear_Expr_applyPerm_go_spec__0___redArg(x_3, x_18);
lean_dec(x_18);
lean_dec(x_3);
if (lean_obj_tag(x_19) == 0)
{
return x_2;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_2);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_2, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
lean_ctor_set(x_2, 0, x_22);
return x_2;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
case 2:
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_2);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 1);
x_28 = l_Nat_Linear_Expr_applyPerm_go(x_1, x_26);
x_29 = l_Nat_Linear_Expr_applyPerm_go(x_1, x_27);
lean_ctor_set(x_2, 1, x_29);
lean_ctor_set(x_2, 0, x_28);
return x_2;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_2, 0);
x_31 = lean_ctor_get(x_2, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_2);
x_32 = l_Nat_Linear_Expr_applyPerm_go(x_1, x_30);
x_33 = l_Nat_Linear_Expr_applyPerm_go(x_1, x_31);
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
case 3:
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_2);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_2, 1);
x_37 = l_Nat_Linear_Expr_applyPerm_go(x_1, x_36);
lean_ctor_set(x_2, 1, x_37);
return x_2;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_2, 0);
x_39 = lean_ctor_get(x_2, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_2);
x_40 = l_Nat_Linear_Expr_applyPerm_go(x_1, x_39);
x_41 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
default: 
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_2);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_2, 0);
x_44 = l_Nat_Linear_Expr_applyPerm_go(x_1, x_43);
lean_ctor_set(x_2, 0, x_44);
return x_2;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_2, 0);
x_46 = lean_ctor_get(x_2, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_2);
x_47 = l_Nat_Linear_Expr_applyPerm_go(x_1, x_45);
x_48 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Nat_Linear_Expr_applyPerm_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Nat_Linear_Expr_applyPerm_go_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Nat_Linear_Expr_applyPerm_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Nat_Linear_Expr_applyPerm_go_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_applyPerm_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_Linear_Expr_applyPerm_go(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_applyPerm(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_Linear_Expr_applyPerm_go(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_applyPerm___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_Linear_Expr_applyPerm(x_1, x_2);
lean_dec(x_1);
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
x_6 = l_Nat_Linear_Expr_applyPerm_go(x_1, x_4);
x_7 = l_Nat_Linear_Expr_applyPerm_go(x_1, x_5);
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
x_11 = l_Nat_Linear_Expr_applyPerm_go(x_1, x_9);
x_12 = l_Nat_Linear_Expr_applyPerm_go(x_1, x_10);
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
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__0____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat.Linear.Expr.num", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__1____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__0____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__2____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__1____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__3____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__4____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__5____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat.Linear.Expr.var", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__6____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__5____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__7____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__6____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__8____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat.Linear.Expr.add", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__9____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__8____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__10____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__9____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__11____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat.Linear.Expr.mulL", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__12____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__11____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__13____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__12____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__14____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat.Linear.Expr.mulR", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__15____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__14____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__16____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__15____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_16; uint8_t x_17; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_4 = x_1;
} else {
 lean_dec_ref(x_1);
 x_4 = lean_box(0);
}
x_16 = lean_unsigned_to_nat(1024u);
x_17 = lean_nat_dec_le(x_16, x_2);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__3____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
x_5 = x_18;
goto block_15;
}
else
{
lean_object* x_19; 
x_19 = l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__4____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
x_5 = x_19;
goto block_15;
}
block_15:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_6 = l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__2____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
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
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_12, 0, x_10);
x_13 = lean_unbox(x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_13);
x_14 = l_Repr_addAppParen(x_12, x_2);
return x_14;
}
}
case 1:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_33; uint8_t x_34; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_21 = x_1;
} else {
 lean_dec_ref(x_1);
 x_21 = lean_box(0);
}
x_33 = lean_unsigned_to_nat(1024u);
x_34 = lean_nat_dec_le(x_33, x_2);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__3____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
x_22 = x_35;
goto block_32;
}
else
{
lean_object* x_36; 
x_36 = l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__4____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
x_22 = x_36;
goto block_32;
}
block_32:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_23 = l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__7____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
x_24 = l_Nat_reprFast(x_20);
if (lean_is_scalar(x_21)) {
 x_25 = lean_alloc_ctor(3, 1, 0);
} else {
 x_25 = x_21;
 lean_ctor_set_tag(x_25, 3);
}
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_29, 0, x_27);
x_30 = lean_unbox(x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_30);
x_31 = l_Repr_addAppParen(x_29, x_2);
return x_31;
}
}
case 2:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_55; 
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_39 = x_1;
} else {
 lean_dec_ref(x_1);
 x_39 = lean_box(0);
}
x_40 = lean_unsigned_to_nat(1024u);
x_55 = lean_nat_dec_le(x_40, x_2);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__3____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
x_41 = x_56;
goto block_54;
}
else
{
lean_object* x_57; 
x_57 = l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__4____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
x_41 = x_57;
goto block_54;
}
block_54:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_42 = lean_box(1);
x_43 = l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__10____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
x_44 = l_Lean_Meta_Simp_Arith_Nat_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_(x_37, x_40);
if (lean_is_scalar(x_39)) {
 x_45 = lean_alloc_ctor(5, 2, 0);
} else {
 x_45 = x_39;
 lean_ctor_set_tag(x_45, 5);
}
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
x_47 = l_Lean_Meta_Simp_Arith_Nat_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_(x_38, x_40);
x_48 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_49, 0, x_41);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_51, 0, x_49);
x_52 = lean_unbox(x_50);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_52);
x_53 = l_Repr_addAppParen(x_51, x_2);
return x_53;
}
}
case 3:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_77; 
x_58 = lean_ctor_get(x_1, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_1, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_60 = x_1;
} else {
 lean_dec_ref(x_1);
 x_60 = lean_box(0);
}
x_61 = lean_unsigned_to_nat(1024u);
x_77 = lean_nat_dec_le(x_61, x_2);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__3____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
x_62 = x_78;
goto block_76;
}
else
{
lean_object* x_79; 
x_79 = l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__4____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
x_62 = x_79;
goto block_76;
}
block_76:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; 
x_63 = lean_box(1);
x_64 = l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__13____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
x_65 = l_Nat_reprFast(x_58);
x_66 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_66, 0, x_65);
if (lean_is_scalar(x_60)) {
 x_67 = lean_alloc_ctor(5, 2, 0);
} else {
 x_67 = x_60;
 lean_ctor_set_tag(x_67, 5);
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_63);
x_69 = l_Lean_Meta_Simp_Arith_Nat_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_(x_59, x_61);
x_70 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_71, 0, x_62);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_73, 0, x_71);
x_74 = lean_unbox(x_72);
lean_ctor_set_uint8(x_73, sizeof(void*)*1, x_74);
x_75 = l_Repr_addAppParen(x_73, x_2);
return x_75;
}
}
default: 
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_99; 
x_80 = lean_ctor_get(x_1, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_1, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_82 = x_1;
} else {
 lean_dec_ref(x_1);
 x_82 = lean_box(0);
}
x_83 = lean_unsigned_to_nat(1024u);
x_99 = lean_nat_dec_le(x_83, x_2);
if (x_99 == 0)
{
lean_object* x_100; 
x_100 = l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__3____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
x_84 = x_100;
goto block_98;
}
else
{
lean_object* x_101; 
x_101 = l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__4____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
x_84 = x_101;
goto block_98;
}
block_98:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; 
x_85 = lean_box(1);
x_86 = l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__16____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
x_87 = l_Lean_Meta_Simp_Arith_Nat_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_(x_80, x_83);
if (lean_is_scalar(x_82)) {
 x_88 = lean_alloc_ctor(5, 2, 0);
} else {
 x_88 = x_82;
 lean_ctor_set_tag(x_88, 5);
}
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_85);
x_90 = l_Nat_reprFast(x_81);
x_91 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_92 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_93, 0, x_84);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_95, 0, x_93);
x_96 = lean_unbox(x_94);
lean_ctor_set_uint8(x_95, sizeof(void*)*1, x_96);
x_97 = l_Repr_addAppParen(x_95, x_2);
return x_97;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_Arith_Nat_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Nat_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169____boxed), 2, 0);
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
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__0____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("{ ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__1____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__2____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__1____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__3____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__2____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__4____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" := ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__5____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__4____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__6____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__5____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
x_2 = l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__3____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__7____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(6u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__8____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__9____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__8____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__10____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lhs", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__11____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__10____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__12____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__13____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rhs", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__14____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__13____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__15____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" }", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__16____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__0____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__17____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__15____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__5____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
x_6 = l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__6____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
x_7 = l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__7____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Bool_repr___redArg(x_2);
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_12, 0, x_10);
x_13 = lean_unbox(x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_13);
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__9____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_box(1);
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__11____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_5);
x_22 = l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__12____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
x_23 = l_Lean_Meta_Simp_Arith_Nat_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_(x_3, x_8);
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_unbox(x_11);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_26);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_15);
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_17);
x_30 = l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__14____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_5);
x_33 = l_Lean_Meta_Simp_Arith_Nat_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_(x_4, x_8);
x_34 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_34, 0, x_22);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_unbox(x_11);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_36);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__3____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
x_39 = l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__16____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
x_41 = l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__17____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_unbox(x_11);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_45);
return x_44;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444____boxed), 2, 0);
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
static lean_object* _init_l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__9____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
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
x_12 = l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg___closed__1;
x_13 = l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(x_11, x_12);
x_14 = l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__4____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
x_15 = l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg___closed__3;
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
x_17 = l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg___closed__4;
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_21, 0, x_19);
x_22 = lean_unbox(x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_22);
return x_21;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_1);
x_25 = l_Nat_reprFast(x_23);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Nat_reprFast(x_24);
x_30 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
x_32 = l_List_reverse___redArg(x_31);
x_33 = l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg___closed__1;
x_34 = l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(x_32, x_33);
x_35 = l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__4____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
x_36 = l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg___closed__3;
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
x_38 = l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg___closed__4;
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_42, 0, x_40);
x_43 = lean_unbox(x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_43);
return x_42;
}
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Std_Format_joinSep___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_1);
lean_ctor_set_tag(x_4, 5);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 0, x_3);
lean_inc(x_2);
x_8 = lean_apply_1(x_2, x_6);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_8);
x_3 = x_9;
x_4 = x_7;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
lean_inc(x_1);
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_1);
lean_inc(x_2);
x_14 = lean_apply_1(x_2, x_11);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_3 = x_15;
x_4 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__1___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_alloc_closure((void*)(l_Std_Format_joinSep___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__1___lam__0), 1, 0);
x_9 = l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg(x_7);
x_10 = l_List_foldl___at___Std_Format_joinSep___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__1_spec__1(x_2, x_8, x_9, x_4);
return x_10;
}
}
}
}
static lean_object* _init_l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[]", 2, 2);
return x_1;
}
}
static lean_object* _init_l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___closed__1;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg___closed__1;
lean_inc(x_1);
x_4 = l_Std_Format_joinSep___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__1(x_1, x_3);
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_6 = lean_ctor_get(x_1, 1);
lean_dec(x_6);
x_7 = lean_ctor_get(x_1, 0);
lean_dec(x_7);
x_8 = l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__4____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
x_9 = l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___closed__4;
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_4);
lean_ctor_set(x_1, 0, x_9);
x_10 = l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___closed__5;
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_14, 0, x_12);
x_15 = lean_unbox(x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_15);
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_1);
x_16 = l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__4____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
x_17 = l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___closed__4;
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
x_19 = l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___closed__5;
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_unbox(x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_24);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_reprPolyCnstr___redArg____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523_(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__5____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
x_6 = l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__6____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
x_7 = l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__7____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
x_8 = l_Bool_repr___redArg(x_2);
x_9 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__9____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_box(1);
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__11____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_5);
x_21 = l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__12____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
x_22 = l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg(x_3);
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_unbox(x_10);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_25);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_14);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_16);
x_29 = l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__14____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_5);
x_32 = l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg(x_4);
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_unbox(x_10);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_35);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__3____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_;
x_38 = l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__16____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
x_40 = l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__17____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_;
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_unbox(x_10);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_44);
return x_43;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_Arith_Nat_reprPolyCnstr___redArg____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523____boxed), 2, 0);
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
x_3 = l_Lean_Expr_const___override(x_2, x_1);
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
x_3 = l_Lean_Expr_const___override(x_2, x_1);
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
x_3 = l_Lean_Expr_const___override(x_2, x_1);
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
x_3 = l_Lean_Expr_const___override(x_2, x_1);
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
x_3 = l_Lean_Expr_const___override(x_2, x_1);
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
lean_dec(x_1);
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
lean_dec(x_1);
x_7 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__8;
x_8 = l_Lean_mkNatLit(x_6);
x_9 = l_Lean_Expr_app___override(x_7, x_8);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
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
lean_inc(x_17);
lean_dec(x_1);
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
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_dec(x_1);
x_24 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__17;
x_25 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(x_22);
x_26 = l_Lean_mkNatLit(x_23);
x_27 = l_Lean_mkAppB(x_24, x_25, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__0() {
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
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__0;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___lam__0), 1, 0);
x_2 = l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
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
x_3 = l_Lean_Expr_const___override(x_2, x_1);
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
x_3 = l_Lean_Expr_const___override(x_2, x_1);
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
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__0() {
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
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__0;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___lam__0), 1, 0);
x_2 = l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_mkNatLit(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_Lean_instInhabitedExpr;
x_9 = lean_array_get(x_8, x_1, x_7);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_1, x_11, x_3);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_1, x_12, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = l_Lean_mkNatAdd(x_14, x_18);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = l_Lean_mkNatAdd(x_14, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
case 3:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_2, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
lean_dec(x_2);
x_26 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_1, x_25, x_3);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = l_Lean_mkNatLit(x_24);
x_30 = l_Lean_mkNatMul(x_29, x_28);
lean_ctor_set(x_26, 0, x_30);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_26, 0);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_26);
x_33 = l_Lean_mkNatLit(x_24);
x_34 = l_Lean_mkNatMul(x_33, x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
default: 
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_2, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_2, 1);
lean_inc(x_37);
lean_dec(x_2);
x_38 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_1, x_36, x_3);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = l_Lean_mkNatLit(x_37);
x_42 = l_Lean_mkNatMul(x_40, x_41);
lean_ctor_set(x_38, 0, x_42);
return x_38;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_38, 0);
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_38);
x_45 = l_Lean_mkNatLit(x_37);
x_46 = l_Lean_mkNatMul(x_43, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_1, x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_1, x_5, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_1, x_6, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Lean_mkNatLE(x_8, x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = l_Lean_mkNatLE(x_8, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_dec(x_2);
x_20 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_1, x_18, x_3);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_1, x_19, x_22);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = l_Lean_mkNatEq(x_21, x_25);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = l_Lean_mkNatEq(x_21, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(x_1, x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_st_ref_get(x_2, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_12 = l_Lean_Meta_KExprMap_find_x3f___redArg(x_11, x_1, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_2, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_get(x_2, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
x_25 = lean_array_get_size(x_21);
lean_dec(x_21);
lean_inc(x_25);
lean_inc(x_1);
x_26 = l_Lean_Meta_KExprMap_insert___redArg(x_23, x_1, x_25, x_3, x_4, x_5, x_6, x_20);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_array_push(x_24, x_1);
lean_ctor_set(x_19, 1, x_29);
lean_ctor_set(x_19, 0, x_27);
x_30 = lean_st_ref_set(x_2, x_19, x_28);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_25);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_25);
lean_free_object(x_19);
lean_dec(x_24);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_26);
if (x_37 == 0)
{
return x_26;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_26, 0);
x_39 = lean_ctor_get(x_26, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_26);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_19, 0);
x_42 = lean_ctor_get(x_19, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_19);
x_43 = lean_array_get_size(x_21);
lean_dec(x_21);
lean_inc(x_43);
lean_inc(x_1);
x_44 = l_Lean_Meta_KExprMap_insert___redArg(x_41, x_1, x_43, x_3, x_4, x_5, x_6, x_20);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_array_push(x_42, x_1);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_st_ref_set(x_2, x_48, x_46);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_51 = x_49;
} else {
 lean_dec_ref(x_49);
 x_51 = lean_box(0);
}
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_43);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_1);
x_54 = lean_ctor_get(x_44, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_44, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_56 = x_44;
} else {
 lean_dec_ref(x_44);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_12);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_12, 0);
lean_dec(x_59);
x_60 = !lean_is_exclusive(x_13);
if (x_60 == 0)
{
return x_12;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_13, 0);
lean_inc(x_61);
lean_dec(x_13);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_12, 0, x_62);
return x_12;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_12, 1);
lean_inc(x_63);
lean_dec(x_12);
x_64 = lean_ctor_get(x_13, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_65 = x_13;
} else {
 lean_dec_ref(x_13);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 1, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_64);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_63);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_12);
if (x_68 == 0)
{
return x_12;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_12, 0);
x_70 = lean_ctor_get(x_12, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_12);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("succ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__0;
x_2 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mul", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__2;
x_2 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__9;
x_2 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("OfNat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ofNat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__6;
x_2 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__5;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Mul", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__2;
x_2 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__8;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Add", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__9;
x_2 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__10;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HMul", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hMul", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__13;
x_2 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__12;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HAdd", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hAdd", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__16;
x_2 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__15;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_inc(x_1);
x_8 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Expr_cleanupAnnotations(x_9);
x_12 = l_Lean_Expr_isApp(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_11);
x_13 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
x_15 = l_Lean_Expr_appFnCleanup___redArg(x_11);
x_16 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__1;
x_17 = l_Lean_Expr_isConstOf(x_15, x_16);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = l_Lean_Expr_isApp(x_15);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_14);
x_19 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
x_72 = l_Lean_Expr_appFnCleanup___redArg(x_15);
x_73 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__3;
x_74 = l_Lean_Expr_isConstOf(x_72, x_73);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__4;
x_76 = l_Lean_Expr_isConstOf(x_72, x_75);
if (x_76 == 0)
{
uint8_t x_77; 
x_77 = l_Lean_Expr_isApp(x_72);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_72);
lean_dec(x_20);
lean_dec(x_14);
x_78 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
x_80 = l_Lean_Expr_appFnCleanup___redArg(x_72);
x_81 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__7;
x_82 = l_Lean_Expr_isConstOf(x_80, x_81);
if (x_82 == 0)
{
uint8_t x_83; 
x_83 = l_Lean_Expr_isApp(x_80);
if (x_83 == 0)
{
lean_object* x_84; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_20);
lean_dec(x_14);
x_84 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = l_Lean_Expr_appFnCleanup___redArg(x_80);
x_86 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__9;
x_87 = l_Lean_Expr_isConstOf(x_85, x_86);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__11;
x_89 = l_Lean_Expr_isConstOf(x_85, x_88);
if (x_89 == 0)
{
uint8_t x_90; 
x_90 = l_Lean_Expr_isApp(x_85);
if (x_90 == 0)
{
lean_object* x_91; 
lean_dec(x_85);
lean_dec(x_79);
lean_dec(x_20);
lean_dec(x_14);
x_91 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_91;
}
else
{
lean_object* x_92; uint8_t x_93; 
x_92 = l_Lean_Expr_appFnCleanup___redArg(x_85);
x_93 = l_Lean_Expr_isApp(x_92);
if (x_93 == 0)
{
lean_object* x_94; 
lean_dec(x_92);
lean_dec(x_79);
lean_dec(x_20);
lean_dec(x_14);
x_94 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = l_Lean_Expr_appFnCleanup___redArg(x_92);
x_96 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__14;
x_97 = l_Lean_Expr_isConstOf(x_95, x_96);
if (x_97 == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__17;
x_99 = l_Lean_Expr_isConstOf(x_95, x_98);
lean_dec(x_95);
if (x_99 == 0)
{
lean_object* x_100; 
lean_dec(x_79);
lean_dec(x_20);
lean_dec(x_14);
x_100 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Lean_Meta_isInstHAddNat___redArg(x_79, x_4, x_10);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_unbox(x_102);
lean_dec(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_20);
lean_dec(x_14);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
lean_dec(x_101);
x_105 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_104);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_1);
x_106 = lean_ctor_get(x_101, 1);
lean_inc(x_106);
lean_dec(x_101);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_107 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_20, x_2, x_3, x_4, x_5, x_6, x_106);
if (lean_obj_tag(x_107) == 0)
{
uint8_t x_108; 
x_108 = !lean_is_exclusive(x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_107, 0);
x_110 = lean_ctor_get(x_107, 1);
x_111 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_14, x_2, x_3, x_4, x_5, x_6, x_110);
if (lean_obj_tag(x_111) == 0)
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_111);
if (x_112 == 0)
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_111, 0);
lean_ctor_set_tag(x_107, 2);
lean_ctor_set(x_107, 1, x_113);
lean_ctor_set(x_111, 0, x_107);
return x_111;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_111, 0);
x_115 = lean_ctor_get(x_111, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_111);
lean_ctor_set_tag(x_107, 2);
lean_ctor_set(x_107, 1, x_114);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_107);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
else
{
lean_free_object(x_107);
lean_dec(x_109);
return x_111;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_107, 0);
x_118 = lean_ctor_get(x_107, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_107);
x_119 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_14, x_2, x_3, x_4, x_5, x_6, x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_122 = x_119;
} else {
 lean_dec_ref(x_119);
 x_122 = lean_box(0);
}
x_123 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_123, 0, x_117);
lean_ctor_set(x_123, 1, x_120);
if (lean_is_scalar(x_122)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_122;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_121);
return x_124;
}
else
{
lean_dec(x_117);
return x_119;
}
}
}
else
{
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_107;
}
}
}
}
else
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; 
lean_dec(x_95);
x_125 = l_Lean_Meta_isInstHMulNat___redArg(x_79, x_4, x_10);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_unbox(x_126);
lean_dec(x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
lean_dec(x_20);
lean_dec(x_14);
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
lean_dec(x_125);
x_129 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_128);
return x_129;
}
else
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_125, 1);
lean_inc(x_130);
lean_dec(x_125);
x_21 = x_14;
x_22 = x_2;
x_23 = x_3;
x_24 = x_4;
x_25 = x_5;
x_26 = x_6;
x_27 = x_130;
goto block_71;
}
}
}
}
}
else
{
lean_object* x_131; lean_object* x_132; uint8_t x_133; 
lean_dec(x_85);
x_131 = l_Lean_Meta_isInstAddNat___redArg(x_79, x_4, x_10);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_unbox(x_132);
lean_dec(x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_20);
lean_dec(x_14);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
lean_dec(x_131);
x_135 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_134);
return x_135;
}
else
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_1);
x_136 = lean_ctor_get(x_131, 1);
lean_inc(x_136);
lean_dec(x_131);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_137 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_20, x_2, x_3, x_4, x_5, x_6, x_136);
if (lean_obj_tag(x_137) == 0)
{
uint8_t x_138; 
x_138 = !lean_is_exclusive(x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_137, 0);
x_140 = lean_ctor_get(x_137, 1);
x_141 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_14, x_2, x_3, x_4, x_5, x_6, x_140);
if (lean_obj_tag(x_141) == 0)
{
uint8_t x_142; 
x_142 = !lean_is_exclusive(x_141);
if (x_142 == 0)
{
lean_object* x_143; 
x_143 = lean_ctor_get(x_141, 0);
lean_ctor_set_tag(x_137, 2);
lean_ctor_set(x_137, 1, x_143);
lean_ctor_set(x_141, 0, x_137);
return x_141;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_141, 0);
x_145 = lean_ctor_get(x_141, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_141);
lean_ctor_set_tag(x_137, 2);
lean_ctor_set(x_137, 1, x_144);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_137);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
else
{
lean_free_object(x_137);
lean_dec(x_139);
return x_141;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_137, 0);
x_148 = lean_ctor_get(x_137, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_137);
x_149 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_14, x_2, x_3, x_4, x_5, x_6, x_148);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_152 = x_149;
} else {
 lean_dec_ref(x_149);
 x_152 = lean_box(0);
}
x_153 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_153, 0, x_147);
lean_ctor_set(x_153, 1, x_150);
if (lean_is_scalar(x_152)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_152;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_151);
return x_154;
}
else
{
lean_dec(x_147);
return x_149;
}
}
}
else
{
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_137;
}
}
}
}
else
{
lean_object* x_155; lean_object* x_156; uint8_t x_157; 
lean_dec(x_85);
x_155 = l_Lean_Meta_isInstMulNat___redArg(x_79, x_4, x_10);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_unbox(x_156);
lean_dec(x_156);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; 
lean_dec(x_20);
lean_dec(x_14);
x_158 = lean_ctor_get(x_155, 1);
lean_inc(x_158);
lean_dec(x_155);
x_159 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_158);
return x_159;
}
else
{
lean_object* x_160; 
x_160 = lean_ctor_get(x_155, 1);
lean_inc(x_160);
lean_dec(x_155);
x_21 = x_14;
x_22 = x_2;
x_23 = x_3;
x_24 = x_4;
x_25 = x_5;
x_26 = x_6;
x_27 = x_160;
goto block_71;
}
}
}
}
else
{
lean_object* x_161; lean_object* x_162; uint8_t x_163; 
lean_dec(x_80);
lean_dec(x_79);
x_161 = l_Lean_Meta_isInstOfNatNat___redArg(x_14, x_4, x_10);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_unbox(x_162);
lean_dec(x_162);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; 
lean_dec(x_20);
x_164 = lean_ctor_get(x_161, 1);
lean_inc(x_164);
lean_dec(x_161);
x_165 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_164);
return x_165;
}
else
{
lean_object* x_166; lean_object* x_167; 
lean_dec(x_1);
x_166 = lean_ctor_get(x_161, 1);
lean_inc(x_166);
lean_dec(x_161);
x_167 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_20, x_2, x_3, x_4, x_5, x_6, x_166);
return x_167;
}
}
}
}
else
{
lean_object* x_168; 
lean_dec(x_72);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_168 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_20, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_168) == 0)
{
uint8_t x_169; 
x_169 = !lean_is_exclusive(x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_168, 0);
x_171 = lean_ctor_get(x_168, 1);
x_172 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_14, x_2, x_3, x_4, x_5, x_6, x_171);
if (lean_obj_tag(x_172) == 0)
{
uint8_t x_173; 
x_173 = !lean_is_exclusive(x_172);
if (x_173 == 0)
{
lean_object* x_174; 
x_174 = lean_ctor_get(x_172, 0);
lean_ctor_set_tag(x_168, 2);
lean_ctor_set(x_168, 1, x_174);
lean_ctor_set(x_172, 0, x_168);
return x_172;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_172, 0);
x_176 = lean_ctor_get(x_172, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_172);
lean_ctor_set_tag(x_168, 2);
lean_ctor_set(x_168, 1, x_175);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_168);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
else
{
lean_free_object(x_168);
lean_dec(x_170);
return x_172;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_168, 0);
x_179 = lean_ctor_get(x_168, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_168);
x_180 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_14, x_2, x_3, x_4, x_5, x_6, x_179);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_183 = x_180;
} else {
 lean_dec_ref(x_180);
 x_183 = lean_box(0);
}
x_184 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_184, 0, x_178);
lean_ctor_set(x_184, 1, x_181);
if (lean_is_scalar(x_183)) {
 x_185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_185 = x_183;
}
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_182);
return x_185;
}
else
{
lean_dec(x_178);
return x_180;
}
}
}
else
{
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_168;
}
}
}
else
{
lean_dec(x_72);
x_21 = x_14;
x_22 = x_2;
x_23 = x_3;
x_24 = x_4;
x_25 = x_5;
x_26 = x_6;
x_27 = x_10;
goto block_71;
}
block_71:
{
lean_object* x_28; lean_object* x_29; 
lean_inc(x_25);
lean_inc(x_20);
x_28 = l_Lean_Meta_evalNat(x_20, x_23, x_24, x_25, x_26, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_25);
x_31 = l_Lean_Meta_evalNat(x_21, x_23, x_24, x_25, x_26, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_20);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_22, x_23, x_24, x_25, x_26, x_33);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_31);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_31, 1);
x_37 = lean_ctor_get(x_31, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_32, 0);
lean_inc(x_38);
lean_dec(x_32);
x_39 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_20, x_22, x_23, x_24, x_25, x_26, x_36);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_ctor_set_tag(x_31, 4);
lean_ctor_set(x_31, 1, x_38);
lean_ctor_set(x_31, 0, x_41);
lean_ctor_set(x_39, 0, x_31);
return x_39;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_39, 0);
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_39);
lean_ctor_set_tag(x_31, 4);
lean_ctor_set(x_31, 1, x_38);
lean_ctor_set(x_31, 0, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_31);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
lean_dec(x_38);
lean_free_object(x_31);
return x_39;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_31, 1);
lean_inc(x_45);
lean_dec(x_31);
x_46 = lean_ctor_get(x_32, 0);
lean_inc(x_46);
lean_dec(x_32);
x_47 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_20, x_22, x_23, x_24, x_25, x_26, x_45);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
x_51 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_46);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
else
{
lean_dec(x_46);
return x_47;
}
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_20);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_28);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_28, 1);
x_55 = lean_ctor_get(x_28, 0);
lean_dec(x_55);
x_56 = lean_ctor_get(x_29, 0);
lean_inc(x_56);
lean_dec(x_29);
x_57 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_21, x_22, x_23, x_24, x_25, x_26, x_54);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_57, 0);
lean_ctor_set_tag(x_28, 3);
lean_ctor_set(x_28, 1, x_59);
lean_ctor_set(x_28, 0, x_56);
lean_ctor_set(x_57, 0, x_28);
return x_57;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_57, 0);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_57);
lean_ctor_set_tag(x_28, 3);
lean_ctor_set(x_28, 1, x_60);
lean_ctor_set(x_28, 0, x_56);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_28);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
else
{
lean_dec(x_56);
lean_free_object(x_28);
return x_57;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_28, 1);
lean_inc(x_63);
lean_dec(x_28);
x_64 = lean_ctor_get(x_29, 0);
lean_inc(x_64);
lean_dec(x_29);
x_65 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_21, x_22, x_23, x_24, x_25, x_26, x_63);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_68 = x_65;
} else {
 lean_dec_ref(x_65);
 x_68 = lean_box(0);
}
x_69 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_69, 0, x_64);
lean_ctor_set(x_69, 1, x_66);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
return x_70;
}
else
{
lean_dec(x_64);
return x_65;
}
}
}
}
}
}
else
{
lean_object* x_186; 
lean_dec(x_15);
lean_dec(x_1);
x_186 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_14, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_186) == 0)
{
uint8_t x_187; 
x_187 = !lean_is_exclusive(x_186);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; 
x_188 = lean_ctor_get(x_186, 0);
x_189 = l_Nat_Linear_Expr_inc(x_188);
lean_ctor_set(x_186, 0, x_189);
return x_186;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_190 = lean_ctor_get(x_186, 0);
x_191 = lean_ctor_get(x_186, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_186);
x_192 = l_Nat_Linear_Expr_inc(x_190);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_191);
return x_193;
}
}
else
{
return x_186;
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
case 4:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr___closed__0;
x_15 = lean_string_dec_eq(x_13, x_14);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
x_16 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__0;
x_18 = lean_string_dec_eq(x_12, x_17);
lean_dec(x_12);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_20 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__1;
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_7);
return x_21;
}
}
}
else
{
lean_object* x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_22 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_22;
}
}
else
{
lean_object* x_23; 
lean_dec(x_10);
lean_dec(x_9);
x_23 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_23;
}
}
else
{
lean_object* x_24; 
lean_dec(x_9);
x_24 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_24;
}
}
case 5:
{
lean_object* x_25; 
x_25 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_25;
}
case 9:
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_7);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_7);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_26);
x_32 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_32;
}
}
case 10:
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
lean_dec(x_1);
x_1 = x_33;
goto _start;
}
default: 
{
lean_object* x_35; 
x_35 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_15; uint8_t x_16; 
x_8 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_11 = x_8;
} else {
 lean_dec_ref(x_8);
 x_11 = lean_box(0);
}
x_15 = l_Lean_Expr_cleanupAnnotations(x_9);
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_14;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_18 = l_Lean_Expr_appFnCleanup___redArg(x_15);
x_19 = l_Lean_Expr_isApp(x_18);
if (x_19 == 0)
{
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_18);
x_22 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__1;
x_23 = l_Lean_Expr_isConstOf(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__3;
x_25 = l_Lean_Expr_isConstOf(x_21, x_24);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = l_Lean_Expr_isApp(x_21);
if (x_26 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_14;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
x_28 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_29 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__5;
x_30 = l_Lean_Expr_isConstOf(x_28, x_29);
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = l_Lean_Expr_isApp(x_28);
if (x_31 == 0)
{
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_14;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = l_Lean_Expr_appFnCleanup___redArg(x_28);
x_33 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__8;
x_34 = l_Lean_Expr_isConstOf(x_32, x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__11;
x_36 = l_Lean_Expr_isConstOf(x_32, x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__13;
x_38 = l_Lean_Expr_isConstOf(x_32, x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__15;
x_40 = l_Lean_Expr_isConstOf(x_32, x_39);
lean_dec(x_32);
if (x_40 == 0)
{
lean_dec(x_27);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
goto block_14;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_11);
x_41 = l_Lean_Meta_isInstLENat___redArg(x_27, x_4, x_10);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
uint8_t x_44; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_41, 0);
lean_dec(x_45);
x_46 = lean_box(0);
lean_ctor_set(x_41, 0, x_46);
return x_41;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_41, 1);
lean_inc(x_47);
lean_dec(x_41);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_41, 1);
lean_inc(x_50);
lean_dec(x_41);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_51 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_20, x_2, x_3, x_4, x_5, x_6, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_17, x_2, x_3, x_4, x_5, x_6, x_53);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set_uint8(x_57, sizeof(void*)*2, x_38);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_54, 0, x_58);
return x_54;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_54, 0);
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_54);
x_61 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_61, 0, x_52);
lean_ctor_set(x_61, 1, x_59);
lean_ctor_set_uint8(x_61, sizeof(void*)*2, x_38);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec(x_52);
x_64 = !lean_is_exclusive(x_54);
if (x_64 == 0)
{
return x_54;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_54, 0);
x_66 = lean_ctor_get(x_54, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_54);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_68 = !lean_is_exclusive(x_51);
if (x_68 == 0)
{
return x_51;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_51, 0);
x_70 = lean_ctor_get(x_51, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_51);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_dec(x_32);
lean_dec(x_11);
x_72 = l_Lean_Meta_isInstLTNat___redArg(x_27, x_4, x_10);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
lean_dec(x_73);
if (x_74 == 0)
{
uint8_t x_75; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_75 = !lean_is_exclusive(x_72);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_72, 0);
lean_dec(x_76);
x_77 = lean_box(0);
lean_ctor_set(x_72, 0, x_77);
return x_72;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_72, 1);
lean_inc(x_78);
lean_dec(x_72);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_72, 1);
lean_inc(x_81);
lean_dec(x_72);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_82 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_20, x_2, x_3, x_4, x_5, x_6, x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_17, x_2, x_3, x_4, x_5, x_6, x_84);
if (lean_obj_tag(x_85) == 0)
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_85, 0);
x_88 = l_Nat_Linear_Expr_inc(x_83);
x_89 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
lean_ctor_set_uint8(x_89, sizeof(void*)*2, x_36);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_85, 0, x_90);
return x_85;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_91 = lean_ctor_get(x_85, 0);
x_92 = lean_ctor_get(x_85, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_85);
x_93 = l_Nat_Linear_Expr_inc(x_83);
x_94 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_91);
lean_ctor_set_uint8(x_94, sizeof(void*)*2, x_36);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_92);
return x_96;
}
}
else
{
uint8_t x_97; 
lean_dec(x_83);
x_97 = !lean_is_exclusive(x_85);
if (x_97 == 0)
{
return x_85;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_85, 0);
x_99 = lean_ctor_get(x_85, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_85);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_101 = !lean_is_exclusive(x_82);
if (x_101 == 0)
{
return x_82;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_82, 0);
x_103 = lean_ctor_get(x_82, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_82);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
}
}
else
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; 
lean_dec(x_32);
lean_dec(x_11);
x_105 = l_Lean_Meta_isInstLENat___redArg(x_27, x_4, x_10);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_unbox(x_106);
lean_dec(x_106);
if (x_107 == 0)
{
uint8_t x_108; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_108 = !lean_is_exclusive(x_105);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_105, 0);
lean_dec(x_109);
x_110 = lean_box(0);
lean_ctor_set(x_105, 0, x_110);
return x_105;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_105, 1);
lean_inc(x_111);
lean_dec(x_105);
x_112 = lean_box(0);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_105, 1);
lean_inc(x_114);
lean_dec(x_105);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_115 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_17, x_2, x_3, x_4, x_5, x_6, x_114);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_20, x_2, x_3, x_4, x_5, x_6, x_117);
if (lean_obj_tag(x_118) == 0)
{
uint8_t x_119; 
x_119 = !lean_is_exclusive(x_118);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_118, 0);
x_121 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_121, 0, x_116);
lean_ctor_set(x_121, 1, x_120);
lean_ctor_set_uint8(x_121, sizeof(void*)*2, x_34);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_118, 0, x_122);
return x_118;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_123 = lean_ctor_get(x_118, 0);
x_124 = lean_ctor_get(x_118, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_118);
x_125 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_125, 0, x_116);
lean_ctor_set(x_125, 1, x_123);
lean_ctor_set_uint8(x_125, sizeof(void*)*2, x_34);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_124);
return x_127;
}
}
else
{
uint8_t x_128; 
lean_dec(x_116);
x_128 = !lean_is_exclusive(x_118);
if (x_128 == 0)
{
return x_118;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_118, 0);
x_130 = lean_ctor_get(x_118, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_118);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
else
{
uint8_t x_132; 
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_132 = !lean_is_exclusive(x_115);
if (x_132 == 0)
{
return x_115;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_115, 0);
x_134 = lean_ctor_get(x_115, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_115);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
}
}
else
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; 
lean_dec(x_32);
lean_dec(x_11);
x_136 = l_Lean_Meta_isInstLTNat___redArg(x_27, x_4, x_10);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_unbox(x_137);
lean_dec(x_137);
if (x_138 == 0)
{
uint8_t x_139; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_139 = !lean_is_exclusive(x_136);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_136, 0);
lean_dec(x_140);
x_141 = lean_box(0);
lean_ctor_set(x_136, 0, x_141);
return x_136;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_136, 1);
lean_inc(x_142);
lean_dec(x_136);
x_143 = lean_box(0);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_142);
return x_144;
}
}
else
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_ctor_get(x_136, 1);
lean_inc(x_145);
lean_dec(x_136);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_146 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_17, x_2, x_3, x_4, x_5, x_6, x_145);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_20, x_2, x_3, x_4, x_5, x_6, x_148);
if (lean_obj_tag(x_149) == 0)
{
uint8_t x_150; 
x_150 = !lean_is_exclusive(x_149);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_151 = lean_ctor_get(x_149, 0);
x_152 = l_Nat_Linear_Expr_inc(x_147);
x_153 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_151);
lean_ctor_set_uint8(x_153, sizeof(void*)*2, x_30);
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_149, 0, x_154);
return x_149;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_155 = lean_ctor_get(x_149, 0);
x_156 = lean_ctor_get(x_149, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_149);
x_157 = l_Nat_Linear_Expr_inc(x_147);
x_158 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_155);
lean_ctor_set_uint8(x_158, sizeof(void*)*2, x_30);
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_158);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_156);
return x_160;
}
}
else
{
uint8_t x_161; 
lean_dec(x_147);
x_161 = !lean_is_exclusive(x_149);
if (x_161 == 0)
{
return x_149;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_149, 0);
x_163 = lean_ctor_get(x_149, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_149);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
}
else
{
uint8_t x_165; 
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_165 = !lean_is_exclusive(x_146);
if (x_165 == 0)
{
return x_146;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_146, 0);
x_167 = lean_ctor_get(x_146, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_146);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
}
}
}
else
{
lean_object* x_169; uint8_t x_170; 
lean_dec(x_28);
lean_dec(x_11);
x_169 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_27, x_4, x_10);
x_170 = !lean_is_exclusive(x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_171 = lean_ctor_get(x_169, 0);
x_172 = lean_ctor_get(x_169, 1);
x_173 = l_Lean_Expr_cleanupAnnotations(x_171);
x_174 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__16;
x_175 = l_Lean_Expr_isConstOf(x_173, x_174);
lean_dec(x_173);
if (x_175 == 0)
{
lean_object* x_176; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_176 = lean_box(0);
lean_ctor_set(x_169, 0, x_176);
return x_169;
}
else
{
lean_object* x_177; 
lean_free_object(x_169);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_177 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_20, x_2, x_3, x_4, x_5, x_6, x_172);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_17, x_2, x_3, x_4, x_5, x_6, x_179);
if (lean_obj_tag(x_180) == 0)
{
uint8_t x_181; 
x_181 = !lean_is_exclusive(x_180);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_180, 0);
x_183 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_183, 0, x_178);
lean_ctor_set(x_183, 1, x_182);
lean_ctor_set_uint8(x_183, sizeof(void*)*2, x_175);
x_184 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_180, 0, x_184);
return x_180;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_185 = lean_ctor_get(x_180, 0);
x_186 = lean_ctor_get(x_180, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_180);
x_187 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_187, 0, x_178);
lean_ctor_set(x_187, 1, x_185);
lean_ctor_set_uint8(x_187, sizeof(void*)*2, x_175);
x_188 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_188, 0, x_187);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_186);
return x_189;
}
}
else
{
uint8_t x_190; 
lean_dec(x_178);
x_190 = !lean_is_exclusive(x_180);
if (x_190 == 0)
{
return x_180;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_180, 0);
x_192 = lean_ctor_get(x_180, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_180);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
}
else
{
uint8_t x_194; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_194 = !lean_is_exclusive(x_177);
if (x_194 == 0)
{
return x_177;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_177, 0);
x_196 = lean_ctor_get(x_177, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_177);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_198 = lean_ctor_get(x_169, 0);
x_199 = lean_ctor_get(x_169, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_169);
x_200 = l_Lean_Expr_cleanupAnnotations(x_198);
x_201 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__16;
x_202 = l_Lean_Expr_isConstOf(x_200, x_201);
lean_dec(x_200);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_203 = lean_box(0);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_199);
return x_204;
}
else
{
lean_object* x_205; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_205 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_20, x_2, x_3, x_4, x_5, x_6, x_199);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_dec(x_205);
x_208 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_17, x_2, x_3, x_4, x_5, x_6, x_207);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_211 = x_208;
} else {
 lean_dec_ref(x_208);
 x_211 = lean_box(0);
}
x_212 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_212, 0, x_206);
lean_ctor_set(x_212, 1, x_209);
lean_ctor_set_uint8(x_212, sizeof(void*)*2, x_202);
x_213 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_213, 0, x_212);
if (lean_is_scalar(x_211)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_211;
}
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_210);
return x_214;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_206);
x_215 = lean_ctor_get(x_208, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_208, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_217 = x_208;
} else {
 lean_dec_ref(x_208);
 x_217 = lean_box(0);
}
if (lean_is_scalar(x_217)) {
 x_218 = lean_alloc_ctor(1, 2, 0);
} else {
 x_218 = x_217;
}
lean_ctor_set(x_218, 0, x_215);
lean_ctor_set(x_218, 1, x_216);
return x_218;
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_219 = lean_ctor_get(x_205, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_205, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_221 = x_205;
} else {
 lean_dec_ref(x_205);
 x_221 = lean_box(0);
}
if (lean_is_scalar(x_221)) {
 x_222 = lean_alloc_ctor(1, 2, 0);
} else {
 x_222 = x_221;
}
lean_ctor_set(x_222, 0, x_219);
lean_ctor_set(x_222, 1, x_220);
return x_222;
}
}
}
}
}
}
else
{
lean_object* x_223; 
lean_dec(x_21);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_223 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_20, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec(x_223);
x_226 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_17, x_2, x_3, x_4, x_5, x_6, x_225);
if (lean_obj_tag(x_226) == 0)
{
uint8_t x_227; 
x_227 = !lean_is_exclusive(x_226);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_226, 0);
x_229 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_229, 0, x_224);
lean_ctor_set(x_229, 1, x_228);
lean_ctor_set_uint8(x_229, sizeof(void*)*2, x_23);
x_230 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_226, 0, x_230);
return x_226;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_231 = lean_ctor_get(x_226, 0);
x_232 = lean_ctor_get(x_226, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_226);
x_233 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_233, 0, x_224);
lean_ctor_set(x_233, 1, x_231);
lean_ctor_set_uint8(x_233, sizeof(void*)*2, x_23);
x_234 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_234, 0, x_233);
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_232);
return x_235;
}
}
else
{
uint8_t x_236; 
lean_dec(x_224);
x_236 = !lean_is_exclusive(x_226);
if (x_236 == 0)
{
return x_226;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_226, 0);
x_238 = lean_ctor_get(x_226, 1);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_226);
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
return x_239;
}
}
}
else
{
uint8_t x_240; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_240 = !lean_is_exclusive(x_223);
if (x_240 == 0)
{
return x_223;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_241 = lean_ctor_get(x_223, 0);
x_242 = lean_ctor_get(x_223, 1);
lean_inc(x_242);
lean_inc(x_241);
lean_dec(x_223);
x_243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_243, 0, x_241);
lean_ctor_set(x_243, 1, x_242);
return x_243;
}
}
}
}
else
{
lean_object* x_244; 
lean_dec(x_21);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_244 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_20, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_247 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_17, x_2, x_3, x_4, x_5, x_6, x_246);
if (lean_obj_tag(x_247) == 0)
{
uint8_t x_248; 
x_248 = !lean_is_exclusive(x_247);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; lean_object* x_254; 
x_249 = lean_ctor_get(x_247, 0);
x_250 = lean_box(0);
x_251 = l_Nat_Linear_Expr_inc(x_245);
x_252 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_249);
x_253 = lean_unbox(x_250);
lean_ctor_set_uint8(x_252, sizeof(void*)*2, x_253);
x_254 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_247, 0, x_254);
return x_247;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; lean_object* x_261; lean_object* x_262; 
x_255 = lean_ctor_get(x_247, 0);
x_256 = lean_ctor_get(x_247, 1);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_247);
x_257 = lean_box(0);
x_258 = l_Nat_Linear_Expr_inc(x_245);
x_259 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_255);
x_260 = lean_unbox(x_257);
lean_ctor_set_uint8(x_259, sizeof(void*)*2, x_260);
x_261 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_261, 0, x_259);
x_262 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_256);
return x_262;
}
}
else
{
uint8_t x_263; 
lean_dec(x_245);
x_263 = !lean_is_exclusive(x_247);
if (x_263 == 0)
{
return x_247;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_247, 0);
x_265 = lean_ctor_get(x_247, 1);
lean_inc(x_265);
lean_inc(x_264);
lean_dec(x_247);
x_266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
return x_266;
}
}
}
else
{
uint8_t x_267; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_267 = !lean_is_exclusive(x_244);
if (x_267 == 0)
{
return x_244;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_244, 0);
x_269 = lean_ctor_get(x_244, 1);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_244);
x_270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_270, 0, x_268);
lean_ctor_set(x_270, 1, x_269);
return x_270;
}
}
}
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
if (lean_is_scalar(x_11)) {
 x_13 = lean_alloc_ctor(0, 2, 0);
} else {
 x_13 = x_11;
}
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg___closed__3;
x_8 = lean_st_mk_ref(x_7, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_9);
x_11 = lean_apply_6(x_1, x_9, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_9, x_13);
lean_dec(x_9);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_12);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_24 = x_21;
} else {
 lean_dec_ref(x_21);
 x_24 = lean_box(0);
}
if (lean_is_scalar(x_24)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_24;
}
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_9);
x_27 = !lean_is_exclusive(x_11);
if (x_27 == 0)
{
return x_11;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_11, 0);
x_29 = lean_ctor_get(x_11, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_11);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___boxed), 7, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_dec_eq(x_13, x_14);
lean_dec(x_13);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_8, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_8, 0);
lean_dec(x_18);
x_19 = lean_box(1);
x_20 = lean_unbox(x_19);
x_21 = l_Lean_sortExprs(x_12, x_20);
lean_dec(x_12);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = l_Nat_Linear_Expr_applyPerm_go(x_24, x_11);
lean_dec(x_24);
lean_ctor_set(x_21, 1, x_23);
lean_ctor_set(x_21, 0, x_25);
lean_ctor_set(x_8, 0, x_21);
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
x_28 = l_Nat_Linear_Expr_applyPerm_go(x_27, x_11);
lean_dec(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_8, 0, x_29);
return x_8;
}
}
else
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_8);
x_30 = lean_box(1);
x_31 = lean_unbox(x_30);
x_32 = l_Lean_sortExprs(x_12, x_31);
lean_dec(x_12);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
x_36 = l_Nat_Linear_Expr_applyPerm_go(x_34, x_11);
lean_dec(x_34);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_33);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_10);
return x_38;
}
}
else
{
lean_dec(x_12);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearCnstr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___boxed), 7, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_9);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_8, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_9, 1);
x_21 = lean_ctor_get(x_9, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_10);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_array_get_size(x_20);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_dec_le(x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; 
lean_free_object(x_9);
x_27 = lean_box(1);
x_28 = lean_unbox(x_27);
x_29 = l_Lean_sortExprs(x_20, x_28);
lean_dec(x_20);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
x_33 = l_Nat_Linear_ExprCnstr_applyPerm(x_32, x_23);
lean_dec(x_32);
lean_ctor_set(x_29, 1, x_31);
lean_ctor_set(x_29, 0, x_33);
lean_ctor_set(x_10, 0, x_29);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_29, 0);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_29);
x_36 = l_Nat_Linear_ExprCnstr_applyPerm(x_35, x_23);
lean_dec(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
lean_ctor_set(x_10, 0, x_37);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
}
else
{
lean_ctor_set(x_9, 0, x_23);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_10, 0);
lean_inc(x_38);
lean_dec(x_10);
x_39 = lean_array_get_size(x_20);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_dec_le(x_39, x_40);
lean_dec(x_39);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_free_object(x_9);
x_42 = lean_box(1);
x_43 = lean_unbox(x_42);
x_44 = l_Lean_sortExprs(x_20, x_43);
lean_dec(x_20);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_47 = x_44;
} else {
 lean_dec_ref(x_44);
 x_47 = lean_box(0);
}
x_48 = l_Nat_Linear_ExprCnstr_applyPerm(x_46, x_38);
lean_dec(x_46);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_8, 0, x_50);
return x_8;
}
else
{
lean_object* x_51; 
lean_ctor_set(x_9, 0, x_38);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_9);
lean_ctor_set(x_8, 0, x_51);
return x_8;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_52 = lean_ctor_get(x_9, 1);
lean_inc(x_52);
lean_dec(x_9);
x_53 = lean_ctor_get(x_10, 0);
lean_inc(x_53);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_54 = x_10;
} else {
 lean_dec_ref(x_10);
 x_54 = lean_box(0);
}
x_55 = lean_array_get_size(x_52);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_dec_le(x_55, x_56);
lean_dec(x_55);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_58 = lean_box(1);
x_59 = lean_unbox(x_58);
x_60 = l_Lean_sortExprs(x_52, x_59);
lean_dec(x_52);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
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
x_64 = l_Nat_Linear_ExprCnstr_applyPerm(x_62, x_53);
lean_dec(x_62);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_61);
if (lean_is_scalar(x_54)) {
 x_66 = lean_alloc_ctor(1, 1, 0);
} else {
 x_66 = x_54;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_8, 0, x_66);
return x_8;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_53);
lean_ctor_set(x_67, 1, x_52);
if (lean_is_scalar(x_54)) {
 x_68 = lean_alloc_ctor(1, 1, 0);
} else {
 x_68 = x_54;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_8, 0, x_68);
return x_8;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_69 = lean_ctor_get(x_8, 1);
lean_inc(x_69);
lean_dec(x_8);
x_70 = lean_ctor_get(x_9, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_71 = x_9;
} else {
 lean_dec_ref(x_9);
 x_71 = lean_box(0);
}
x_72 = lean_ctor_get(x_10, 0);
lean_inc(x_72);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_73 = x_10;
} else {
 lean_dec_ref(x_10);
 x_73 = lean_box(0);
}
x_74 = lean_array_get_size(x_70);
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_nat_dec_le(x_74, x_75);
lean_dec(x_74);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_71);
x_77 = lean_box(1);
x_78 = lean_unbox(x_77);
x_79 = l_Lean_sortExprs(x_70, x_78);
lean_dec(x_70);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_82 = x_79;
} else {
 lean_dec_ref(x_79);
 x_82 = lean_box(0);
}
x_83 = l_Nat_Linear_ExprCnstr_applyPerm(x_81, x_72);
lean_dec(x_81);
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_82;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_80);
if (lean_is_scalar(x_73)) {
 x_85 = lean_alloc_ctor(1, 1, 0);
} else {
 x_85 = x_73;
}
lean_ctor_set(x_85, 0, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_69);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
if (lean_is_scalar(x_71)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_71;
}
lean_ctor_set(x_87, 0, x_72);
lean_ctor_set(x_87, 1, x_70);
if (lean_is_scalar(x_73)) {
 x_88 = lean_alloc_ctor(1, 1, 0);
} else {
 x_88 = x_73;
}
lean_ctor_set(x_88, 0, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_69);
return x_89;
}
}
}
}
else
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_8);
if (x_90 == 0)
{
return x_8;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_8, 0);
x_92 = lean_ctor_get(x_8, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_8);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f___closed__16;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_mkNatLit(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_dec_lt(x_7, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0___boxed), 1, 0);
x_11 = l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__0;
x_12 = l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__2;
x_13 = l_Lean_RArray_toExpr___redArg(x_11, x_10, x_12, x_2, x_3, x_4, x_5, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0___boxed), 1, 0);
x_15 = l_Lean_Meta_Simp_Arith_Nat_toContextExpr___closed__0;
x_16 = l_Lean_RArray_ofArray___redArg(x_1);
x_17 = l_Lean_RArray_toExpr___redArg(x_15, x_14, x_16, x_2, x_3, x_4, x_5, x_6);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Lean_Util_SortExprs(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Check(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Offset(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_KExprMap(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_RArray(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_SortExprs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Check(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Offset(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_KExprMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_RArray(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__0____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_ = _init_l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__0____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__0____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_);
l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__1____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_ = _init_l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__1____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__1____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_);
l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__2____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_ = _init_l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__2____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__2____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_);
l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__3____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_ = _init_l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__3____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__3____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_);
l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__4____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_ = _init_l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__4____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__4____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_);
l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__5____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_ = _init_l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__5____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__5____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_);
l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__6____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_ = _init_l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__6____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__6____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_);
l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__7____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_ = _init_l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__7____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__7____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_);
l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__8____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_ = _init_l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__8____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__8____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_);
l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__9____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_ = _init_l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__9____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__9____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_);
l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__10____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_ = _init_l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__10____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__10____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_);
l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__11____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_ = _init_l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__11____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__11____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_);
l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__12____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_ = _init_l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__12____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__12____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_);
l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__13____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_ = _init_l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__13____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__13____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_);
l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__14____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_ = _init_l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__14____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__14____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_);
l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__15____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_ = _init_l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__15____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__15____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_);
l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__16____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_ = _init_l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__16____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_reprExpr___closed__16____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_);
l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean___closed__0 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean___closed__0);
l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean);
l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__0____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_ = _init_l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__0____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__0____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_);
l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__1____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_ = _init_l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__1____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__1____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_);
l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__2____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_ = _init_l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__2____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__2____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_);
l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__3____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_ = _init_l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__3____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__3____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_);
l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__4____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_ = _init_l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__4____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__4____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_);
l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__5____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_ = _init_l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__5____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__5____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_);
l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__6____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_ = _init_l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__6____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__6____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_);
l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__7____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_ = _init_l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__7____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__7____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_);
l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__8____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_ = _init_l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__8____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__8____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_);
l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__9____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_ = _init_l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__9____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__9____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_);
l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__10____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_ = _init_l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__10____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__10____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_);
l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__11____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_ = _init_l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__11____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__11____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_);
l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__12____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_ = _init_l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__12____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__12____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_);
l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__13____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_ = _init_l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__13____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__13____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_);
l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__14____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_ = _init_l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__14____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__14____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_);
l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__15____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_ = _init_l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__15____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__15____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_);
l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__16____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_ = _init_l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__16____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__16____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_);
l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__17____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_ = _init_l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__17____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg___closed__17____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_);
l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean___closed__0 = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean___closed__0);
l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean);
l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg___closed__0 = _init_l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg___closed__0();
lean_mark_persistent(l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg___closed__0);
l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg___closed__1 = _init_l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg___closed__1();
lean_mark_persistent(l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg___closed__1);
l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg___closed__2 = _init_l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg___closed__2();
lean_mark_persistent(l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg___closed__2);
l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg___closed__3 = _init_l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg___closed__3();
lean_mark_persistent(l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg___closed__3);
l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg___closed__4 = _init_l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg___closed__4();
lean_mark_persistent(l_Prod_repr___at___List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg___closed__4);
l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___closed__0 = _init_l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___closed__0();
lean_mark_persistent(l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___closed__0);
l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___closed__1 = _init_l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___closed__1();
lean_mark_persistent(l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___closed__1);
l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___closed__2 = _init_l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___closed__2();
lean_mark_persistent(l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___closed__2);
l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___closed__3 = _init_l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___closed__3();
lean_mark_persistent(l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___closed__3);
l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___closed__4 = _init_l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___closed__4();
lean_mark_persistent(l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___closed__4);
l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___closed__5 = _init_l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___closed__5();
lean_mark_persistent(l_List_repr___at___Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___closed__5);
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
l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr = _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__0 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__0);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__1 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__1);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__2 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__2);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__3 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__3);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__4 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__4);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__5 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__5);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__6 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__6);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__7 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__7();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__7);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__8 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__8();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__8);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__9 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__9();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__9);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__10 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__10();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__10);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__11 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__11();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__11);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__12 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__12();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__12);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__13 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__13();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__13);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__14 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__14();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__14);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__15 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__15();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__15);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__16 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__16();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__16);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__17 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__17();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit___closed__17);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__0 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__0);
l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__1 = _init_l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___closed__1);
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
