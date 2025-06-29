// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Arith.Int.Basic
// Imports: Init.Data.Int.Linear Lean.Util.SortExprs Lean.Meta.Check Lean.Meta.Offset Lean.Meta.IntInstTesters Lean.Meta.AppBuilder Lean.Meta.KExprMap Lean.Data.RArray
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
lean_object* l_Lean_Meta_isInstHAddInt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_adapter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Int_Linear_reprPoly___closed__5____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_;
LEAN_EXPORT lean_object* l_Int_Linear_reprPoly____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstAddInt___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_Linear_instReprPoly__lean___closed__0;
lean_object* l_Lean_mkNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__11;
static lean_object* l_Int_Linear_reprExpr___closed__13____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
static lean_object* l_Int_Linear_reprExpr___closed__19____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_denoteExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__13;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__13;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Int_Linear_Expr_applyPerm_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__2;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__18;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16;
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__0;
static lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1;
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_Meta_isInstLTInt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_mkIntSub(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__5;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__9;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__8;
LEAN_EXPORT lean_object* l_Int_Linear_Expr_denoteExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14;
static lean_object* l_Int_Linear_reprExpr___closed__12____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__7;
static lean_object* l_Int_Linear_reprExpr___closed__4____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
static lean_object* l_Int_Linear_instReprExpr__lean___closed__0;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__3;
lean_object* l_Lean_mkIntMul(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
static lean_object* l_Int_Linear_reprExpr___closed__17____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_Linear_reprPoly___closed__3____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_;
static lean_object* l_Int_Linear_reprExpr___closed__16____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
uint8_t lean_int_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0;
lean_object* l_Lean_RArray_toExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprPoly;
lean_object* l_Lean_Level_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr___lam__0___boxed(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__12;
lean_object* l_Lean_Meta_isInstMulInt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_reprPoly____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348____boxed(lean_object*, lean_object*);
static lean_object* l_Int_Linear_reprExpr___closed__1____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__20;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__3;
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprExpr;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__15;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__4;
lean_object* l_Lean_sortExprs(lean_object*, uint8_t);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__11;
static lean_object* l_Int_Linear_reprExpr___closed__15____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
static lean_object* l_Int_Linear_reprExpr___closed__7____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__6;
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_toExpr_go(lean_object*, lean_object*);
lean_object* l_Lean_Meta_KExprMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstHMulInt___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_KExprMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__0;
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__14;
static lean_object* l_Int_Linear_reprExpr___closed__9____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__14;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__18;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__5;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__7;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__8;
LEAN_EXPORT lean_object* l_Int_Linear_Expr_applyPerm___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__15;
static lean_object* l_Int_Linear_reprExpr___closed__10____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
lean_object* l_Lean_RArray_ofArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprExpr___lam__0(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Int_Linear_reprExpr___closed__14____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__2;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__5;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Int_Linear_reprPoly___closed__2____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__0;
lean_object* l_Lean_Meta_isInstDvdInt___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__14;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(lean_object*);
lean_object* l_Lean_Meta_isInstHSubInt___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__22;
static lean_object* l_Int_Linear_reprExpr___closed__18____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__3;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr___lam__0(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__1;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__12;
static lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__0;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__1;
static lean_object* l_Int_Linear_reprExpr___closed__11____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__7;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__9;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__13;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__4;
lean_object* l_Lean_mkIntLit(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_instReprPoly__lean;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__5;
lean_object* l_Lean_mkIntAdd(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__11;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__6;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__3;
static lean_object* l_Int_Linear_reprPoly___closed__1____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_applyPerm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly(lean_object*);
static lean_object* l_Int_Linear_reprExpr___closed__5____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__18;
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__19;
static lean_object* l_Int_Linear_reprExpr___closed__8____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
static lean_object* l_Int_Linear_Poly_toExpr_go___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_toExpr(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__2;
static lean_object* l_Int_Linear_reprExpr___closed__6____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
LEAN_EXPORT lean_object* l_Int_Linear_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprPoly___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__10;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__3;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__17;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__17;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_applyPerm_go(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Int_Linear_reprPoly___closed__6____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__9;
lean_object* l_Lean_Meta_isInstNegInt___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__4;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__0;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___closed__0;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11;
LEAN_EXPORT lean_object* l_Int_Linear_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476____boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__19;
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__4;
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstLEInt___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__2;
static lean_object* l_Int_Linear_reprExpr___closed__3____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__9;
static lean_object* l_Int_Linear_reprPoly___closed__0____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
static lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__1;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Int_Linear_Expr_applyPerm_go_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__10;
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__21;
LEAN_EXPORT lean_object* l_Int_Linear_instReprExpr__lean;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Int_Linear_Expr_applyPerm_go_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__6;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__8;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__16;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Int_Linear_reprPoly___closed__4____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_;
lean_object* l_Lean_Meta_isInstSubInt___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__6;
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_int_neg(lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__12;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Int_Linear_Expr_applyPerm_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_applyPerm_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_denoteExpr___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__16;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__2;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__2;
static lean_object* l_Int_Linear_reprExpr___closed__2____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__1;
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__15;
static lean_object* l_Int_Linear_reprExpr___closed__0____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
lean_object* l_Lean_mkIntNeg(lean_object*);
static lean_object* l_Int_Linear_reprExpr___closed__20____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
static lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__7;
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__0;
static lean_object* l_Int_Linear_Poly_toExpr_go___closed__1;
static lean_object* _init_l_Int_Linear_Poly_toExpr_go___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Int_Linear_Poly_toExpr_go___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_toExpr_go(lean_object* x_1, lean_object* x_2) {
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
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Int_Linear_Poly_toExpr_go___closed__0;
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
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = l_Int_Linear_Poly_toExpr_go___closed__1;
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
x_25 = l_Int_Linear_Poly_toExpr_go___closed__1;
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
lean_inc(x_33);
lean_dec(x_2);
x_34 = l_Int_Linear_Poly_toExpr_go___closed__0;
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
lean_inc(x_46);
lean_dec(x_2);
x_47 = l_Int_Linear_Poly_toExpr_go___closed__0;
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
x_3 = l_Int_Linear_Poly_toExpr_go(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Int_Linear_Expr_applyPerm_go_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Int_Linear_Expr_applyPerm_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Int_Linear_Expr_applyPerm_go_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_applyPerm_go(lean_object* x_1, lean_object* x_2) {
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
x_19 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Int_Linear_Expr_applyPerm_go_spec__0___redArg(x_3, x_18);
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
x_28 = l_Int_Linear_Expr_applyPerm_go(x_1, x_26);
x_29 = l_Int_Linear_Expr_applyPerm_go(x_1, x_27);
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
x_32 = l_Int_Linear_Expr_applyPerm_go(x_1, x_30);
x_33 = l_Int_Linear_Expr_applyPerm_go(x_1, x_31);
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
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_2, 0);
x_37 = lean_ctor_get(x_2, 1);
x_38 = l_Int_Linear_Expr_applyPerm_go(x_1, x_36);
x_39 = l_Int_Linear_Expr_applyPerm_go(x_1, x_37);
lean_ctor_set(x_2, 1, x_39);
lean_ctor_set(x_2, 0, x_38);
return x_2;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_2, 0);
x_41 = lean_ctor_get(x_2, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_2);
x_42 = l_Int_Linear_Expr_applyPerm_go(x_1, x_40);
x_43 = l_Int_Linear_Expr_applyPerm_go(x_1, x_41);
x_44 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
case 4:
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_2);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_2, 0);
x_47 = l_Int_Linear_Expr_applyPerm_go(x_1, x_46);
lean_ctor_set(x_2, 0, x_47);
return x_2;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_2, 0);
lean_inc(x_48);
lean_dec(x_2);
x_49 = l_Int_Linear_Expr_applyPerm_go(x_1, x_48);
x_50 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
case 5:
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_2);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_2, 1);
x_53 = l_Int_Linear_Expr_applyPerm_go(x_1, x_52);
lean_ctor_set(x_2, 1, x_53);
return x_2;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_2, 0);
x_55 = lean_ctor_get(x_2, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_2);
x_56 = l_Int_Linear_Expr_applyPerm_go(x_1, x_55);
x_57 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
default: 
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_2);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_2, 0);
x_60 = l_Int_Linear_Expr_applyPerm_go(x_1, x_59);
lean_ctor_set(x_2, 0, x_60);
return x_2;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_2, 0);
x_62 = lean_ctor_get(x_2, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_2);
x_63 = l_Int_Linear_Expr_applyPerm_go(x_1, x_61);
x_64 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Int_Linear_Expr_applyPerm_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Int_Linear_Expr_applyPerm_go_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Int_Linear_Expr_applyPerm_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Int_Linear_Expr_applyPerm_go_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_applyPerm_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_Linear_Expr_applyPerm_go(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_applyPerm(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_Linear_Expr_applyPerm_go(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_applyPerm___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_Linear_Expr_applyPerm(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Int_Linear_reprPoly___closed__0____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int.Linear.Poly.num", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Int_Linear_reprPoly___closed__1____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Int_Linear_reprPoly___closed__0____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Int_Linear_reprPoly___closed__2____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Int_Linear_reprPoly___closed__1____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_Linear_reprPoly___closed__3____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Int_Linear_reprPoly___closed__4____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int.Linear.Poly.add", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Int_Linear_reprPoly___closed__5____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Int_Linear_reprPoly___closed__4____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Int_Linear_reprPoly___closed__6____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Int_Linear_reprPoly___closed__5____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_reprPoly____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_26; uint8_t x_27; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_14 = x_1;
} else {
 lean_dec_ref(x_1);
 x_14 = lean_box(0);
}
x_26 = lean_unsigned_to_nat(1024u);
x_27 = lean_nat_dec_le(x_26, x_2);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = l_Int_Linear_reprPoly___closed__3____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_;
x_15 = x_28;
goto block_25;
}
else
{
lean_object* x_29; 
x_29 = l_Int_Linear_Poly_toExpr_go___closed__0;
x_15 = x_29;
goto block_25;
}
block_25:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = l_Int_Linear_reprPoly___closed__2____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_;
x_17 = l_Int_Linear_Poly_toExpr_go___closed__1;
x_18 = lean_int_dec_lt(x_13, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Int_repr(x_13);
lean_dec(x_13);
if (lean_is_scalar(x_14)) {
 x_20 = lean_alloc_ctor(3, 1, 0);
} else {
 x_20 = x_14;
 lean_ctor_set_tag(x_20, 3);
}
lean_ctor_set(x_20, 0, x_19);
x_3 = x_16;
x_4 = x_15;
x_5 = x_20;
goto block_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_unsigned_to_nat(1024u);
x_22 = l_Int_repr(x_13);
lean_dec(x_13);
if (lean_is_scalar(x_14)) {
 x_23 = lean_alloc_ctor(3, 1, 0);
} else {
 x_23 = x_14;
 lean_ctor_set_tag(x_23, 3);
}
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Repr_addAppParen(x_23, x_21);
x_3 = x_16;
x_4 = x_15;
x_5 = x_24;
goto block_12;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_52; uint8_t x_63; 
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 2);
lean_inc(x_32);
lean_dec(x_1);
x_33 = lean_unsigned_to_nat(1024u);
x_63 = lean_nat_dec_le(x_33, x_2);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = l_Int_Linear_reprPoly___closed__3____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_;
x_52 = x_64;
goto block_62;
}
else
{
lean_object* x_65; 
x_65 = l_Int_Linear_Poly_toExpr_go___closed__0;
x_52 = x_65;
goto block_62;
}
block_51:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_37);
lean_inc(x_36);
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
x_40 = l_Nat_reprFast(x_31);
x_41 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_36);
x_44 = l_Int_Linear_reprPoly____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_(x_32, x_33);
x_45 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_46, 0, x_35);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_48, 0, x_46);
x_49 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_49);
x_50 = l_Repr_addAppParen(x_48, x_2);
return x_50;
}
block_62:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_box(1);
x_54 = l_Int_Linear_reprPoly___closed__6____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_;
x_55 = l_Int_Linear_Poly_toExpr_go___closed__1;
x_56 = lean_int_dec_lt(x_30, x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = l_Int_repr(x_30);
lean_dec(x_30);
x_58 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_34 = x_54;
x_35 = x_52;
x_36 = x_53;
x_37 = x_58;
goto block_51;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = l_Int_repr(x_30);
lean_dec(x_30);
x_60 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = l_Repr_addAppParen(x_60, x_33);
x_34 = x_54;
x_35 = x_52;
x_36 = x_53;
x_37 = x_61;
goto block_51;
}
}
}
block_12:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_10);
x_11 = l_Repr_addAppParen(x_9, x_2);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_reprPoly____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_Linear_reprPoly____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Int_Linear_instReprPoly__lean___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_Linear_reprPoly____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348____boxed), 2, 0);
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
static lean_object* _init_l_Int_Linear_reprExpr___closed__0____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int.Linear.Expr.num", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Int_Linear_reprExpr___closed__1____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Int_Linear_reprExpr___closed__0____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Int_Linear_reprExpr___closed__2____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Int_Linear_reprExpr___closed__1____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_Linear_reprExpr___closed__3____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int.Linear.Expr.var", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Int_Linear_reprExpr___closed__4____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Int_Linear_reprExpr___closed__3____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Int_Linear_reprExpr___closed__5____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Int_Linear_reprExpr___closed__4____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_Linear_reprExpr___closed__6____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int.Linear.Expr.add", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Int_Linear_reprExpr___closed__7____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Int_Linear_reprExpr___closed__6____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Int_Linear_reprExpr___closed__8____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Int_Linear_reprExpr___closed__7____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_Linear_reprExpr___closed__9____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int.Linear.Expr.sub", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Int_Linear_reprExpr___closed__10____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Int_Linear_reprExpr___closed__9____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Int_Linear_reprExpr___closed__11____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Int_Linear_reprExpr___closed__10____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_Linear_reprExpr___closed__12____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int.Linear.Expr.neg", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Int_Linear_reprExpr___closed__13____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Int_Linear_reprExpr___closed__12____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Int_Linear_reprExpr___closed__14____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Int_Linear_reprExpr___closed__13____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_Linear_reprExpr___closed__15____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int.Linear.Expr.mulL", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Int_Linear_reprExpr___closed__16____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Int_Linear_reprExpr___closed__15____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Int_Linear_reprExpr___closed__17____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Int_Linear_reprExpr___closed__16____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Int_Linear_reprExpr___closed__18____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int.Linear.Expr.mulR", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Int_Linear_reprExpr___closed__19____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Int_Linear_reprExpr___closed__18____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Int_Linear_reprExpr___closed__20____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Int_Linear_reprExpr___closed__19____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_36; uint8_t x_37; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_24 = x_1;
} else {
 lean_dec_ref(x_1);
 x_24 = lean_box(0);
}
x_36 = lean_unsigned_to_nat(1024u);
x_37 = lean_nat_dec_le(x_36, x_2);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = l_Int_Linear_reprPoly___closed__3____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_;
x_25 = x_38;
goto block_35;
}
else
{
lean_object* x_39; 
x_39 = l_Int_Linear_Poly_toExpr_go___closed__0;
x_25 = x_39;
goto block_35;
}
block_35:
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = l_Int_Linear_reprExpr___closed__2____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
x_27 = l_Int_Linear_Poly_toExpr_go___closed__1;
x_28 = lean_int_dec_lt(x_23, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Int_repr(x_23);
lean_dec(x_23);
if (lean_is_scalar(x_24)) {
 x_30 = lean_alloc_ctor(3, 1, 0);
} else {
 x_30 = x_24;
 lean_ctor_set_tag(x_30, 3);
}
lean_ctor_set(x_30, 0, x_29);
x_13 = x_26;
x_14 = x_25;
x_15 = x_30;
goto block_22;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_unsigned_to_nat(1024u);
x_32 = l_Int_repr(x_23);
lean_dec(x_23);
if (lean_is_scalar(x_24)) {
 x_33 = lean_alloc_ctor(3, 1, 0);
} else {
 x_33 = x_24;
 lean_ctor_set_tag(x_33, 3);
}
lean_ctor_set(x_33, 0, x_32);
x_34 = l_Repr_addAppParen(x_33, x_31);
x_13 = x_26;
x_14 = x_25;
x_15 = x_34;
goto block_22;
}
}
}
case 1:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_53; uint8_t x_54; 
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_41 = x_1;
} else {
 lean_dec_ref(x_1);
 x_41 = lean_box(0);
}
x_53 = lean_unsigned_to_nat(1024u);
x_54 = lean_nat_dec_le(x_53, x_2);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = l_Int_Linear_reprPoly___closed__3____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_;
x_42 = x_55;
goto block_52;
}
else
{
lean_object* x_56; 
x_56 = l_Int_Linear_Poly_toExpr_go___closed__0;
x_42 = x_56;
goto block_52;
}
block_52:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; 
x_43 = l_Int_Linear_reprExpr___closed__5____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
x_44 = l_Nat_reprFast(x_40);
if (lean_is_scalar(x_41)) {
 x_45 = lean_alloc_ctor(3, 1, 0);
} else {
 x_45 = x_41;
 lean_ctor_set_tag(x_45, 3);
}
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_49, 0, x_47);
x_50 = lean_unbox(x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_50);
x_51 = l_Repr_addAppParen(x_49, x_2);
return x_51;
}
}
case 2:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_75; 
x_57 = lean_ctor_get(x_1, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_1, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_59 = x_1;
} else {
 lean_dec_ref(x_1);
 x_59 = lean_box(0);
}
x_60 = lean_unsigned_to_nat(1024u);
x_75 = lean_nat_dec_le(x_60, x_2);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = l_Int_Linear_reprPoly___closed__3____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_;
x_61 = x_76;
goto block_74;
}
else
{
lean_object* x_77; 
x_77 = l_Int_Linear_Poly_toExpr_go___closed__0;
x_61 = x_77;
goto block_74;
}
block_74:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; 
x_62 = lean_box(1);
x_63 = l_Int_Linear_reprExpr___closed__8____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
x_64 = l_Int_Linear_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_(x_57, x_60);
if (lean_is_scalar(x_59)) {
 x_65 = lean_alloc_ctor(5, 2, 0);
} else {
 x_65 = x_59;
 lean_ctor_set_tag(x_65, 5);
}
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_62);
x_67 = l_Int_Linear_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_(x_58, x_60);
x_68 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_69, 0, x_61);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_71, 0, x_69);
x_72 = lean_unbox(x_70);
lean_ctor_set_uint8(x_71, sizeof(void*)*1, x_72);
x_73 = l_Repr_addAppParen(x_71, x_2);
return x_73;
}
}
case 3:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_96; 
x_78 = lean_ctor_get(x_1, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_1, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_80 = x_1;
} else {
 lean_dec_ref(x_1);
 x_80 = lean_box(0);
}
x_81 = lean_unsigned_to_nat(1024u);
x_96 = lean_nat_dec_le(x_81, x_2);
if (x_96 == 0)
{
lean_object* x_97; 
x_97 = l_Int_Linear_reprPoly___closed__3____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_;
x_82 = x_97;
goto block_95;
}
else
{
lean_object* x_98; 
x_98 = l_Int_Linear_Poly_toExpr_go___closed__0;
x_82 = x_98;
goto block_95;
}
block_95:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; 
x_83 = lean_box(1);
x_84 = l_Int_Linear_reprExpr___closed__11____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
x_85 = l_Int_Linear_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_(x_78, x_81);
if (lean_is_scalar(x_80)) {
 x_86 = lean_alloc_ctor(5, 2, 0);
} else {
 x_86 = x_80;
 lean_ctor_set_tag(x_86, 5);
}
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_83);
x_88 = l_Int_Linear_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_(x_79, x_81);
x_89 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_90, 0, x_82);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_box(0);
x_92 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_92, 0, x_90);
x_93 = lean_unbox(x_91);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_93);
x_94 = l_Repr_addAppParen(x_92, x_2);
return x_94;
}
}
case 4:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_111; 
x_99 = lean_ctor_get(x_1, 0);
lean_inc(x_99);
lean_dec(x_1);
x_100 = lean_unsigned_to_nat(1024u);
x_111 = lean_nat_dec_le(x_100, x_2);
if (x_111 == 0)
{
lean_object* x_112; 
x_112 = l_Int_Linear_reprPoly___closed__3____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_;
x_101 = x_112;
goto block_110;
}
else
{
lean_object* x_113; 
x_113 = l_Int_Linear_Poly_toExpr_go___closed__0;
x_101 = x_113;
goto block_110;
}
block_110:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; 
x_102 = l_Int_Linear_reprExpr___closed__14____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
x_103 = l_Int_Linear_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_(x_99, x_100);
x_104 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_105, 0, x_101);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_box(0);
x_107 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_107, 0, x_105);
x_108 = lean_unbox(x_106);
lean_ctor_set_uint8(x_107, sizeof(void*)*1, x_108);
x_109 = l_Repr_addAppParen(x_107, x_2);
return x_109;
}
}
case 5:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_132; uint8_t x_143; 
x_114 = lean_ctor_get(x_1, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_1, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_116 = x_1;
} else {
 lean_dec_ref(x_1);
 x_116 = lean_box(0);
}
x_117 = lean_unsigned_to_nat(1024u);
x_143 = lean_nat_dec_le(x_117, x_2);
if (x_143 == 0)
{
lean_object* x_144; 
x_144 = l_Int_Linear_reprPoly___closed__3____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_;
x_132 = x_144;
goto block_142;
}
else
{
lean_object* x_145; 
x_145 = l_Int_Linear_Poly_toExpr_go___closed__0;
x_132 = x_145;
goto block_142;
}
block_131:
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; lean_object* x_130; 
if (lean_is_scalar(x_116)) {
 x_122 = lean_alloc_ctor(5, 2, 0);
} else {
 x_122 = x_116;
}
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_119);
x_124 = l_Int_Linear_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_(x_115, x_117);
x_125 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_126, 0, x_118);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_box(0);
x_128 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_128, 0, x_126);
x_129 = lean_unbox(x_127);
lean_ctor_set_uint8(x_128, sizeof(void*)*1, x_129);
x_130 = l_Repr_addAppParen(x_128, x_2);
return x_130;
}
block_142:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_133 = lean_box(1);
x_134 = l_Int_Linear_reprExpr___closed__17____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
x_135 = l_Int_Linear_Poly_toExpr_go___closed__1;
x_136 = lean_int_dec_lt(x_114, x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = l_Int_repr(x_114);
lean_dec(x_114);
x_138 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_138, 0, x_137);
x_118 = x_132;
x_119 = x_133;
x_120 = x_134;
x_121 = x_138;
goto block_131;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = l_Int_repr(x_114);
lean_dec(x_114);
x_140 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_140, 0, x_139);
x_141 = l_Repr_addAppParen(x_140, x_117);
x_118 = x_132;
x_119 = x_133;
x_120 = x_134;
x_121 = x_141;
goto block_131;
}
}
}
default: 
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_164; 
x_146 = lean_ctor_get(x_1, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_1, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_148 = x_1;
} else {
 lean_dec_ref(x_1);
 x_148 = lean_box(0);
}
x_149 = lean_unsigned_to_nat(1024u);
x_164 = lean_nat_dec_le(x_149, x_2);
if (x_164 == 0)
{
lean_object* x_165; 
x_165 = l_Int_Linear_reprPoly___closed__3____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_;
x_150 = x_165;
goto block_163;
}
else
{
lean_object* x_166; 
x_166 = l_Int_Linear_Poly_toExpr_go___closed__0;
x_150 = x_166;
goto block_163;
}
block_163:
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_151 = lean_box(1);
x_152 = l_Int_Linear_reprExpr___closed__20____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_;
x_153 = l_Int_Linear_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_(x_146, x_149);
if (lean_is_scalar(x_148)) {
 x_154 = lean_alloc_ctor(5, 2, 0);
} else {
 x_154 = x_148;
 lean_ctor_set_tag(x_154, 5);
}
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
x_155 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_151);
x_156 = l_Int_Linear_Poly_toExpr_go___closed__1;
x_157 = lean_int_dec_lt(x_147, x_156);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; 
x_158 = l_Int_repr(x_147);
lean_dec(x_147);
x_159 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_159, 0, x_158);
x_3 = x_155;
x_4 = x_150;
x_5 = x_159;
goto block_12;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = l_Int_repr(x_147);
lean_dec(x_147);
x_161 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_161, 0, x_160);
x_162 = l_Repr_addAppParen(x_161, x_149);
x_3 = x_155;
x_4 = x_150;
x_5 = x_162;
goto block_12;
}
}
}
}
block_12:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_10);
x_11 = l_Repr_addAppParen(x_9, x_2);
return x_11;
}
block_22:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_19, 0, x_17);
x_20 = lean_unbox(x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_20);
x_21 = l_Repr_addAppParen(x_19, x_2);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_Linear_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Int_Linear_instReprExpr__lean___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Int_Linear_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476____boxed), 2, 0);
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
x_3 = l_Lean_Expr_const___override(x_2, x_1);
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
x_3 = l_Lean_Expr_const___override(x_2, x_1);
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
lean_dec(x_1);
x_3 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__5;
x_4 = l_Int_Linear_Poly_toExpr_go___closed__1;
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
lean_inc(x_19);
lean_dec(x_1);
x_20 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__19;
x_26 = l_Int_Linear_Poly_toExpr_go___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprPoly___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__0() {
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
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__0;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_instToExprPoly() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_instToExprPoly___lam__0), 1, 0);
x_2 = l_Lean_Meta_Simp_Arith_Int_instToExprPoly___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
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
x_3 = l_Lean_Expr_const___override(x_2, x_1);
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
x_3 = l_Lean_Expr_const___override(x_2, x_1);
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
x_3 = l_Lean_Expr_const___override(x_2, x_1);
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
x_3 = l_Lean_Expr_const___override(x_2, x_1);
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
x_3 = l_Lean_Expr_const___override(x_2, x_1);
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
x_3 = l_Lean_Expr_const___override(x_2, x_1);
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
x_3 = l_Lean_Expr_const___override(x_2, x_1);
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
lean_dec(x_1);
x_3 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__2;
x_4 = l_Int_Linear_Poly_toExpr_go___closed__1;
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
lean_dec(x_1);
x_18 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__5;
x_19 = l_Lean_mkNatLit(x_17);
x_20 = l_Lean_Expr_app___override(x_18, x_19);
return x_20;
}
case 2:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_dec(x_1);
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
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
lean_dec(x_1);
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
lean_inc(x_33);
lean_dec(x_1);
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
lean_inc(x_38);
lean_dec(x_1);
x_39 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__15;
x_44 = l_Int_Linear_Poly_toExpr_go___closed__1;
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
lean_inc(x_55);
x_56 = lean_ctor_get(x_1, 1);
lean_inc(x_56);
lean_dec(x_1);
x_57 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__18;
x_58 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_55);
x_59 = l_Int_Linear_Poly_toExpr_go___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprExpr___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__0() {
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
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__0;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_instToExprExpr() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_instToExprExpr___lam__0), 1, 0);
x_2 = l_Lean_Meta_Simp_Arith_Int_instToExprExpr___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_denoteExpr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
lean_dec(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Int_Linear_Poly_toExpr_go___closed__1;
x_6 = lean_int_dec_le(x_5, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11;
x_8 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13;
x_9 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16;
x_10 = lean_int_neg(x_4);
lean_dec(x_4);
x_11 = l_Int_toNat(x_10);
lean_dec(x_10);
x_12 = l_Lean_instToExprInt_mkNat(x_11);
x_13 = l_Lean_mkApp3(x_7, x_8, x_9, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Int_toNat(x_4);
lean_dec(x_4);
x_16 = l_Lean_instToExprInt_mkNat(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
}
case 1:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_apply_1(x_1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
return x_20;
}
case 2:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec(x_2);
lean_inc(x_1);
x_23 = l_Int_Linear_Expr_denoteExpr___redArg(x_1, x_21, x_3);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Int_Linear_Expr_denoteExpr___redArg(x_1, x_22, x_25);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = l_Lean_mkIntAdd(x_24, x_28);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_26);
x_32 = l_Lean_mkIntAdd(x_24, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
case 3:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_2, 1);
lean_inc(x_35);
lean_dec(x_2);
lean_inc(x_1);
x_36 = l_Int_Linear_Expr_denoteExpr___redArg(x_1, x_34, x_3);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Int_Linear_Expr_denoteExpr___redArg(x_1, x_35, x_38);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = l_Lean_mkIntSub(x_37, x_41);
lean_ctor_set(x_39, 0, x_42);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_39, 0);
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_39);
x_45 = l_Lean_mkIntSub(x_37, x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
case 4:
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_2, 0);
lean_inc(x_47);
lean_dec(x_2);
x_48 = l_Int_Linear_Expr_denoteExpr___redArg(x_1, x_47, x_3);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = l_Lean_mkIntNeg(x_50);
lean_ctor_set(x_48, 0, x_51);
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_48, 0);
x_53 = lean_ctor_get(x_48, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_48);
x_54 = l_Lean_mkIntNeg(x_52);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
case 5:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_66; uint8_t x_67; 
x_56 = lean_ctor_get(x_2, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_2, 1);
lean_inc(x_57);
lean_dec(x_2);
x_58 = l_Int_Linear_Expr_denoteExpr___redArg(x_1, x_57, x_3);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_61 = x_58;
} else {
 lean_dec_ref(x_58);
 x_61 = lean_box(0);
}
x_66 = l_Int_Linear_Poly_toExpr_go___closed__1;
x_67 = lean_int_dec_le(x_66, x_56);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_68 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11;
x_69 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13;
x_70 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16;
x_71 = lean_int_neg(x_56);
lean_dec(x_56);
x_72 = l_Int_toNat(x_71);
lean_dec(x_71);
x_73 = l_Lean_instToExprInt_mkNat(x_72);
x_74 = l_Lean_mkApp3(x_68, x_69, x_70, x_73);
x_62 = x_74;
goto block_65;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = l_Int_toNat(x_56);
lean_dec(x_56);
x_76 = l_Lean_instToExprInt_mkNat(x_75);
x_62 = x_76;
goto block_65;
}
block_65:
{
lean_object* x_63; lean_object* x_64; 
x_63 = l_Lean_mkIntMul(x_62, x_59);
if (lean_is_scalar(x_61)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_61;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_60);
return x_64;
}
}
default: 
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_87; uint8_t x_88; 
x_77 = lean_ctor_get(x_2, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_2, 1);
lean_inc(x_78);
lean_dec(x_2);
x_79 = l_Int_Linear_Expr_denoteExpr___redArg(x_1, x_77, x_3);
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
x_87 = l_Int_Linear_Poly_toExpr_go___closed__1;
x_88 = lean_int_dec_le(x_87, x_78);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_89 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11;
x_90 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13;
x_91 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16;
x_92 = lean_int_neg(x_78);
lean_dec(x_78);
x_93 = l_Int_toNat(x_92);
lean_dec(x_92);
x_94 = l_Lean_instToExprInt_mkNat(x_93);
x_95 = l_Lean_mkApp3(x_89, x_90, x_91, x_94);
x_83 = x_95;
goto block_86;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = l_Int_toNat(x_78);
lean_dec(x_78);
x_97 = l_Lean_instToExprInt_mkNat(x_96);
x_83 = x_97;
goto block_86;
}
block_86:
{
lean_object* x_84; lean_object* x_85; 
x_84 = l_Lean_mkIntMul(x_80, x_83);
if (lean_is_scalar(x_82)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_82;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_81);
return x_85;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_denoteExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Int_Linear_Expr_denoteExpr___redArg(x_1, x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_denoteExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Int_Linear_Expr_denoteExpr(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_dec(x_1);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l_Int_Linear_Poly_toExpr_go___closed__1;
x_11 = lean_int_dec_eq(x_9, x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = lean_int_dec_le(x_10, x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11;
x_14 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13;
x_15 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16;
x_16 = lean_int_neg(x_9);
lean_dec(x_9);
x_17 = l_Int_toNat(x_16);
lean_dec(x_16);
x_18 = l_Lean_instToExprInt_mkNat(x_17);
x_19 = l_Lean_mkApp3(x_13, x_14, x_15, x_18);
x_5 = x_19;
goto block_8;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Int_toNat(x_9);
lean_dec(x_9);
x_21 = l_Lean_instToExprInt_mkNat(x_20);
x_5 = x_21;
goto block_8;
}
}
else
{
lean_object* x_22; 
lean_dec(x_9);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_4);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_32; uint8_t x_33; 
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_3, 2);
lean_inc(x_25);
lean_dec(x_3);
x_32 = l_Int_Linear_Poly_toExpr_go___closed__0;
x_33 = lean_int_dec_eq(x_23, x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = l_Int_Linear_Poly_toExpr_go___closed__1;
x_35 = lean_int_dec_le(x_34, x_23);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11;
x_37 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13;
x_38 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16;
x_39 = lean_int_neg(x_23);
lean_dec(x_23);
x_40 = l_Int_toNat(x_39);
lean_dec(x_39);
x_41 = l_Lean_instToExprInt_mkNat(x_40);
x_42 = l_Lean_mkApp3(x_36, x_37, x_38, x_41);
x_26 = x_42;
goto block_31;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = l_Int_toNat(x_23);
lean_dec(x_23);
x_44 = l_Lean_instToExprInt_mkNat(x_43);
x_26 = x_44;
goto block_31;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_23);
lean_inc(x_1);
x_45 = lean_apply_1(x_1, x_24);
x_46 = l_Lean_mkIntAdd(x_2, x_45);
x_2 = x_46;
x_3 = x_25;
goto _start;
}
block_31:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_inc(x_1);
x_27 = lean_apply_1(x_1, x_24);
x_28 = l_Lean_mkIntMul(x_26, x_27);
x_29 = l_Lean_mkIntAdd(x_2, x_28);
x_2 = x_29;
x_3 = x_25;
goto _start;
}
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_mkIntAdd(x_2, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Int_Linear_Poly_denoteExpr_go___redArg(x_1, x_2, x_3, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Int_Linear_Poly_denoteExpr_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
lean_dec(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Int_Linear_Poly_toExpr_go___closed__1;
x_6 = lean_int_dec_le(x_5, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11;
x_8 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13;
x_9 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16;
x_10 = lean_int_neg(x_4);
lean_dec(x_4);
x_11 = l_Int_toNat(x_10);
lean_dec(x_10);
x_12 = l_Lean_instToExprInt_mkNat(x_11);
x_13 = l_Lean_mkApp3(x_7, x_8, x_9, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Int_toNat(x_4);
lean_dec(x_4);
x_16 = l_Lean_instToExprInt_mkNat(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_26; uint8_t x_27; 
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 2);
lean_inc(x_20);
lean_dec(x_2);
x_26 = l_Int_Linear_Poly_toExpr_go___closed__0;
x_27 = lean_int_dec_eq(x_18, x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = l_Int_Linear_Poly_toExpr_go___closed__1;
x_29 = lean_int_dec_le(x_28, x_18);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__11;
x_31 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13;
x_32 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__16;
x_33 = lean_int_neg(x_18);
lean_dec(x_18);
x_34 = l_Int_toNat(x_33);
lean_dec(x_33);
x_35 = l_Lean_instToExprInt_mkNat(x_34);
x_36 = l_Lean_mkApp3(x_30, x_31, x_32, x_35);
x_21 = x_36;
goto block_25;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Int_toNat(x_18);
lean_dec(x_18);
x_38 = l_Lean_instToExprInt_mkNat(x_37);
x_21 = x_38;
goto block_25;
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_18);
lean_inc(x_1);
x_39 = lean_apply_1(x_1, x_19);
x_40 = l_Int_Linear_Poly_denoteExpr_go___redArg(x_1, x_39, x_20, x_3);
return x_40;
}
block_25:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_inc(x_1);
x_22 = lean_apply_1(x_1, x_19);
x_23 = l_Lean_mkIntMul(x_21, x_22);
x_24 = l_Int_Linear_Poly_denoteExpr_go___redArg(x_1, x_23, x_20, x_3);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Int_Linear_Poly_denoteExpr___redArg(x_1, x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Int_Linear_Poly_denoteExpr(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__7;
x_2 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mul", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__1;
x_2 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__8;
x_2 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17;
x_2 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("OfNat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ofNat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__6;
x_2 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__5;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Mul", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__1;
x_2 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__8;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Sub", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr___closed__8;
x_2 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__10;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Add", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__17;
x_2 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__12;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HMul", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hMul", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__15;
x_2 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__14;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HSub", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hSub", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__18;
x_2 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__17;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HAdd", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hAdd", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__21;
x_2 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__20;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_inc(x_1);
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
x_12 = l_Lean_Expr_cleanupAnnotations(x_9);
x_13 = l_Lean_Expr_isApp(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
lean_dec(x_11);
x_14 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
x_16 = l_Lean_Expr_appFnCleanup___redArg(x_12);
x_17 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__0;
x_18 = l_Lean_Expr_isConstOf(x_16, x_17);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_Expr_isApp(x_16);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
x_20 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
x_65 = l_Lean_Expr_appFnCleanup___redArg(x_16);
x_66 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__2;
x_67 = l_Lean_Expr_isConstOf(x_65, x_66);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__3;
x_69 = l_Lean_Expr_isConstOf(x_65, x_68);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__4;
x_71 = l_Lean_Expr_isConstOf(x_65, x_70);
if (x_71 == 0)
{
uint8_t x_72; 
x_72 = l_Lean_Expr_isApp(x_65);
if (x_72 == 0)
{
lean_object* x_73; 
lean_dec(x_65);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_11);
x_73 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_74 = lean_ctor_get(x_65, 1);
lean_inc(x_74);
x_75 = l_Lean_Expr_appFnCleanup___redArg(x_65);
x_76 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__8;
x_77 = l_Lean_Expr_isConstOf(x_75, x_76);
if (x_77 == 0)
{
lean_object* x_78; uint8_t x_79; 
x_78 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__7;
x_79 = l_Lean_Expr_isConstOf(x_75, x_78);
if (x_79 == 0)
{
uint8_t x_80; 
x_80 = l_Lean_Expr_isApp(x_75);
if (x_80 == 0)
{
lean_object* x_81; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_11);
x_81 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = l_Lean_Expr_appFnCleanup___redArg(x_75);
x_83 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__9;
x_84 = l_Lean_Expr_isConstOf(x_82, x_83);
if (x_84 == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__11;
x_86 = l_Lean_Expr_isConstOf(x_82, x_85);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__13;
x_88 = l_Lean_Expr_isConstOf(x_82, x_87);
if (x_88 == 0)
{
uint8_t x_89; 
x_89 = l_Lean_Expr_isApp(x_82);
if (x_89 == 0)
{
lean_object* x_90; 
lean_dec(x_82);
lean_dec(x_74);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_11);
x_90 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_90;
}
else
{
lean_object* x_91; uint8_t x_92; 
x_91 = l_Lean_Expr_appFnCleanup___redArg(x_82);
x_92 = l_Lean_Expr_isApp(x_91);
if (x_92 == 0)
{
lean_object* x_93; 
lean_dec(x_91);
lean_dec(x_74);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_11);
x_93 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_94 = l_Lean_Expr_appFnCleanup___redArg(x_91);
x_95 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__16;
x_96 = l_Lean_Expr_isConstOf(x_94, x_95);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
lean_dec(x_11);
x_97 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__19;
x_98 = l_Lean_Expr_isConstOf(x_94, x_97);
if (x_98 == 0)
{
lean_object* x_99; uint8_t x_100; 
x_99 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__22;
x_100 = l_Lean_Expr_isConstOf(x_94, x_99);
lean_dec(x_94);
if (x_100 == 0)
{
lean_object* x_101; 
lean_dec(x_74);
lean_dec(x_21);
lean_dec(x_15);
x_101 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_102 = l_Lean_Meta_isInstHAddInt___redArg(x_74, x_4, x_10);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_unbox(x_103);
lean_dec(x_103);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_21);
lean_dec(x_15);
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
lean_dec(x_102);
x_106 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_105);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_1);
x_107 = lean_ctor_get(x_102, 1);
lean_inc(x_107);
lean_dec(x_102);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_108 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_21, x_2, x_3, x_4, x_5, x_6, x_107);
if (lean_obj_tag(x_108) == 0)
{
uint8_t x_109; 
x_109 = !lean_is_exclusive(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_108, 0);
x_111 = lean_ctor_get(x_108, 1);
x_112 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_15, x_2, x_3, x_4, x_5, x_6, x_111);
if (lean_obj_tag(x_112) == 0)
{
uint8_t x_113; 
x_113 = !lean_is_exclusive(x_112);
if (x_113 == 0)
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_112, 0);
lean_ctor_set_tag(x_108, 2);
lean_ctor_set(x_108, 1, x_114);
lean_ctor_set(x_112, 0, x_108);
return x_112;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_112, 0);
x_116 = lean_ctor_get(x_112, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_112);
lean_ctor_set_tag(x_108, 2);
lean_ctor_set(x_108, 1, x_115);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_108);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
else
{
lean_free_object(x_108);
lean_dec(x_110);
return x_112;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_108, 0);
x_119 = lean_ctor_get(x_108, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_108);
x_120 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_15, x_2, x_3, x_4, x_5, x_6, x_119);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_123 = x_120;
} else {
 lean_dec_ref(x_120);
 x_123 = lean_box(0);
}
x_124 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_124, 0, x_118);
lean_ctor_set(x_124, 1, x_121);
if (lean_is_scalar(x_123)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_123;
}
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_122);
return x_125;
}
else
{
lean_dec(x_118);
return x_120;
}
}
}
else
{
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_108;
}
}
}
}
else
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; 
lean_dec(x_94);
x_126 = l_Lean_Meta_isInstHSubInt___redArg(x_74, x_4, x_10);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_unbox(x_127);
lean_dec(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_21);
lean_dec(x_15);
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_129);
lean_dec(x_126);
x_130 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_129);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_1);
x_131 = lean_ctor_get(x_126, 1);
lean_inc(x_131);
lean_dec(x_126);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_132 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_21, x_2, x_3, x_4, x_5, x_6, x_131);
if (lean_obj_tag(x_132) == 0)
{
uint8_t x_133; 
x_133 = !lean_is_exclusive(x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_132, 0);
x_135 = lean_ctor_get(x_132, 1);
x_136 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_15, x_2, x_3, x_4, x_5, x_6, x_135);
if (lean_obj_tag(x_136) == 0)
{
uint8_t x_137; 
x_137 = !lean_is_exclusive(x_136);
if (x_137 == 0)
{
lean_object* x_138; 
x_138 = lean_ctor_get(x_136, 0);
lean_ctor_set_tag(x_132, 3);
lean_ctor_set(x_132, 1, x_138);
lean_ctor_set(x_136, 0, x_132);
return x_136;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_136, 0);
x_140 = lean_ctor_get(x_136, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_136);
lean_ctor_set_tag(x_132, 3);
lean_ctor_set(x_132, 1, x_139);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_132);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
else
{
lean_free_object(x_132);
lean_dec(x_134);
return x_136;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_132, 0);
x_143 = lean_ctor_get(x_132, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_132);
x_144 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_15, x_2, x_3, x_4, x_5, x_6, x_143);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_147 = x_144;
} else {
 lean_dec_ref(x_144);
 x_147 = lean_box(0);
}
x_148 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_148, 0, x_142);
lean_ctor_set(x_148, 1, x_145);
if (lean_is_scalar(x_147)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_147;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_146);
return x_149;
}
else
{
lean_dec(x_142);
return x_144;
}
}
}
else
{
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_132;
}
}
}
}
else
{
lean_object* x_150; lean_object* x_151; uint8_t x_152; 
lean_dec(x_94);
x_150 = l_Lean_Meta_isInstHMulInt___redArg(x_74, x_4, x_10);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_unbox(x_151);
lean_dec(x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_11);
x_153 = lean_ctor_get(x_150, 1);
lean_inc(x_153);
lean_dec(x_150);
x_154 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_153);
return x_154;
}
else
{
lean_object* x_155; 
x_155 = lean_ctor_get(x_150, 1);
lean_inc(x_155);
lean_dec(x_150);
x_22 = x_15;
x_23 = x_2;
x_24 = x_3;
x_25 = x_4;
x_26 = x_5;
x_27 = x_6;
x_28 = x_155;
goto block_64;
}
}
}
}
}
else
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; 
lean_dec(x_82);
lean_dec(x_11);
x_156 = l_Lean_Meta_isInstAddInt___redArg(x_74, x_4, x_10);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_unbox(x_157);
lean_dec(x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; 
lean_dec(x_21);
lean_dec(x_15);
x_159 = lean_ctor_get(x_156, 1);
lean_inc(x_159);
lean_dec(x_156);
x_160 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_159);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_1);
x_161 = lean_ctor_get(x_156, 1);
lean_inc(x_161);
lean_dec(x_156);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_162 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_21, x_2, x_3, x_4, x_5, x_6, x_161);
if (lean_obj_tag(x_162) == 0)
{
uint8_t x_163; 
x_163 = !lean_is_exclusive(x_162);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_162, 0);
x_165 = lean_ctor_get(x_162, 1);
x_166 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_15, x_2, x_3, x_4, x_5, x_6, x_165);
if (lean_obj_tag(x_166) == 0)
{
uint8_t x_167; 
x_167 = !lean_is_exclusive(x_166);
if (x_167 == 0)
{
lean_object* x_168; 
x_168 = lean_ctor_get(x_166, 0);
lean_ctor_set_tag(x_162, 2);
lean_ctor_set(x_162, 1, x_168);
lean_ctor_set(x_166, 0, x_162);
return x_166;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_166, 0);
x_170 = lean_ctor_get(x_166, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_166);
lean_ctor_set_tag(x_162, 2);
lean_ctor_set(x_162, 1, x_169);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_162);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
else
{
lean_free_object(x_162);
lean_dec(x_164);
return x_166;
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_162, 0);
x_173 = lean_ctor_get(x_162, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_162);
x_174 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_15, x_2, x_3, x_4, x_5, x_6, x_173);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_177 = x_174;
} else {
 lean_dec_ref(x_174);
 x_177 = lean_box(0);
}
x_178 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_178, 0, x_172);
lean_ctor_set(x_178, 1, x_175);
if (lean_is_scalar(x_177)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_177;
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_176);
return x_179;
}
else
{
lean_dec(x_172);
return x_174;
}
}
}
else
{
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_162;
}
}
}
}
else
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; 
lean_dec(x_82);
lean_dec(x_11);
x_180 = l_Lean_Meta_isInstSubInt___redArg(x_74, x_4, x_10);
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_unbox(x_181);
lean_dec(x_181);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; 
lean_dec(x_21);
lean_dec(x_15);
x_183 = lean_ctor_get(x_180, 1);
lean_inc(x_183);
lean_dec(x_180);
x_184 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_183);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; 
lean_dec(x_1);
x_185 = lean_ctor_get(x_180, 1);
lean_inc(x_185);
lean_dec(x_180);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_186 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_21, x_2, x_3, x_4, x_5, x_6, x_185);
if (lean_obj_tag(x_186) == 0)
{
uint8_t x_187; 
x_187 = !lean_is_exclusive(x_186);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_186, 0);
x_189 = lean_ctor_get(x_186, 1);
x_190 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_15, x_2, x_3, x_4, x_5, x_6, x_189);
if (lean_obj_tag(x_190) == 0)
{
uint8_t x_191; 
x_191 = !lean_is_exclusive(x_190);
if (x_191 == 0)
{
lean_object* x_192; 
x_192 = lean_ctor_get(x_190, 0);
lean_ctor_set_tag(x_186, 3);
lean_ctor_set(x_186, 1, x_192);
lean_ctor_set(x_190, 0, x_186);
return x_190;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_190, 0);
x_194 = lean_ctor_get(x_190, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_190);
lean_ctor_set_tag(x_186, 3);
lean_ctor_set(x_186, 1, x_193);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_186);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
else
{
lean_free_object(x_186);
lean_dec(x_188);
return x_190;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_186, 0);
x_197 = lean_ctor_get(x_186, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_186);
x_198 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_15, x_2, x_3, x_4, x_5, x_6, x_197);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_201 = x_198;
} else {
 lean_dec_ref(x_198);
 x_201 = lean_box(0);
}
x_202 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_202, 0, x_196);
lean_ctor_set(x_202, 1, x_199);
if (lean_is_scalar(x_201)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_201;
}
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_200);
return x_203;
}
else
{
lean_dec(x_196);
return x_198;
}
}
}
else
{
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_186;
}
}
}
}
else
{
lean_object* x_204; lean_object* x_205; uint8_t x_206; 
lean_dec(x_82);
x_204 = l_Lean_Meta_isInstMulInt___redArg(x_74, x_4, x_10);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_unbox(x_205);
lean_dec(x_205);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; 
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_11);
x_207 = lean_ctor_get(x_204, 1);
lean_inc(x_207);
lean_dec(x_204);
x_208 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_207);
return x_208;
}
else
{
lean_object* x_209; 
x_209 = lean_ctor_get(x_204, 1);
lean_inc(x_209);
lean_dec(x_204);
x_22 = x_15;
x_23 = x_2;
x_24 = x_3;
x_25 = x_4;
x_26 = x_5;
x_27 = x_6;
x_28 = x_209;
goto block_64;
}
}
}
}
else
{
lean_object* x_210; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_210 = l_Lean_Meta_getIntValue_x3f(x_1, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec(x_210);
x_213 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_212);
return x_213;
}
else
{
uint8_t x_214; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_214 = !lean_is_exclusive(x_210);
if (x_214 == 0)
{
lean_object* x_215; uint8_t x_216; 
x_215 = lean_ctor_get(x_210, 0);
lean_dec(x_215);
x_216 = !lean_is_exclusive(x_211);
if (x_216 == 0)
{
lean_ctor_set_tag(x_211, 0);
return x_210;
}
else
{
lean_object* x_217; lean_object* x_218; 
x_217 = lean_ctor_get(x_211, 0);
lean_inc(x_217);
lean_dec(x_211);
x_218 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_210, 0, x_218);
return x_210;
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_219 = lean_ctor_get(x_210, 1);
lean_inc(x_219);
lean_dec(x_210);
x_220 = lean_ctor_get(x_211, 0);
lean_inc(x_220);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 x_221 = x_211;
} else {
 lean_dec_ref(x_211);
 x_221 = lean_box(0);
}
if (lean_is_scalar(x_221)) {
 x_222 = lean_alloc_ctor(0, 1, 0);
} else {
 x_222 = x_221;
 lean_ctor_set_tag(x_222, 0);
}
lean_ctor_set(x_222, 0, x_220);
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_219);
return x_223;
}
}
}
else
{
uint8_t x_224; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_224 = !lean_is_exclusive(x_210);
if (x_224 == 0)
{
return x_210;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_210, 0);
x_226 = lean_ctor_get(x_210, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_210);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
return x_227;
}
}
}
}
else
{
lean_object* x_228; lean_object* x_229; uint8_t x_230; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_11);
x_228 = l_Lean_Meta_isInstNegInt___redArg(x_21, x_4, x_10);
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_unbox(x_229);
lean_dec(x_229);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; 
lean_dec(x_15);
x_231 = lean_ctor_get(x_228, 1);
lean_inc(x_231);
lean_dec(x_228);
x_232 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_231);
return x_232;
}
else
{
lean_object* x_233; lean_object* x_234; 
lean_dec(x_1);
x_233 = lean_ctor_get(x_228, 1);
lean_inc(x_233);
lean_dec(x_228);
x_234 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_15, x_2, x_3, x_4, x_5, x_6, x_233);
if (lean_obj_tag(x_234) == 0)
{
uint8_t x_235; 
x_235 = !lean_is_exclusive(x_234);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; 
x_236 = lean_ctor_get(x_234, 0);
x_237 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_234, 0, x_237);
return x_234;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_238 = lean_ctor_get(x_234, 0);
x_239 = lean_ctor_get(x_234, 1);
lean_inc(x_239);
lean_inc(x_238);
lean_dec(x_234);
x_240 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_240, 0, x_238);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_239);
return x_241;
}
}
else
{
return x_234;
}
}
}
}
}
else
{
lean_object* x_242; 
lean_dec(x_65);
lean_dec(x_11);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_242 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_21, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_242) == 0)
{
uint8_t x_243; 
x_243 = !lean_is_exclusive(x_242);
if (x_243 == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_242, 0);
x_245 = lean_ctor_get(x_242, 1);
x_246 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_15, x_2, x_3, x_4, x_5, x_6, x_245);
if (lean_obj_tag(x_246) == 0)
{
uint8_t x_247; 
x_247 = !lean_is_exclusive(x_246);
if (x_247 == 0)
{
lean_object* x_248; 
x_248 = lean_ctor_get(x_246, 0);
lean_ctor_set_tag(x_242, 2);
lean_ctor_set(x_242, 1, x_248);
lean_ctor_set(x_246, 0, x_242);
return x_246;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_249 = lean_ctor_get(x_246, 0);
x_250 = lean_ctor_get(x_246, 1);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_246);
lean_ctor_set_tag(x_242, 2);
lean_ctor_set(x_242, 1, x_249);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_242);
lean_ctor_set(x_251, 1, x_250);
return x_251;
}
}
else
{
lean_free_object(x_242);
lean_dec(x_244);
return x_246;
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_242, 0);
x_253 = lean_ctor_get(x_242, 1);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_242);
x_254 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_15, x_2, x_3, x_4, x_5, x_6, x_253);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_254, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_257 = x_254;
} else {
 lean_dec_ref(x_254);
 x_257 = lean_box(0);
}
x_258 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_258, 0, x_252);
lean_ctor_set(x_258, 1, x_255);
if (lean_is_scalar(x_257)) {
 x_259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_259 = x_257;
}
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_256);
return x_259;
}
else
{
lean_dec(x_252);
return x_254;
}
}
}
else
{
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_242;
}
}
}
else
{
lean_object* x_260; 
lean_dec(x_65);
lean_dec(x_11);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_260 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_21, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_260) == 0)
{
uint8_t x_261; 
x_261 = !lean_is_exclusive(x_260);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_262 = lean_ctor_get(x_260, 0);
x_263 = lean_ctor_get(x_260, 1);
x_264 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_15, x_2, x_3, x_4, x_5, x_6, x_263);
if (lean_obj_tag(x_264) == 0)
{
uint8_t x_265; 
x_265 = !lean_is_exclusive(x_264);
if (x_265 == 0)
{
lean_object* x_266; 
x_266 = lean_ctor_get(x_264, 0);
lean_ctor_set_tag(x_260, 3);
lean_ctor_set(x_260, 1, x_266);
lean_ctor_set(x_264, 0, x_260);
return x_264;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_264, 0);
x_268 = lean_ctor_get(x_264, 1);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_264);
lean_ctor_set_tag(x_260, 3);
lean_ctor_set(x_260, 1, x_267);
x_269 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_269, 0, x_260);
lean_ctor_set(x_269, 1, x_268);
return x_269;
}
}
else
{
lean_free_object(x_260);
lean_dec(x_262);
return x_264;
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_270 = lean_ctor_get(x_260, 0);
x_271 = lean_ctor_get(x_260, 1);
lean_inc(x_271);
lean_inc(x_270);
lean_dec(x_260);
x_272 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_15, x_2, x_3, x_4, x_5, x_6, x_271);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_275 = x_272;
} else {
 lean_dec_ref(x_272);
 x_275 = lean_box(0);
}
x_276 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_276, 0, x_270);
lean_ctor_set(x_276, 1, x_273);
if (lean_is_scalar(x_275)) {
 x_277 = lean_alloc_ctor(0, 2, 0);
} else {
 x_277 = x_275;
}
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_274);
return x_277;
}
else
{
lean_dec(x_270);
return x_272;
}
}
}
else
{
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_260;
}
}
}
else
{
lean_dec(x_65);
x_22 = x_15;
x_23 = x_2;
x_24 = x_3;
x_25 = x_4;
x_26 = x_5;
x_27 = x_6;
x_28 = x_10;
goto block_64;
}
block_64:
{
lean_object* x_29; 
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_21);
x_29 = l_Lean_Meta_getIntValue_x3f(x_21, x_24, x_25, x_26, x_27, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
x_32 = l_Lean_Meta_getIntValue_x3f(x_22, x_24, x_25, x_26, x_27, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_21);
lean_dec(x_11);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_23, x_24, x_25, x_26, x_27, x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_1);
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_ctor_get(x_33, 0);
lean_inc(x_37);
lean_dec(x_33);
x_38 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_21, x_23, x_24, x_25, x_26, x_27, x_36);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
if (lean_is_scalar(x_11)) {
 x_41 = lean_alloc_ctor(6, 2, 0);
} else {
 x_41 = x_11;
 lean_ctor_set_tag(x_41, 6);
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_37);
lean_ctor_set(x_38, 0, x_41);
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_38);
if (lean_is_scalar(x_11)) {
 x_44 = lean_alloc_ctor(6, 2, 0);
} else {
 x_44 = x_11;
 lean_ctor_set_tag(x_44, 6);
}
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_37);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
lean_dec(x_37);
lean_dec(x_11);
return x_38;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_32);
if (x_46 == 0)
{
return x_32;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_32, 0);
x_48 = lean_ctor_get(x_32, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_32);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_21);
lean_dec(x_1);
x_50 = lean_ctor_get(x_29, 1);
lean_inc(x_50);
lean_dec(x_29);
x_51 = lean_ctor_get(x_30, 0);
lean_inc(x_51);
lean_dec(x_30);
x_52 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_22, x_23, x_24, x_25, x_26, x_27, x_50);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_52, 0);
if (lean_is_scalar(x_11)) {
 x_55 = lean_alloc_ctor(5, 2, 0);
} else {
 x_55 = x_11;
 lean_ctor_set_tag(x_55, 5);
}
lean_ctor_set(x_55, 0, x_51);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_52, 0, x_55);
return x_52;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_52, 0);
x_57 = lean_ctor_get(x_52, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_52);
if (lean_is_scalar(x_11)) {
 x_58 = lean_alloc_ctor(5, 2, 0);
} else {
 x_58 = x_11;
 lean_ctor_set_tag(x_58, 5);
}
lean_ctor_set(x_58, 0, x_51);
lean_ctor_set(x_58, 1, x_56);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
else
{
lean_dec(x_51);
lean_dec(x_11);
return x_52;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_29);
if (x_60 == 0)
{
return x_29;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_29, 0);
x_62 = lean_ctor_get(x_29, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_29);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
}
else
{
lean_object* x_278; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_1);
x_278 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_15, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_278) == 0)
{
uint8_t x_279; 
x_279 = !lean_is_exclusive(x_278);
if (x_279 == 0)
{
lean_object* x_280; lean_object* x_281; 
x_280 = lean_ctor_get(x_278, 0);
x_281 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_278, 0, x_281);
return x_278;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_282 = lean_ctor_get(x_278, 0);
x_283 = lean_ctor_get(x_278, 1);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_278);
x_284 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_284, 0, x_282);
x_285 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_283);
return x_285;
}
}
else
{
return x_278;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
case 5:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
case 10:
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_1 = x_10;
goto _start;
}
default: 
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_18);
x_22 = l_Lean_Expr_isApp(x_21);
if (x_22 == 0)
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
x_24 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_25 = l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___closed__1;
x_26 = l_Lean_Expr_isConstOf(x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_dec(x_23);
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
lean_object* x_27; uint8_t x_28; 
lean_dec(x_11);
x_27 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_23, x_4, x_10);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
x_31 = l_Lean_Expr_cleanupAnnotations(x_29);
x_32 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12;
x_33 = l_Lean_Expr_isConstOf(x_31, x_32);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_34 = lean_box(0);
lean_ctor_set(x_27, 0, x_34);
return x_27;
}
else
{
lean_object* x_35; 
lean_free_object(x_27);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_35 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_20, x_2, x_3, x_4, x_5, x_6, x_30);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
x_39 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_17, x_2, x_3, x_4, x_5, x_6, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
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
switch (lean_obj_tag(x_37)) {
case 0:
{
if (lean_obj_tag(x_40) == 1)
{
lean_object* x_47; 
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_37);
x_47 = lean_box(0);
lean_ctor_set(x_35, 1, x_41);
lean_ctor_set(x_35, 0, x_47);
return x_35;
}
else
{
lean_free_object(x_35);
goto block_46;
}
}
case 1:
{
switch (lean_obj_tag(x_40)) {
case 0:
{
lean_object* x_48; 
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_37);
x_48 = lean_box(0);
lean_ctor_set(x_35, 1, x_41);
lean_ctor_set(x_35, 0, x_48);
return x_35;
}
case 1:
{
lean_object* x_49; 
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_37);
x_49 = lean_box(0);
lean_ctor_set(x_35, 1, x_41);
lean_ctor_set(x_35, 0, x_49);
return x_35;
}
default: 
{
lean_free_object(x_35);
goto block_46;
}
}
}
default: 
{
lean_free_object(x_35);
goto block_46;
}
}
block_46:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_40);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
if (lean_is_scalar(x_42)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_42;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_41);
return x_45;
}
}
else
{
uint8_t x_50; 
lean_free_object(x_35);
lean_dec(x_37);
x_50 = !lean_is_exclusive(x_39);
if (x_50 == 0)
{
return x_39;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_39, 0);
x_52 = lean_ctor_get(x_39, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_39);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_35, 0);
x_55 = lean_ctor_get(x_35, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_35);
x_56 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_17, x_2, x_3, x_4, x_5, x_6, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
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
switch (lean_obj_tag(x_54)) {
case 0:
{
if (lean_obj_tag(x_57) == 1)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_54);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_58);
return x_65;
}
else
{
goto block_63;
}
}
case 1:
{
switch (lean_obj_tag(x_57)) {
case 0:
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_54);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_58);
return x_67;
}
case 1:
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_54);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_58);
return x_69;
}
default: 
{
goto block_63;
}
}
}
default: 
{
goto block_63;
}
}
block_63:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_54);
lean_ctor_set(x_60, 1, x_57);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
if (lean_is_scalar(x_59)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_59;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_58);
return x_62;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_54);
x_70 = lean_ctor_get(x_56, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_56, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_72 = x_56;
} else {
 lean_dec_ref(x_56);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_74 = !lean_is_exclusive(x_35);
if (x_74 == 0)
{
return x_35;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_35, 0);
x_76 = lean_ctor_get(x_35, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_35);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_78 = lean_ctor_get(x_27, 0);
x_79 = lean_ctor_get(x_27, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_27);
x_80 = l_Lean_Expr_cleanupAnnotations(x_78);
x_81 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__12;
x_82 = l_Lean_Expr_isConstOf(x_80, x_81);
lean_dec(x_80);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_79);
return x_84;
}
else
{
lean_object* x_85; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_85 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_20, x_2, x_3, x_4, x_5, x_6, x_79);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_88 = x_85;
} else {
 lean_dec_ref(x_85);
 x_88 = lean_box(0);
}
x_89 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_17, x_2, x_3, x_4, x_5, x_6, x_87);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_92 = x_89;
} else {
 lean_dec_ref(x_89);
 x_92 = lean_box(0);
}
switch (lean_obj_tag(x_86)) {
case 0:
{
if (lean_obj_tag(x_90) == 1)
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_92);
lean_dec(x_90);
lean_dec(x_86);
x_97 = lean_box(0);
if (lean_is_scalar(x_88)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_88;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_91);
return x_98;
}
else
{
lean_dec(x_88);
goto block_96;
}
}
case 1:
{
switch (lean_obj_tag(x_90)) {
case 0:
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_92);
lean_dec(x_90);
lean_dec(x_86);
x_99 = lean_box(0);
if (lean_is_scalar(x_88)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_88;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_91);
return x_100;
}
case 1:
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_92);
lean_dec(x_90);
lean_dec(x_86);
x_101 = lean_box(0);
if (lean_is_scalar(x_88)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_88;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_91);
return x_102;
}
default: 
{
lean_dec(x_88);
goto block_96;
}
}
}
default: 
{
lean_dec(x_88);
goto block_96;
}
}
block_96:
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_86);
lean_ctor_set(x_93, 1, x_90);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
if (lean_is_scalar(x_92)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_92;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_91);
return x_95;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_88);
lean_dec(x_86);
x_103 = lean_ctor_get(x_89, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_89, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_105 = x_89;
} else {
 lean_dec_ref(x_89);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_107 = lean_ctor_get(x_85, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_85, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_109 = x_85;
} else {
 lean_dec_ref(x_85);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
x_1 = l_Int_Linear_Poly_toExpr_go___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_22 = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__1;
x_23 = l_Lean_Expr_isConstOf(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__3;
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
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
x_28 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_29 = l_Lean_Expr_isApp(x_28);
if (x_29 == 0)
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
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = l_Lean_Expr_appFnCleanup___redArg(x_28);
x_31 = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__6;
x_32 = l_Lean_Expr_isConstOf(x_30, x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__9;
x_34 = l_Lean_Expr_isConstOf(x_30, x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__11;
x_36 = l_Lean_Expr_isConstOf(x_30, x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__13;
x_38 = l_Lean_Expr_isConstOf(x_30, x_37);
lean_dec(x_30);
if (x_38 == 0)
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
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_11);
x_39 = l_Lean_Meta_isInstLEInt___redArg(x_27, x_4, x_10);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
uint8_t x_42; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_42 = !lean_is_exclusive(x_39);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_39, 0);
lean_dec(x_43);
x_44 = lean_box(0);
lean_ctor_set(x_39, 0, x_44);
return x_39;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_dec(x_39);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_39, 1);
lean_inc(x_48);
lean_dec(x_39);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_49 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_20, x_2, x_3, x_4, x_5, x_6, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_17, x_2, x_3, x_4, x_5, x_6, x_51);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_50);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_52, 0, x_56);
return x_52;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_52, 0);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_52);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_50);
lean_ctor_set(x_59, 1, x_57);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
}
else
{
uint8_t x_62; 
lean_dec(x_50);
x_62 = !lean_is_exclusive(x_52);
if (x_62 == 0)
{
return x_52;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_52, 0);
x_64 = lean_ctor_get(x_52, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_52);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_66 = !lean_is_exclusive(x_49);
if (x_66 == 0)
{
return x_49;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_49, 0);
x_68 = lean_ctor_get(x_49, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_49);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
}
else
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
lean_dec(x_30);
lean_dec(x_11);
x_70 = l_Lean_Meta_isInstLTInt___redArg(x_27, x_4, x_10);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_unbox(x_71);
lean_dec(x_71);
if (x_72 == 0)
{
uint8_t x_73; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_73 = !lean_is_exclusive(x_70);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_70, 0);
lean_dec(x_74);
x_75 = lean_box(0);
lean_ctor_set(x_70, 0, x_75);
return x_70;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_70, 1);
lean_inc(x_76);
lean_dec(x_70);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_70, 1);
lean_inc(x_79);
lean_dec(x_70);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_80 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_20, x_2, x_3, x_4, x_5, x_6, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_17, x_2, x_3, x_4, x_5, x_6, x_82);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_83, 0);
x_86 = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14;
x_87 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_87, 0, x_81);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_83, 0, x_89);
return x_83;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_90 = lean_ctor_get(x_83, 0);
x_91 = lean_ctor_get(x_83, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_83);
x_92 = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14;
x_93 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_93, 0, x_81);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_90);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_91);
return x_96;
}
}
else
{
uint8_t x_97; 
lean_dec(x_81);
x_97 = !lean_is_exclusive(x_83);
if (x_97 == 0)
{
return x_83;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_83, 0);
x_99 = lean_ctor_get(x_83, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_83);
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
x_101 = !lean_is_exclusive(x_80);
if (x_101 == 0)
{
return x_80;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_80, 0);
x_103 = lean_ctor_get(x_80, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_80);
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
lean_dec(x_30);
lean_dec(x_11);
x_105 = l_Lean_Meta_isInstLEInt___redArg(x_27, x_4, x_10);
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
x_115 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_17, x_2, x_3, x_4, x_5, x_6, x_114);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_20, x_2, x_3, x_4, x_5, x_6, x_117);
if (lean_obj_tag(x_118) == 0)
{
uint8_t x_119; 
x_119 = !lean_is_exclusive(x_118);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_118, 0);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_116);
lean_ctor_set(x_121, 1, x_120);
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
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_116);
lean_ctor_set(x_125, 1, x_123);
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
lean_dec(x_30);
lean_dec(x_11);
x_136 = l_Lean_Meta_isInstLTInt___redArg(x_27, x_4, x_10);
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
x_146 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_17, x_2, x_3, x_4, x_5, x_6, x_145);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_20, x_2, x_3, x_4, x_5, x_6, x_148);
if (lean_obj_tag(x_149) == 0)
{
uint8_t x_150; 
x_150 = !lean_is_exclusive(x_149);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_151 = lean_ctor_get(x_149, 0);
x_152 = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14;
x_153 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_153, 0, x_147);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_151);
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_149, 0, x_155);
return x_149;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_156 = lean_ctor_get(x_149, 0);
x_157 = lean_ctor_get(x_149, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_149);
x_158 = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14;
x_159 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_159, 0, x_147);
lean_ctor_set(x_159, 1, x_158);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_156);
x_161 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_161, 0, x_160);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_157);
return x_162;
}
}
else
{
uint8_t x_163; 
lean_dec(x_147);
x_163 = !lean_is_exclusive(x_149);
if (x_163 == 0)
{
return x_149;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_149, 0);
x_165 = lean_ctor_get(x_149, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_149);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
else
{
uint8_t x_167; 
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_167 = !lean_is_exclusive(x_146);
if (x_167 == 0)
{
return x_146;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_146, 0);
x_169 = lean_ctor_get(x_146, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_146);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
}
}
}
}
}
else
{
lean_object* x_171; 
lean_dec(x_21);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_171 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_20, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_17, x_2, x_3, x_4, x_5, x_6, x_173);
if (lean_obj_tag(x_174) == 0)
{
uint8_t x_175; 
x_175 = !lean_is_exclusive(x_174);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_174, 0);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_172);
lean_ctor_set(x_177, 1, x_176);
x_178 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_174, 0, x_178);
return x_174;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_179 = lean_ctor_get(x_174, 0);
x_180 = lean_ctor_get(x_174, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_174);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_172);
lean_ctor_set(x_181, 1, x_179);
x_182 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_182, 0, x_181);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_180);
return x_183;
}
}
else
{
uint8_t x_184; 
lean_dec(x_172);
x_184 = !lean_is_exclusive(x_174);
if (x_184 == 0)
{
return x_174;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_174, 0);
x_186 = lean_ctor_get(x_174, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_174);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
else
{
uint8_t x_188; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_188 = !lean_is_exclusive(x_171);
if (x_188 == 0)
{
return x_171;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_171, 0);
x_190 = lean_ctor_get(x_171, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_171);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
}
else
{
lean_object* x_192; 
lean_dec(x_21);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_192 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_20, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_17, x_2, x_3, x_4, x_5, x_6, x_194);
if (lean_obj_tag(x_195) == 0)
{
uint8_t x_196; 
x_196 = !lean_is_exclusive(x_195);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_197 = lean_ctor_get(x_195, 0);
x_198 = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14;
x_199 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_199, 0, x_193);
lean_ctor_set(x_199, 1, x_198);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_197);
x_201 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_195, 0, x_201);
return x_195;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_202 = lean_ctor_get(x_195, 0);
x_203 = lean_ctor_get(x_195, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_195);
x_204 = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___closed__14;
x_205 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_205, 0, x_193);
lean_ctor_set(x_205, 1, x_204);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_202);
x_207 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_207, 0, x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_203);
return x_208;
}
}
else
{
uint8_t x_209; 
lean_dec(x_193);
x_209 = !lean_is_exclusive(x_195);
if (x_209 == 0)
{
return x_195;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_195, 0);
x_211 = lean_ctor_get(x_195, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_195);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
}
}
else
{
uint8_t x_213; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_213 = !lean_is_exclusive(x_192);
if (x_213 == 0)
{
return x_192;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_192, 0);
x_215 = lean_ctor_get(x_192, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_192);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
return x_216;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_18);
x_22 = l_Lean_Expr_isApp(x_21);
if (x_22 == 0)
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
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
x_24 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_25 = l_Lean_Expr_isApp(x_24);
if (x_25 == 0)
{
lean_dec(x_24);
lean_dec(x_23);
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
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = l_Lean_Expr_appFnCleanup___redArg(x_24);
x_27 = l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___closed__2;
x_28 = l_Lean_Expr_isConstOf(x_26, x_27);
lean_dec(x_26);
if (x_28 == 0)
{
lean_dec(x_23);
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
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_11);
x_29 = l_Lean_Meta_isInstDvdInt___redArg(x_23, x_4, x_10);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
uint8_t x_32; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_29, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_29, 0, x_34);
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_29, 1);
lean_inc(x_38);
lean_dec(x_29);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_39 = l_Lean_Meta_getIntValue_x3f(x_20, x_3, x_4, x_5, x_6, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 0);
lean_dec(x_42);
x_43 = lean_box(0);
lean_ctor_set(x_39, 0, x_43);
return x_39;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_dec(x_39);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
lean_dec(x_39);
x_48 = !lean_is_exclusive(x_40);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_40, 0);
x_50 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_17, x_2, x_3, x_4, x_5, x_6, x_47);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_49);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_40, 0, x_53);
lean_ctor_set(x_50, 0, x_40);
return x_50;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_50, 0);
x_55 = lean_ctor_get(x_50, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_50);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_49);
lean_ctor_set(x_56, 1, x_54);
lean_ctor_set(x_40, 0, x_56);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_40);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_free_object(x_40);
lean_dec(x_49);
x_58 = !lean_is_exclusive(x_50);
if (x_58 == 0)
{
return x_50;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_50, 0);
x_60 = lean_ctor_get(x_50, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_50);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_40, 0);
lean_inc(x_62);
lean_dec(x_40);
x_63 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_17, x_2, x_3, x_4, x_5, x_6, x_47);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set(x_67, 1, x_64);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
if (lean_is_scalar(x_66)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_66;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_65);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_62);
x_70 = lean_ctor_get(x_63, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_63, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_72 = x_63;
} else {
 lean_dec_ref(x_63);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_74 = !lean_is_exclusive(x_39);
if (x_74 == 0)
{
return x_39;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_39, 0);
x_76 = lean_ctor_get(x_39, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_39);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg___closed__3;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toLinearExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr___boxed), 7, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(x_7, x_2, x_3, x_4, x_5, x_6);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_8, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_8, 0);
lean_dec(x_18);
x_19 = l_Lean_sortExprs(x_12, x_15);
lean_dec(x_12);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = l_Int_Linear_Expr_applyPerm_go(x_22, x_11);
lean_dec(x_22);
lean_ctor_set(x_19, 1, x_21);
lean_ctor_set(x_19, 0, x_23);
lean_ctor_set(x_8, 0, x_19);
return x_8;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_19);
x_26 = l_Int_Linear_Expr_applyPerm_go(x_25, x_11);
lean_dec(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_8, 0, x_27);
return x_8;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_8);
x_28 = l_Lean_sortExprs(x_12, x_15);
lean_dec(x_12);
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
x_32 = l_Int_Linear_Expr_applyPerm_go(x_30, x_11);
lean_dec(x_30);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_29);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_10);
return x_34;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_adapter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_apply_1(x_2, x_1);
x_9 = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_10);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_9, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_10);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_10, 1);
x_24 = lean_ctor_get(x_10, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
x_28 = lean_array_get_size(x_23);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_dec_le(x_28, x_29);
lean_dec(x_28);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
lean_free_object(x_10);
x_31 = l_Lean_sortExprs(x_23, x_30);
lean_dec(x_23);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
x_35 = l_Int_Linear_Expr_applyPerm_go(x_34, x_26);
x_36 = l_Int_Linear_Expr_applyPerm_go(x_34, x_27);
lean_dec(x_34);
lean_ctor_set(x_31, 1, x_33);
lean_ctor_set(x_31, 0, x_36);
lean_ctor_set(x_20, 1, x_31);
lean_ctor_set(x_20, 0, x_35);
lean_ctor_set(x_9, 0, x_11);
return x_9;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = l_Int_Linear_Expr_applyPerm_go(x_38, x_26);
x_40 = l_Int_Linear_Expr_applyPerm_go(x_38, x_27);
lean_dec(x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_37);
lean_ctor_set(x_20, 1, x_41);
lean_ctor_set(x_20, 0, x_39);
lean_ctor_set(x_9, 0, x_11);
return x_9;
}
}
else
{
lean_ctor_set(x_20, 1, x_23);
lean_ctor_set(x_20, 0, x_27);
lean_ctor_set(x_10, 1, x_20);
lean_ctor_set(x_10, 0, x_26);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_9, 0, x_11);
return x_9;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_42 = lean_ctor_get(x_20, 0);
x_43 = lean_ctor_get(x_20, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_20);
x_44 = lean_array_get_size(x_23);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_dec_le(x_44, x_45);
lean_dec(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_free_object(x_10);
x_47 = l_Lean_sortExprs(x_23, x_46);
lean_dec(x_23);
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
x_51 = l_Int_Linear_Expr_applyPerm_go(x_49, x_42);
x_52 = l_Int_Linear_Expr_applyPerm_go(x_49, x_43);
lean_dec(x_49);
if (lean_is_scalar(x_50)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_50;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_48);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_11, 0, x_54);
lean_ctor_set(x_9, 0, x_11);
return x_9;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_43);
lean_ctor_set(x_55, 1, x_23);
lean_ctor_set(x_10, 1, x_55);
lean_ctor_set(x_10, 0, x_42);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_9, 0, x_11);
return x_9;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_56 = lean_ctor_get(x_10, 1);
lean_inc(x_56);
lean_dec(x_10);
x_57 = lean_ctor_get(x_20, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_20, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_59 = x_20;
} else {
 lean_dec_ref(x_20);
 x_59 = lean_box(0);
}
x_60 = lean_array_get_size(x_56);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_dec_le(x_60, x_61);
lean_dec(x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_63 = l_Lean_sortExprs(x_56, x_62);
lean_dec(x_56);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
x_67 = l_Int_Linear_Expr_applyPerm_go(x_65, x_57);
x_68 = l_Int_Linear_Expr_applyPerm_go(x_65, x_58);
lean_dec(x_65);
if (lean_is_scalar(x_66)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_66;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_64);
if (lean_is_scalar(x_59)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_59;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set(x_11, 0, x_70);
lean_ctor_set(x_9, 0, x_11);
return x_9;
}
else
{
lean_object* x_71; lean_object* x_72; 
if (lean_is_scalar(x_59)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_59;
}
lean_ctor_set(x_71, 0, x_58);
lean_ctor_set(x_71, 1, x_56);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_57);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_11, 0, x_72);
lean_ctor_set(x_9, 0, x_11);
return x_9;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_73 = lean_ctor_get(x_11, 0);
x_74 = lean_ctor_get(x_9, 1);
lean_inc(x_74);
lean_dec(x_9);
x_75 = lean_ctor_get(x_10, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_76 = x_10;
} else {
 lean_dec_ref(x_10);
 x_76 = lean_box(0);
}
x_77 = lean_ctor_get(x_73, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_79 = x_73;
} else {
 lean_dec_ref(x_73);
 x_79 = lean_box(0);
}
x_80 = lean_array_get_size(x_75);
x_81 = lean_unsigned_to_nat(1u);
x_82 = lean_nat_dec_le(x_80, x_81);
lean_dec(x_80);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_76);
x_83 = l_Lean_sortExprs(x_75, x_82);
lean_dec(x_75);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_86 = x_83;
} else {
 lean_dec_ref(x_83);
 x_86 = lean_box(0);
}
x_87 = l_Int_Linear_Expr_applyPerm_go(x_85, x_77);
x_88 = l_Int_Linear_Expr_applyPerm_go(x_85, x_78);
lean_dec(x_85);
if (lean_is_scalar(x_86)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_86;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_84);
if (lean_is_scalar(x_79)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_79;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set(x_11, 0, x_90);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_11);
lean_ctor_set(x_91, 1, x_74);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
if (lean_is_scalar(x_79)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_79;
}
lean_ctor_set(x_92, 0, x_78);
lean_ctor_set(x_92, 1, x_75);
if (lean_is_scalar(x_76)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_76;
}
lean_ctor_set(x_93, 0, x_77);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set(x_11, 0, x_93);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_11);
lean_ctor_set(x_94, 1, x_74);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_95 = lean_ctor_get(x_11, 0);
lean_inc(x_95);
lean_dec(x_11);
x_96 = lean_ctor_get(x_9, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_97 = x_9;
} else {
 lean_dec_ref(x_9);
 x_97 = lean_box(0);
}
x_98 = lean_ctor_get(x_10, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_99 = x_10;
} else {
 lean_dec_ref(x_10);
 x_99 = lean_box(0);
}
x_100 = lean_ctor_get(x_95, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_95, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_102 = x_95;
} else {
 lean_dec_ref(x_95);
 x_102 = lean_box(0);
}
x_103 = lean_array_get_size(x_98);
x_104 = lean_unsigned_to_nat(1u);
x_105 = lean_nat_dec_le(x_103, x_104);
lean_dec(x_103);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_99);
x_106 = l_Lean_sortExprs(x_98, x_105);
lean_dec(x_98);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_109 = x_106;
} else {
 lean_dec_ref(x_106);
 x_109 = lean_box(0);
}
x_110 = l_Int_Linear_Expr_applyPerm_go(x_108, x_100);
x_111 = l_Int_Linear_Expr_applyPerm_go(x_108, x_101);
lean_dec(x_108);
if (lean_is_scalar(x_109)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_109;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_107);
if (lean_is_scalar(x_102)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_102;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_113);
if (lean_is_scalar(x_97)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_97;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_96);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
if (lean_is_scalar(x_102)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_102;
}
lean_ctor_set(x_116, 0, x_101);
lean_ctor_set(x_116, 1, x_98);
if (lean_is_scalar(x_99)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_99;
}
lean_ctor_set(x_117, 0, x_100);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_117);
if (lean_is_scalar(x_97)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_97;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_96);
return x_119;
}
}
}
}
else
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_9);
if (x_120 == 0)
{
return x_9;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_9, 0);
x_122 = lean_ctor_get(x_9, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_9);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___boxed), 7, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(x_7, x_2, x_3, x_4, x_5, x_6);
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
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_8);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_8, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_9);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_9, 1);
x_23 = lean_ctor_get(x_9, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
x_27 = lean_array_get_size(x_22);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_dec_le(x_27, x_28);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
lean_free_object(x_9);
x_30 = l_Lean_sortExprs(x_22, x_29);
lean_dec(x_22);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
x_34 = l_Int_Linear_Expr_applyPerm_go(x_33, x_25);
x_35 = l_Int_Linear_Expr_applyPerm_go(x_33, x_26);
lean_dec(x_33);
lean_ctor_set(x_30, 1, x_32);
lean_ctor_set(x_30, 0, x_35);
lean_ctor_set(x_19, 1, x_30);
lean_ctor_set(x_19, 0, x_34);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = l_Int_Linear_Expr_applyPerm_go(x_37, x_25);
x_39 = l_Int_Linear_Expr_applyPerm_go(x_37, x_26);
lean_dec(x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_36);
lean_ctor_set(x_19, 1, x_40);
lean_ctor_set(x_19, 0, x_38);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
}
else
{
lean_ctor_set(x_19, 1, x_22);
lean_ctor_set(x_19, 0, x_26);
lean_ctor_set(x_9, 1, x_19);
lean_ctor_set(x_9, 0, x_25);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_19, 0);
x_42 = lean_ctor_get(x_19, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_19);
x_43 = lean_array_get_size(x_22);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_dec_le(x_43, x_44);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_free_object(x_9);
x_46 = l_Lean_sortExprs(x_22, x_45);
lean_dec(x_22);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_50 = l_Int_Linear_Expr_applyPerm_go(x_48, x_41);
x_51 = l_Int_Linear_Expr_applyPerm_go(x_48, x_42);
lean_dec(x_48);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_47);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_10, 0, x_53);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_42);
lean_ctor_set(x_54, 1, x_22);
lean_ctor_set(x_9, 1, x_54);
lean_ctor_set(x_9, 0, x_41);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_55 = lean_ctor_get(x_9, 1);
lean_inc(x_55);
lean_dec(x_9);
x_56 = lean_ctor_get(x_19, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_19, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_58 = x_19;
} else {
 lean_dec_ref(x_19);
 x_58 = lean_box(0);
}
x_59 = lean_array_get_size(x_55);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_dec_le(x_59, x_60);
lean_dec(x_59);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_62 = l_Lean_sortExprs(x_55, x_61);
lean_dec(x_55);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = l_Int_Linear_Expr_applyPerm_go(x_64, x_56);
x_67 = l_Int_Linear_Expr_applyPerm_go(x_64, x_57);
lean_dec(x_64);
if (lean_is_scalar(x_65)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_65;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_63);
if (lean_is_scalar(x_58)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_58;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set(x_10, 0, x_69);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
else
{
lean_object* x_70; lean_object* x_71; 
if (lean_is_scalar(x_58)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_58;
}
lean_ctor_set(x_70, 0, x_57);
lean_ctor_set(x_70, 1, x_55);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_56);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_10, 0, x_71);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_72 = lean_ctor_get(x_10, 0);
x_73 = lean_ctor_get(x_8, 1);
lean_inc(x_73);
lean_dec(x_8);
x_74 = lean_ctor_get(x_9, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_75 = x_9;
} else {
 lean_dec_ref(x_9);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get(x_72, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_78 = x_72;
} else {
 lean_dec_ref(x_72);
 x_78 = lean_box(0);
}
x_79 = lean_array_get_size(x_74);
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_nat_dec_le(x_79, x_80);
lean_dec(x_79);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_75);
x_82 = l_Lean_sortExprs(x_74, x_81);
lean_dec(x_74);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_85 = x_82;
} else {
 lean_dec_ref(x_82);
 x_85 = lean_box(0);
}
x_86 = l_Int_Linear_Expr_applyPerm_go(x_84, x_76);
x_87 = l_Int_Linear_Expr_applyPerm_go(x_84, x_77);
lean_dec(x_84);
if (lean_is_scalar(x_85)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_85;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_83);
if (lean_is_scalar(x_78)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_78;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_10, 0, x_89);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_10);
lean_ctor_set(x_90, 1, x_73);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
if (lean_is_scalar(x_78)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_78;
}
lean_ctor_set(x_91, 0, x_77);
lean_ctor_set(x_91, 1, x_74);
if (lean_is_scalar(x_75)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_75;
}
lean_ctor_set(x_92, 0, x_76);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set(x_10, 0, x_92);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_10);
lean_ctor_set(x_93, 1, x_73);
return x_93;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_94 = lean_ctor_get(x_10, 0);
lean_inc(x_94);
lean_dec(x_10);
x_95 = lean_ctor_get(x_8, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_96 = x_8;
} else {
 lean_dec_ref(x_8);
 x_96 = lean_box(0);
}
x_97 = lean_ctor_get(x_9, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_98 = x_9;
} else {
 lean_dec_ref(x_9);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_94, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_94, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_101 = x_94;
} else {
 lean_dec_ref(x_94);
 x_101 = lean_box(0);
}
x_102 = lean_array_get_size(x_97);
x_103 = lean_unsigned_to_nat(1u);
x_104 = lean_nat_dec_le(x_102, x_103);
lean_dec(x_102);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_98);
x_105 = l_Lean_sortExprs(x_97, x_104);
lean_dec(x_97);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_108 = x_105;
} else {
 lean_dec_ref(x_105);
 x_108 = lean_box(0);
}
x_109 = l_Int_Linear_Expr_applyPerm_go(x_107, x_99);
x_110 = l_Int_Linear_Expr_applyPerm_go(x_107, x_100);
lean_dec(x_107);
if (lean_is_scalar(x_108)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_108;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_106);
if (lean_is_scalar(x_101)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_101;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_112);
if (lean_is_scalar(x_96)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_96;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_95);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
if (lean_is_scalar(x_101)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_101;
}
lean_ctor_set(x_115, 0, x_100);
lean_ctor_set(x_115, 1, x_97);
if (lean_is_scalar(x_98)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_98;
}
lean_ctor_set(x_116, 0, x_99);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_116);
if (lean_is_scalar(x_96)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_96;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_95);
return x_118;
}
}
}
}
else
{
uint8_t x_119; 
x_119 = !lean_is_exclusive(x_8);
if (x_119 == 0)
{
return x_8;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_8, 0);
x_121 = lean_ctor_get(x_8, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_8);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___boxed), 7, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(x_7, x_2, x_3, x_4, x_5, x_6);
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
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_8);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_8, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_9);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_9, 1);
x_23 = lean_ctor_get(x_9, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
x_27 = lean_array_get_size(x_22);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_dec_le(x_27, x_28);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
lean_free_object(x_9);
x_30 = l_Lean_sortExprs(x_22, x_29);
lean_dec(x_22);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
x_34 = l_Int_Linear_Expr_applyPerm_go(x_33, x_25);
x_35 = l_Int_Linear_Expr_applyPerm_go(x_33, x_26);
lean_dec(x_33);
lean_ctor_set(x_30, 1, x_32);
lean_ctor_set(x_30, 0, x_35);
lean_ctor_set(x_19, 1, x_30);
lean_ctor_set(x_19, 0, x_34);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = l_Int_Linear_Expr_applyPerm_go(x_37, x_25);
x_39 = l_Int_Linear_Expr_applyPerm_go(x_37, x_26);
lean_dec(x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_36);
lean_ctor_set(x_19, 1, x_40);
lean_ctor_set(x_19, 0, x_38);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
}
else
{
lean_ctor_set(x_19, 1, x_22);
lean_ctor_set(x_19, 0, x_26);
lean_ctor_set(x_9, 1, x_19);
lean_ctor_set(x_9, 0, x_25);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_19, 0);
x_42 = lean_ctor_get(x_19, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_19);
x_43 = lean_array_get_size(x_22);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_dec_le(x_43, x_44);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_free_object(x_9);
x_46 = l_Lean_sortExprs(x_22, x_45);
lean_dec(x_22);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_50 = l_Int_Linear_Expr_applyPerm_go(x_48, x_41);
x_51 = l_Int_Linear_Expr_applyPerm_go(x_48, x_42);
lean_dec(x_48);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_47);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_10, 0, x_53);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_42);
lean_ctor_set(x_54, 1, x_22);
lean_ctor_set(x_9, 1, x_54);
lean_ctor_set(x_9, 0, x_41);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_55 = lean_ctor_get(x_9, 1);
lean_inc(x_55);
lean_dec(x_9);
x_56 = lean_ctor_get(x_19, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_19, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_58 = x_19;
} else {
 lean_dec_ref(x_19);
 x_58 = lean_box(0);
}
x_59 = lean_array_get_size(x_55);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_dec_le(x_59, x_60);
lean_dec(x_59);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_62 = l_Lean_sortExprs(x_55, x_61);
lean_dec(x_55);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = l_Int_Linear_Expr_applyPerm_go(x_64, x_56);
x_67 = l_Int_Linear_Expr_applyPerm_go(x_64, x_57);
lean_dec(x_64);
if (lean_is_scalar(x_65)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_65;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_63);
if (lean_is_scalar(x_58)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_58;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set(x_10, 0, x_69);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
else
{
lean_object* x_70; lean_object* x_71; 
if (lean_is_scalar(x_58)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_58;
}
lean_ctor_set(x_70, 0, x_57);
lean_ctor_set(x_70, 1, x_55);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_56);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_10, 0, x_71);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_72 = lean_ctor_get(x_10, 0);
x_73 = lean_ctor_get(x_8, 1);
lean_inc(x_73);
lean_dec(x_8);
x_74 = lean_ctor_get(x_9, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_75 = x_9;
} else {
 lean_dec_ref(x_9);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get(x_72, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_78 = x_72;
} else {
 lean_dec_ref(x_72);
 x_78 = lean_box(0);
}
x_79 = lean_array_get_size(x_74);
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_nat_dec_le(x_79, x_80);
lean_dec(x_79);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_75);
x_82 = l_Lean_sortExprs(x_74, x_81);
lean_dec(x_74);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_85 = x_82;
} else {
 lean_dec_ref(x_82);
 x_85 = lean_box(0);
}
x_86 = l_Int_Linear_Expr_applyPerm_go(x_84, x_76);
x_87 = l_Int_Linear_Expr_applyPerm_go(x_84, x_77);
lean_dec(x_84);
if (lean_is_scalar(x_85)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_85;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_83);
if (lean_is_scalar(x_78)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_78;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_10, 0, x_89);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_10);
lean_ctor_set(x_90, 1, x_73);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
if (lean_is_scalar(x_78)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_78;
}
lean_ctor_set(x_91, 0, x_77);
lean_ctor_set(x_91, 1, x_74);
if (lean_is_scalar(x_75)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_75;
}
lean_ctor_set(x_92, 0, x_76);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set(x_10, 0, x_92);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_10);
lean_ctor_set(x_93, 1, x_73);
return x_93;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_94 = lean_ctor_get(x_10, 0);
lean_inc(x_94);
lean_dec(x_10);
x_95 = lean_ctor_get(x_8, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_96 = x_8;
} else {
 lean_dec_ref(x_8);
 x_96 = lean_box(0);
}
x_97 = lean_ctor_get(x_9, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_98 = x_9;
} else {
 lean_dec_ref(x_9);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_94, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_94, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_101 = x_94;
} else {
 lean_dec_ref(x_94);
 x_101 = lean_box(0);
}
x_102 = lean_array_get_size(x_97);
x_103 = lean_unsigned_to_nat(1u);
x_104 = lean_nat_dec_le(x_102, x_103);
lean_dec(x_102);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_98);
x_105 = l_Lean_sortExprs(x_97, x_104);
lean_dec(x_97);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_108 = x_105;
} else {
 lean_dec_ref(x_105);
 x_108 = lean_box(0);
}
x_109 = l_Int_Linear_Expr_applyPerm_go(x_107, x_99);
x_110 = l_Int_Linear_Expr_applyPerm_go(x_107, x_100);
lean_dec(x_107);
if (lean_is_scalar(x_108)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_108;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_106);
if (lean_is_scalar(x_101)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_101;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_112);
if (lean_is_scalar(x_96)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_96;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_95);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
if (lean_is_scalar(x_101)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_101;
}
lean_ctor_set(x_115, 0, x_100);
lean_ctor_set(x_115, 1, x_97);
if (lean_is_scalar(x_98)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_98;
}
lean_ctor_set(x_116, 0, x_99);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_116);
if (lean_is_scalar(x_96)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_96;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_95);
return x_118;
}
}
}
}
else
{
uint8_t x_119; 
x_119 = !lean_is_exclusive(x_8);
if (x_119 == 0)
{
return x_8;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_8, 0);
x_121 = lean_ctor_get(x_8, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_8);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___boxed), 7, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(x_7, x_2, x_3, x_4, x_5, x_6);
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
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_8);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_8, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_9);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_9, 1);
x_23 = lean_ctor_get(x_9, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
x_27 = lean_array_get_size(x_22);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_dec_le(x_27, x_28);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
lean_free_object(x_9);
x_30 = l_Lean_sortExprs(x_22, x_29);
lean_dec(x_22);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
x_34 = l_Int_Linear_Expr_applyPerm_go(x_33, x_26);
lean_dec(x_33);
lean_ctor_set(x_30, 1, x_32);
lean_ctor_set(x_30, 0, x_34);
lean_ctor_set(x_19, 1, x_30);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_30, 0);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_30);
x_37 = l_Int_Linear_Expr_applyPerm_go(x_36, x_26);
lean_dec(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
lean_ctor_set(x_19, 1, x_38);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
}
else
{
lean_ctor_set(x_19, 1, x_22);
lean_ctor_set(x_19, 0, x_26);
lean_ctor_set(x_9, 1, x_19);
lean_ctor_set(x_9, 0, x_25);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_39 = lean_ctor_get(x_19, 0);
x_40 = lean_ctor_get(x_19, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_19);
x_41 = lean_array_get_size(x_22);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_dec_le(x_41, x_42);
lean_dec(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_free_object(x_9);
x_44 = l_Lean_sortExprs(x_22, x_43);
lean_dec(x_22);
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
x_48 = l_Int_Linear_Expr_applyPerm_go(x_46, x_40);
lean_dec(x_46);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_39);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_10, 0, x_50);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_40);
lean_ctor_set(x_51, 1, x_22);
lean_ctor_set(x_9, 1, x_51);
lean_ctor_set(x_9, 0, x_39);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_52 = lean_ctor_get(x_9, 1);
lean_inc(x_52);
lean_dec(x_9);
x_53 = lean_ctor_get(x_19, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_19, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_55 = x_19;
} else {
 lean_dec_ref(x_19);
 x_55 = lean_box(0);
}
x_56 = lean_array_get_size(x_52);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_dec_le(x_56, x_57);
lean_dec(x_56);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_59 = l_Lean_sortExprs(x_52, x_58);
lean_dec(x_52);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_62 = x_59;
} else {
 lean_dec_ref(x_59);
 x_62 = lean_box(0);
}
x_63 = l_Int_Linear_Expr_applyPerm_go(x_61, x_54);
lean_dec(x_61);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_60);
if (lean_is_scalar(x_55)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_55;
}
lean_ctor_set(x_65, 0, x_53);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_10, 0, x_65);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
else
{
lean_object* x_66; lean_object* x_67; 
if (lean_is_scalar(x_55)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_55;
}
lean_ctor_set(x_66, 0, x_54);
lean_ctor_set(x_66, 1, x_52);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_53);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_10, 0, x_67);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_68 = lean_ctor_get(x_10, 0);
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
x_72 = lean_ctor_get(x_68, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_68, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_74 = x_68;
} else {
 lean_dec_ref(x_68);
 x_74 = lean_box(0);
}
x_75 = lean_array_get_size(x_70);
x_76 = lean_unsigned_to_nat(1u);
x_77 = lean_nat_dec_le(x_75, x_76);
lean_dec(x_75);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_71);
x_78 = l_Lean_sortExprs(x_70, x_77);
lean_dec(x_70);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_81 = x_78;
} else {
 lean_dec_ref(x_78);
 x_81 = lean_box(0);
}
x_82 = l_Int_Linear_Expr_applyPerm_go(x_80, x_73);
lean_dec(x_80);
if (lean_is_scalar(x_81)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_81;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_79);
if (lean_is_scalar(x_74)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_74;
}
lean_ctor_set(x_84, 0, x_72);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set(x_10, 0, x_84);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_10);
lean_ctor_set(x_85, 1, x_69);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
if (lean_is_scalar(x_74)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_74;
}
lean_ctor_set(x_86, 0, x_73);
lean_ctor_set(x_86, 1, x_70);
if (lean_is_scalar(x_71)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_71;
}
lean_ctor_set(x_87, 0, x_72);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set(x_10, 0, x_87);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_10);
lean_ctor_set(x_88, 1, x_69);
return x_88;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_89 = lean_ctor_get(x_10, 0);
lean_inc(x_89);
lean_dec(x_10);
x_90 = lean_ctor_get(x_8, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_91 = x_8;
} else {
 lean_dec_ref(x_8);
 x_91 = lean_box(0);
}
x_92 = lean_ctor_get(x_9, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_93 = x_9;
} else {
 lean_dec_ref(x_9);
 x_93 = lean_box(0);
}
x_94 = lean_ctor_get(x_89, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_89, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_96 = x_89;
} else {
 lean_dec_ref(x_89);
 x_96 = lean_box(0);
}
x_97 = lean_array_get_size(x_92);
x_98 = lean_unsigned_to_nat(1u);
x_99 = lean_nat_dec_le(x_97, x_98);
lean_dec(x_97);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
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
x_104 = l_Int_Linear_Expr_applyPerm_go(x_102, x_95);
lean_dec(x_102);
if (lean_is_scalar(x_103)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_103;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_101);
if (lean_is_scalar(x_96)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_96;
}
lean_ctor_set(x_106, 0, x_94);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
if (lean_is_scalar(x_91)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_91;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_90);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
if (lean_is_scalar(x_96)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_96;
}
lean_ctor_set(x_109, 0, x_95);
lean_ctor_set(x_109, 1, x_92);
if (lean_is_scalar(x_93)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_93;
}
lean_ctor_set(x_110, 0, x_94);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
if (lean_is_scalar(x_91)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_91;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_90);
return x_112;
}
}
}
}
else
{
uint8_t x_113; 
x_113 = !lean_is_exclusive(x_8);
if (x_113 == 0)
{
return x_8;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_8, 0);
x_115 = lean_ctor_get(x_8, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_8);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Int_Linear_Poly_toExpr_go___closed__1;
x_2 = l_Lean_mkIntLit(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_toContextExpr___lam__0___boxed), 1, 0);
x_11 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13;
x_12 = l_Lean_Meta_Simp_Arith_Int_toContextExpr___closed__1;
x_13 = l_Lean_RArray_toExpr___redArg(x_11, x_10, x_12, x_2, x_3, x_4, x_5, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_toContextExpr___lam__0___boxed), 1, 0);
x_15 = l_Lean_Meta_Simp_Arith_Int_ofPoly___closed__13;
x_16 = l_Lean_RArray_ofArray___redArg(x_1);
x_17 = l_Lean_RArray_toExpr___redArg(x_15, x_14, x_16, x_2, x_3, x_4, x_5, x_6);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_Arith_Int_toContextExpr___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_Data_Int_Linear(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_SortExprs(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Check(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Offset(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_IntInstTesters(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_KExprMap(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_RArray(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Int_Linear(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_SortExprs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Check(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Offset(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_IntInstTesters(builtin, lean_io_mk_world());
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
l_Int_Linear_Poly_toExpr_go___closed__0 = _init_l_Int_Linear_Poly_toExpr_go___closed__0();
lean_mark_persistent(l_Int_Linear_Poly_toExpr_go___closed__0);
l_Int_Linear_Poly_toExpr_go___closed__1 = _init_l_Int_Linear_Poly_toExpr_go___closed__1();
lean_mark_persistent(l_Int_Linear_Poly_toExpr_go___closed__1);
l_Int_Linear_reprPoly___closed__0____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_ = _init_l_Int_Linear_reprPoly___closed__0____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_();
lean_mark_persistent(l_Int_Linear_reprPoly___closed__0____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_);
l_Int_Linear_reprPoly___closed__1____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_ = _init_l_Int_Linear_reprPoly___closed__1____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_();
lean_mark_persistent(l_Int_Linear_reprPoly___closed__1____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_);
l_Int_Linear_reprPoly___closed__2____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_ = _init_l_Int_Linear_reprPoly___closed__2____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_();
lean_mark_persistent(l_Int_Linear_reprPoly___closed__2____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_);
l_Int_Linear_reprPoly___closed__3____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_ = _init_l_Int_Linear_reprPoly___closed__3____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_();
lean_mark_persistent(l_Int_Linear_reprPoly___closed__3____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_);
l_Int_Linear_reprPoly___closed__4____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_ = _init_l_Int_Linear_reprPoly___closed__4____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_();
lean_mark_persistent(l_Int_Linear_reprPoly___closed__4____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_);
l_Int_Linear_reprPoly___closed__5____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_ = _init_l_Int_Linear_reprPoly___closed__5____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_();
lean_mark_persistent(l_Int_Linear_reprPoly___closed__5____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_);
l_Int_Linear_reprPoly___closed__6____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_ = _init_l_Int_Linear_reprPoly___closed__6____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_();
lean_mark_persistent(l_Int_Linear_reprPoly___closed__6____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_);
l_Int_Linear_instReprPoly__lean___closed__0 = _init_l_Int_Linear_instReprPoly__lean___closed__0();
lean_mark_persistent(l_Int_Linear_instReprPoly__lean___closed__0);
l_Int_Linear_instReprPoly__lean = _init_l_Int_Linear_instReprPoly__lean();
lean_mark_persistent(l_Int_Linear_instReprPoly__lean);
l_Int_Linear_reprExpr___closed__0____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_ = _init_l_Int_Linear_reprExpr___closed__0____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_();
lean_mark_persistent(l_Int_Linear_reprExpr___closed__0____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_);
l_Int_Linear_reprExpr___closed__1____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_ = _init_l_Int_Linear_reprExpr___closed__1____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_();
lean_mark_persistent(l_Int_Linear_reprExpr___closed__1____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_);
l_Int_Linear_reprExpr___closed__2____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_ = _init_l_Int_Linear_reprExpr___closed__2____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_();
lean_mark_persistent(l_Int_Linear_reprExpr___closed__2____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_);
l_Int_Linear_reprExpr___closed__3____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_ = _init_l_Int_Linear_reprExpr___closed__3____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_();
lean_mark_persistent(l_Int_Linear_reprExpr___closed__3____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_);
l_Int_Linear_reprExpr___closed__4____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_ = _init_l_Int_Linear_reprExpr___closed__4____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_();
lean_mark_persistent(l_Int_Linear_reprExpr___closed__4____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_);
l_Int_Linear_reprExpr___closed__5____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_ = _init_l_Int_Linear_reprExpr___closed__5____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_();
lean_mark_persistent(l_Int_Linear_reprExpr___closed__5____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_);
l_Int_Linear_reprExpr___closed__6____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_ = _init_l_Int_Linear_reprExpr___closed__6____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_();
lean_mark_persistent(l_Int_Linear_reprExpr___closed__6____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_);
l_Int_Linear_reprExpr___closed__7____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_ = _init_l_Int_Linear_reprExpr___closed__7____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_();
lean_mark_persistent(l_Int_Linear_reprExpr___closed__7____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_);
l_Int_Linear_reprExpr___closed__8____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_ = _init_l_Int_Linear_reprExpr___closed__8____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_();
lean_mark_persistent(l_Int_Linear_reprExpr___closed__8____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_);
l_Int_Linear_reprExpr___closed__9____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_ = _init_l_Int_Linear_reprExpr___closed__9____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_();
lean_mark_persistent(l_Int_Linear_reprExpr___closed__9____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_);
l_Int_Linear_reprExpr___closed__10____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_ = _init_l_Int_Linear_reprExpr___closed__10____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_();
lean_mark_persistent(l_Int_Linear_reprExpr___closed__10____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_);
l_Int_Linear_reprExpr___closed__11____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_ = _init_l_Int_Linear_reprExpr___closed__11____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_();
lean_mark_persistent(l_Int_Linear_reprExpr___closed__11____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_);
l_Int_Linear_reprExpr___closed__12____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_ = _init_l_Int_Linear_reprExpr___closed__12____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_();
lean_mark_persistent(l_Int_Linear_reprExpr___closed__12____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_);
l_Int_Linear_reprExpr___closed__13____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_ = _init_l_Int_Linear_reprExpr___closed__13____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_();
lean_mark_persistent(l_Int_Linear_reprExpr___closed__13____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_);
l_Int_Linear_reprExpr___closed__14____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_ = _init_l_Int_Linear_reprExpr___closed__14____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_();
lean_mark_persistent(l_Int_Linear_reprExpr___closed__14____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_);
l_Int_Linear_reprExpr___closed__15____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_ = _init_l_Int_Linear_reprExpr___closed__15____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_();
lean_mark_persistent(l_Int_Linear_reprExpr___closed__15____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_);
l_Int_Linear_reprExpr___closed__16____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_ = _init_l_Int_Linear_reprExpr___closed__16____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_();
lean_mark_persistent(l_Int_Linear_reprExpr___closed__16____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_);
l_Int_Linear_reprExpr___closed__17____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_ = _init_l_Int_Linear_reprExpr___closed__17____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_();
lean_mark_persistent(l_Int_Linear_reprExpr___closed__17____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_);
l_Int_Linear_reprExpr___closed__18____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_ = _init_l_Int_Linear_reprExpr___closed__18____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_();
lean_mark_persistent(l_Int_Linear_reprExpr___closed__18____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_);
l_Int_Linear_reprExpr___closed__19____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_ = _init_l_Int_Linear_reprExpr___closed__19____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_();
lean_mark_persistent(l_Int_Linear_reprExpr___closed__19____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_);
l_Int_Linear_reprExpr___closed__20____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_ = _init_l_Int_Linear_reprExpr___closed__20____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_();
lean_mark_persistent(l_Int_Linear_reprExpr___closed__20____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_);
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
l_Lean_Meta_Simp_Arith_Int_instToExprExpr = _init_l_Lean_Meta_Simp_Arith_Int_instToExprExpr();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_instToExprExpr);
l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__0 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__0();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__0);
l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__1 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__1);
l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__2 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__2);
l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__3 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__3);
l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__4 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__4);
l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__5 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__5);
l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__6 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__6);
l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__7 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__7();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__7);
l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__8 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__8();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__8);
l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__9 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__9();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__9);
l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__10 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__10();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__10);
l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__11 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__11();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__11);
l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__12 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__12();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__12);
l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__13 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__13();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__13);
l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__14 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__14();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__14);
l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__15 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__15();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__15);
l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__16 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__16();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__16);
l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__17 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__17();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__17);
l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__18 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__18();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__18);
l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__19 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__19();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__19);
l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__20 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__20();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__20);
l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__21 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__21();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__21);
l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__22 = _init_l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__22();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___closed__22);
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
