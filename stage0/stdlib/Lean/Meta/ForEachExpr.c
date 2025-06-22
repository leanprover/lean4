// Lean compiler output
// Module: Lean.Meta.ForEachExpr
// Imports: Lean.Expr Lean.Util.MonadCache Lean.Meta.Basic
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
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda_visit___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_visitLambda___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_setMVarUserNamesAt___closed__0;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Meta_mkForallFVars_x27_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_setMVarUserNamesAt_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_setMVarUserNamesAt_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_visitLambda_visit___at___Lean_Meta_visitLambda___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__7_spec__7_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_resetMVarUserNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars_x27___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5___lam__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_setMVarUserNamesAt_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_resetMVarUserNames_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet_visit___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet_visit___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Meta_visitLet_visit___at___Lean_Meta_visitLet___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__12_spec__12_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall_visit___at___Lean_Meta_visitForall___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__10_spec__10___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_resetMVarUserNames_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___Lean_Meta_setMVarUserNamesAt_spec__1(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_instMonadControlTOfMonadControl___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_modifyGetUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_setMVarUserNamesAt_spec__3_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall_visit___at___Lean_Meta_visitForall___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__10_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_forEachExpr_x27___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkForallFVars_x27_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Meta_visitLet_visit___at___Lean_Meta_visitLet___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__12_spec__12_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_setMVarUserNamesAt_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_setMVarUserNamesAt___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkForallFVars_x27_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_setMVarUserNamesAt___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet_visit___at___Lean_Meta_visitLet___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__12_spec__12___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_forEachExpr_x27___redArg___closed__0;
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_resetMVarUserNames_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_forEachExpr_x27___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__5___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars_x27___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_setMVarUserNamesAt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall_visit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda_visit___at___Lean_Meta_visitLambda___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__7_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_forEachExpr_x27_visit___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_resetMVarUserNames_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_visitLambda_visit___at___Lean_Meta_visitLambda___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__7_spec__7_spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Array_contains___at___Lean_Meta_setMVarUserNamesAt_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg___lam__0(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_resetMVarUserNames___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___at___Lean_Meta_mkForallFVars_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_setMVarUserNamesAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_visitLambda_visit___at___Lean_Meta_visitLambda___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__7_spec__7_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_setMVarUserNamesAt_spec__3_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_forEachExpr_x27___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_setMVarUserNamesAt_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_visitLambda_visit___at___Lean_Meta_visitLambda___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__7_spec__7_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet_visit___at___Lean_Meta_visitLet___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__12_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Meta_visitLet_visit___at___Lean_Meta_visitLet___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__12_spec__12_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__1___redArg(lean_object*);
lean_object* l_instMonadControlReaderT(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_forEachExpr_x27___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda_visit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_setMVarUserNamesAt_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___Lean_Meta_setMVarUserNamesAt_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet_visit___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet_visit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_forEachExpr_x27___redArg___closed__3;
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_setMVarUserNamesAt_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_setMVarUserNamesAt_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet_visit___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_contains___at___Lean_Meta_setMVarUserNamesAt_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__5___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_setMVarUserNamesAt_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars_x27___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_hash___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_setMVarUserNamesAt_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfMonadControl___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_visitLambda_visit___at___Lean_Meta_visitLambda___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__7_spec__7_spec__7___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_setMVarUserNamesAt_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Meta_visitLet_visit___at___Lean_Meta_visitLet___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__12_spec__12_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_setMVarUserNamesAt___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_forEachExpr_x27_visit___redArg___closed__1;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars_x27___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Meta_mkForallFVars_x27_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___at___Lean_Meta_mkForallFVars_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda_visit___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_setMVarUserNamesAt_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda_visit___at___Lean_Meta_visitLambda___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__7_spec__7___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* l_Lean_MetavarContext_setMVarUserNameTemporarily(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda_visit___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_array_push(x_1, x_6);
x_8 = l_Lean_Meta_visitLambda_visit___redArg(x_2, x_3, x_4, x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda_visit___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
x_10 = l_Lean_Meta_withLocalDecl___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda_visit___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 6)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
x_10 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_4);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_visitLambda_visit___redArg___lam__0), 6, 5);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_3);
lean_closure_set(x_11, 4, x_9);
x_12 = lean_expr_instantiate_rev(x_8, x_4);
lean_dec(x_4);
lean_dec(x_8);
x_13 = lean_box(x_10);
lean_inc(x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_visitLambda_visit___redArg___lam__1___boxed), 7, 6);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_1);
lean_closure_set(x_14, 2, x_7);
lean_closure_set(x_14, 3, x_13);
lean_closure_set(x_14, 4, x_12);
lean_closure_set(x_14, 5, x_11);
x_15 = lean_apply_1(x_3, x_12);
x_16 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_15, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_expr_instantiate_rev(x_5, x_4);
lean_dec(x_4);
lean_dec(x_5);
x_18 = lean_apply_1(x_3, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_visitLambda_visit___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda_visit___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lean_Meta_visitLambda_visit___redArg___lam__1(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
lean_dec(x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_visitLambda___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Meta_visitLambda___redArg___closed__0;
x_6 = l_Lean_Meta_visitLambda_visit___redArg(x_1, x_2, x_3, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_visitLambda___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall_visit___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_array_push(x_1, x_6);
x_8 = l_Lean_Meta_visitForall_visit___redArg(x_2, x_3, x_4, x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall_visit___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 7)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
x_10 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_4);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_visitForall_visit___redArg___lam__0), 6, 5);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_3);
lean_closure_set(x_11, 4, x_9);
x_12 = lean_expr_instantiate_rev(x_8, x_4);
lean_dec(x_4);
lean_dec(x_8);
x_13 = lean_box(x_10);
lean_inc(x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_visitLambda_visit___redArg___lam__1___boxed), 7, 6);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_1);
lean_closure_set(x_14, 2, x_7);
lean_closure_set(x_14, 3, x_13);
lean_closure_set(x_14, 4, x_12);
lean_closure_set(x_14, 5, x_11);
x_15 = lean_apply_1(x_3, x_12);
x_16 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_15, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_expr_instantiate_rev(x_5, x_4);
lean_dec(x_4);
lean_dec(x_5);
x_18 = lean_apply_1(x_3, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_visitForall_visit___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Meta_visitLambda___redArg___closed__0;
x_6 = l_Lean_Meta_visitForall_visit___redArg(x_1, x_2, x_3, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_visitForall___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet_visit___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_array_push(x_1, x_6);
x_8 = l_Lean_Meta_visitLet_visit___redArg(x_2, x_3, x_4, x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet_visit___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
x_10 = l_Lean_Meta_withLetDecl___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet_visit___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_apply_1(x_1, x_2);
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet_visit___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 8)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 3);
lean_inc(x_10);
lean_dec(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_4);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_visitLet_visit___redArg___lam__0), 6, 5);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_3);
lean_closure_set(x_11, 4, x_10);
x_12 = lean_expr_instantiate_rev(x_8, x_4);
lean_dec(x_8);
x_13 = lean_expr_instantiate_rev(x_9, x_4);
lean_dec(x_4);
lean_dec(x_9);
lean_inc(x_13);
lean_inc(x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_visitLet_visit___redArg___lam__1___boxed), 7, 6);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_1);
lean_closure_set(x_14, 2, x_7);
lean_closure_set(x_14, 3, x_12);
lean_closure_set(x_14, 4, x_13);
lean_closure_set(x_14, 5, x_11);
lean_inc(x_6);
lean_inc(x_3);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_visitLet_visit___redArg___lam__2___boxed), 5, 4);
lean_closure_set(x_15, 0, x_3);
lean_closure_set(x_15, 1, x_13);
lean_closure_set(x_15, 2, x_6);
lean_closure_set(x_15, 3, x_14);
x_16 = lean_apply_1(x_3, x_12);
x_17 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_16, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_expr_instantiate_rev(x_5, x_4);
lean_dec(x_4);
lean_dec(x_5);
x_19 = lean_apply_1(x_3, x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_visitLet_visit___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet_visit___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_visitLet_visit___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet_visit___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_visitLet_visit___redArg___lam__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Meta_visitLambda___redArg___closed__0;
x_6 = l_Lean_Meta_visitLet_visit___redArg(x_1, x_2, x_3, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_visitLet___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_ctor_get(x_4, 1);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_array_get_size(x_5);
x_8 = l_Lean_Expr_hash(x_2);
x_9 = 32;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = 16;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_17 = 1;
x_18 = lean_usize_sub(x_16, x_17);
x_19 = lean_usize_land(x_15, x_18);
x_20 = lean_array_uget(x_5, x_19);
x_21 = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(x_3, x_2, x_20);
x_22 = lean_apply_2(x_6, lean_box(0), x_21);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_4, lean_box(0), x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; lean_object* x_23; uint8_t x_24; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_box(0);
x_10 = lean_array_get_size(x_8);
x_11 = l_Lean_Expr_hash(x_1);
x_12 = 32;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = 16;
x_16 = lean_uint64_shift_right(x_14, x_15);
x_17 = lean_uint64_xor(x_14, x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_20 = 1;
x_21 = lean_usize_sub(x_19, x_20);
x_22 = lean_usize_land(x_18, x_21);
x_23 = lean_array_uget(x_8, x_22);
lean_inc(x_23);
lean_inc(x_1);
lean_inc(x_2);
x_24 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_2, x_1, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_2);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_7, x_25);
lean_dec(x_7);
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_3);
lean_ctor_set(x_27, 2, x_23);
x_28 = lean_array_uset(x_8, x_22, x_27);
x_29 = lean_unsigned_to_nat(4u);
x_30 = lean_nat_mul(x_26, x_29);
x_31 = lean_unsigned_to_nat(3u);
x_32 = lean_nat_div(x_30, x_31);
lean_dec(x_30);
x_33 = lean_array_get_size(x_28);
x_34 = lean_nat_dec_le(x_32, x_33);
lean_dec(x_33);
lean_dec(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_4, x_28);
lean_ctor_set(x_5, 1, x_35);
lean_ctor_set(x_5, 0, x_26);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_9);
lean_ctor_set(x_36, 1, x_5);
return x_36;
}
else
{
lean_object* x_37; 
lean_dec(x_4);
lean_ctor_set(x_5, 1, x_28);
lean_ctor_set(x_5, 0, x_26);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_9);
lean_ctor_set(x_37, 1, x_5);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_4);
x_38 = lean_box(0);
x_39 = lean_array_uset(x_8, x_22, x_38);
x_40 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_2, x_1, x_3, x_23);
x_41 = lean_array_uset(x_39, x_22, x_40);
lean_ctor_set(x_5, 1, x_41);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_9);
lean_ctor_set(x_42, 1, x_5);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; size_t x_54; size_t x_55; size_t x_56; size_t x_57; size_t x_58; lean_object* x_59; uint8_t x_60; 
x_43 = lean_ctor_get(x_5, 0);
x_44 = lean_ctor_get(x_5, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_5);
x_45 = lean_box(0);
x_46 = lean_array_get_size(x_44);
x_47 = l_Lean_Expr_hash(x_1);
x_48 = 32;
x_49 = lean_uint64_shift_right(x_47, x_48);
x_50 = lean_uint64_xor(x_47, x_49);
x_51 = 16;
x_52 = lean_uint64_shift_right(x_50, x_51);
x_53 = lean_uint64_xor(x_50, x_52);
x_54 = lean_uint64_to_usize(x_53);
x_55 = lean_usize_of_nat(x_46);
lean_dec(x_46);
x_56 = 1;
x_57 = lean_usize_sub(x_55, x_56);
x_58 = lean_usize_land(x_54, x_57);
x_59 = lean_array_uget(x_44, x_58);
lean_inc(x_59);
lean_inc(x_1);
lean_inc(x_2);
x_60 = l_Std_DHashMap_Internal_AssocList_contains___redArg(x_2, x_1, x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
lean_dec(x_2);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_43, x_61);
lean_dec(x_43);
x_63 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_63, 0, x_1);
lean_ctor_set(x_63, 1, x_3);
lean_ctor_set(x_63, 2, x_59);
x_64 = lean_array_uset(x_44, x_58, x_63);
x_65 = lean_unsigned_to_nat(4u);
x_66 = lean_nat_mul(x_62, x_65);
x_67 = lean_unsigned_to_nat(3u);
x_68 = lean_nat_div(x_66, x_67);
lean_dec(x_66);
x_69 = lean_array_get_size(x_64);
x_70 = lean_nat_dec_le(x_68, x_69);
lean_dec(x_69);
lean_dec(x_68);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(x_4, x_64);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_62);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_45);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_4);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_62);
lean_ctor_set(x_74, 1, x_64);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_45);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_4);
x_76 = lean_box(0);
x_77 = lean_array_uset(x_44, x_58, x_76);
x_78 = l_Std_DHashMap_Internal_AssocList_replace___redArg(x_2, x_1, x_3, x_59);
x_79 = lean_array_uset(x_77, x_58, x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_43);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_45);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__2), 5, 4);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_8);
lean_closure_set(x_10, 3, x_4);
x_11 = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(x_11, 0, lean_box(0));
lean_closure_set(x_11, 1, lean_box(0));
lean_closure_set(x_11, 2, lean_box(0));
lean_closure_set(x_11, 3, x_5);
lean_closure_set(x_11, 4, x_10);
x_12 = lean_apply_2(x_6, lean_box(0), x_11);
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_12, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_forEachExpr_x27_visit___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__5___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadControlReaderT(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, uint8_t x_10) {
_start:
{
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_apply_2(x_11, lean_box(0), x_12);
return x_13;
}
else
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
lean_dec(x_1);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__4___boxed), 7, 6);
lean_closure_set(x_16, 0, x_3);
lean_closure_set(x_16, 1, x_4);
lean_closure_set(x_16, 2, x_5);
lean_closure_set(x_16, 3, x_6);
lean_closure_set(x_16, 4, x_15);
lean_closure_set(x_16, 5, x_7);
x_17 = l_Lean_Meta_forEachExpr_x27_visit___redArg(x_3, x_4, x_5, x_6, x_14, x_7);
x_18 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_17, x_16);
return x_18;
}
case 6:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_8);
lean_dec(x_1);
x_19 = l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__5___closed__0;
lean_inc(x_4);
x_20 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_4);
lean_inc(x_4);
x_21 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_21, 0, x_19);
lean_closure_set(x_21, 1, x_4);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27_visit___redArg), 6, 4);
lean_closure_set(x_23, 0, x_3);
lean_closure_set(x_23, 1, x_4);
lean_closure_set(x_23, 2, x_5);
lean_closure_set(x_23, 3, x_6);
x_24 = l_Lean_Meta_visitLambda___redArg(x_9, x_22, x_23, x_2);
x_25 = lean_apply_1(x_24, x_7);
return x_25;
}
case 7:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_8);
lean_dec(x_1);
x_26 = l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__5___closed__0;
lean_inc(x_4);
x_27 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_27, 0, x_26);
lean_closure_set(x_27, 1, x_4);
lean_inc(x_4);
x_28 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_28, 0, x_26);
lean_closure_set(x_28, 1, x_4);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27_visit___redArg), 6, 4);
lean_closure_set(x_30, 0, x_3);
lean_closure_set(x_30, 1, x_4);
lean_closure_set(x_30, 2, x_5);
lean_closure_set(x_30, 3, x_6);
x_31 = l_Lean_Meta_visitForall___redArg(x_9, x_29, x_30, x_2);
x_32 = lean_apply_1(x_31, x_7);
return x_32;
}
case 8:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_8);
lean_dec(x_1);
x_33 = l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__5___closed__0;
lean_inc(x_4);
x_34 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(x_34, 0, x_33);
lean_closure_set(x_34, 1, x_4);
lean_inc(x_4);
x_35 = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(x_35, 0, x_33);
lean_closure_set(x_35, 1, x_4);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27_visit___redArg), 6, 4);
lean_closure_set(x_37, 0, x_3);
lean_closure_set(x_37, 1, x_4);
lean_closure_set(x_37, 2, x_5);
lean_closure_set(x_37, 3, x_6);
x_38 = l_Lean_Meta_visitLet___redArg(x_9, x_36, x_37, x_2);
x_39 = lean_apply_1(x_38, x_7);
return x_39;
}
case 10:
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_40 = lean_ctor_get(x_2, 1);
lean_inc(x_40);
lean_dec(x_2);
x_41 = l_Lean_Meta_forEachExpr_x27_visit___redArg(x_3, x_4, x_5, x_6, x_40, x_7);
return x_41;
}
case 11:
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_42 = lean_ctor_get(x_2, 2);
lean_inc(x_42);
lean_dec(x_2);
x_43 = l_Lean_Meta_forEachExpr_x27_visit___redArg(x_3, x_4, x_5, x_6, x_42, x_7);
return x_43;
}
default: 
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_ctor_get(x_1, 1);
lean_inc(x_44);
lean_dec(x_1);
x_45 = lean_box(0);
x_46 = lean_apply_2(x_44, lean_box(0), x_45);
return x_46;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
x_8 = lean_apply_1(x_1, x_2);
lean_inc(x_3);
x_9 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_4);
x_10 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_9, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_apply_2(x_12, lean_box(0), x_11);
return x_13;
}
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27_visit___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Expr_eqv___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27_visit___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Expr_hash___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_inc(x_1);
x_7 = l_ReaderT_instMonad___redArg(x_1);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = l_Lean_Meta_forEachExpr_x27_visit___redArg___closed__0;
lean_inc(x_5);
lean_inc(x_8);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_11, 0, x_8);
lean_closure_set(x_11, 1, x_5);
lean_closure_set(x_11, 2, x_10);
x_12 = l_Lean_Meta_forEachExpr_x27_visit___redArg___closed__1;
lean_inc(x_9);
lean_inc(x_4);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_8);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__3), 8, 7);
lean_closure_set(x_13, 0, x_8);
lean_closure_set(x_13, 1, x_5);
lean_closure_set(x_13, 2, x_10);
lean_closure_set(x_13, 3, x_12);
lean_closure_set(x_13, 4, x_6);
lean_closure_set(x_13, 5, x_4);
lean_closure_set(x_13, 6, x_9);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_5);
lean_inc(x_8);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__5___boxed), 10, 9);
lean_closure_set(x_14, 0, x_8);
lean_closure_set(x_14, 1, x_5);
lean_closure_set(x_14, 2, x_1);
lean_closure_set(x_14, 3, x_2);
lean_closure_set(x_14, 4, x_3);
lean_closure_set(x_14, 5, x_4);
lean_closure_set(x_14, 6, x_6);
lean_closure_set(x_14, 7, x_9);
lean_closure_set(x_14, 8, x_7);
lean_inc(x_9);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__6), 7, 6);
lean_closure_set(x_15, 0, x_3);
lean_closure_set(x_15, 1, x_5);
lean_closure_set(x_15, 2, x_9);
lean_closure_set(x_15, 3, x_14);
lean_closure_set(x_15, 4, x_13);
lean_closure_set(x_15, 5, x_8);
x_16 = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(x_16, 0, lean_box(0));
lean_closure_set(x_16, 1, lean_box(0));
lean_closure_set(x_16, 2, x_6);
x_17 = lean_apply_2(x_4, lean_box(0), x_16);
lean_inc(x_9);
x_18 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_17, x_11);
x_19 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_18, x_15);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_forEachExpr_x27_visit___redArg(x_2, x_3, x_4, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_10);
lean_dec(x_10);
x_12 = l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_forEachExpr_x27_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_apply_1(x_1, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27___redArg___lam__0___boxed), 6, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27___redArg___lam__3), 3, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
x_7 = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, lean_box(0));
lean_closure_set(x_7, 2, x_2);
x_8 = lean_apply_2(x_3, lean_box(0), x_7);
x_9 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27___redArg___lam__4), 5, 4);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_2);
lean_closure_set(x_9, 3, x_3);
x_10 = l_Lean_Meta_forEachExpr_x27_visit___redArg(x_4, x_5, x_6, x_2, x_7, x_8);
x_11 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_10, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_Meta_forEachExpr_x27___redArg___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_forEachExpr_x27___redArg___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_forEachExpr_x27___redArg___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_forEachExpr_x27___redArg___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_forEachExpr_x27___redArg___closed__4;
x_2 = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27___redArg___lam__1), 3, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = l_Lean_Meta_forEachExpr_x27___redArg___closed__5;
x_11 = l_Lean_Meta_forEachExpr_x27___redArg___lam__1(x_2, lean_box(0), x_10);
lean_inc(x_8);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27___redArg___lam__2), 2, 1);
lean_closure_set(x_12, 0, x_8);
lean_inc(x_7);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27___redArg___lam__5), 8, 7);
lean_closure_set(x_13, 0, x_8);
lean_closure_set(x_13, 1, x_9);
lean_closure_set(x_13, 2, x_7);
lean_closure_set(x_13, 3, x_1);
lean_closure_set(x_13, 4, x_3);
lean_closure_set(x_13, 5, x_5);
lean_closure_set(x_13, 6, x_4);
lean_inc(x_7);
x_14 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_11, x_13);
x_15 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_14, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_forEachExpr_x27___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_forEachExpr_x27___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(1);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_apply_1(x_1, x_4);
x_6 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr___redArg___lam__1), 4, 3);
lean_closure_set(x_10, 0, x_5);
lean_closure_set(x_10, 1, x_7);
lean_closure_set(x_10, 2, x_9);
x_11 = l_Lean_Meta_forEachExpr_x27___redArg(x_1, x_2, x_3, x_4, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_forEachExpr___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_forEachExpr___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Lean_Name_isAnonymous(x_3);
x_5 = lean_box(x_4);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_8, 0, x_6);
x_9 = lean_alloc_closure((void*)(l_Lean_MVarId_getDecl___boxed), 6, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = lean_apply_2(x_2, lean_box(0), x_9);
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_10, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_box(0);
x_14 = lean_apply_2(x_12, lean_box(0), x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_setMVarUserNamesAt_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_setMVarUserNamesAt_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_setMVarUserNamesAt_spec__0___redArg___lam__0), 8, 1);
lean_closure_set(x_10, 0, x_3);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux___redArg(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_setMVarUserNamesAt_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_setMVarUserNamesAt_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Array_contains___at___Lean_Meta_setMVarUserNamesAt_spec__1_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_expr_eqv(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
return x_7;
}
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
return x_12;
}
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___Lean_Meta_setMVarUserNamesAt_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
size_t x_6; size_t x_7; uint8_t x_8; 
x_6 = 0;
x_7 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_8 = l_Array_anyMUnsafe_any___at___Array_contains___at___Lean_Meta_setMVarUserNamesAt_spec__1_spec__1(x_2, x_1, x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_setMVarUserNamesAt_spec__3_spec__3___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_5);
x_13 = lean_nat_dec_lt(x_1, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_4);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_15 = l_Lean_instInhabitedExpr;
x_16 = lean_array_get(x_15, x_5, x_1);
x_17 = l_Lean_Meta_getFVarLocalDecl___redArg(x_16, x_7, x_9, x_10, x_11);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_56; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_56 = lean_ctor_get(x_18, 2);
lean_inc(x_56);
lean_dec(x_18);
x_20 = x_56;
goto block_55;
block_55:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_21 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg(x_20, x_10, x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_st_ref_take(x_3, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_4);
x_27 = lean_array_push(x_25, x_4);
x_28 = lean_st_ref_set(x_3, x_27, x_26);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_st_ref_take(x_8, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = l_Lean_MetavarContext_setMVarUserNameTemporarily(x_34, x_4, x_22);
lean_ctor_set(x_31, 0, x_35);
x_36 = lean_st_ref_set(x_8, x_31, x_32);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
x_39 = lean_box(0);
lean_ctor_set(x_36, 0, x_39);
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_dec(x_36);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_43 = lean_ctor_get(x_31, 0);
x_44 = lean_ctor_get(x_31, 1);
x_45 = lean_ctor_get(x_31, 2);
x_46 = lean_ctor_get(x_31, 3);
x_47 = lean_ctor_get(x_31, 4);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_31);
x_48 = l_Lean_MetavarContext_setMVarUserNameTemporarily(x_43, x_4, x_22);
x_49 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_44);
lean_ctor_set(x_49, 2, x_45);
lean_ctor_set(x_49, 3, x_46);
lean_ctor_set(x_49, 4, x_47);
x_50 = lean_st_ref_set(x_8, x_49, x_32);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_52 = x_50;
} else {
 lean_dec_ref(x_50);
 x_52 = lean_box(0);
}
x_53 = lean_box(0);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_4);
x_57 = !lean_is_exclusive(x_17);
if (x_57 == 0)
{
return x_17;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_17, 0);
x_59 = lean_ctor_get(x_17, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_17);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_setMVarUserNamesAt_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_22; 
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_22 = lean_nat_dec_lt(x_9, x_15);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_14);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; uint8_t x_52; 
lean_dec(x_8);
x_24 = lean_array_fget(x_1, x_9);
x_52 = l_Lean_Expr_isMVar(x_24);
if (x_52 == 0)
{
x_25 = x_52;
goto block_51;
}
else
{
uint8_t x_53; 
x_53 = l_Array_contains___at___Lean_Meta_setMVarUserNamesAt_spec__1(x_6, x_24);
x_25 = x_53;
goto block_51;
}
block_51:
{
if (x_25 == 0)
{
lean_dec(x_24);
lean_inc(x_2);
x_17 = x_2;
x_18 = x_14;
goto block_21;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_Expr_mvarId_x21(x_24);
lean_dec(x_24);
lean_inc(x_26);
x_27 = l_Lean_MVarId_getDecl(x_26, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Name_isAnonymous(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_dec(x_26);
lean_inc(x_2);
x_17 = x_2;
x_18 = x_29;
goto block_21;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_Expr_getAppFn(x_4);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_33 = lean_infer_type(x_32, x_10, x_11, x_12, x_13, x_29);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_9);
x_36 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_setMVarUserNamesAt_spec__3_spec__3___redArg___lam__0___boxed), 11, 4);
lean_closure_set(x_36, 0, x_9);
lean_closure_set(x_36, 1, x_2);
lean_closure_set(x_36, 2, x_3);
lean_closure_set(x_36, 3, x_26);
x_37 = lean_nat_add(x_9, x_5);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_box(0);
x_40 = lean_unbox(x_39);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_41 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_setMVarUserNamesAt_spec__0___redArg(x_34, x_38, x_36, x_40, x_10, x_11, x_12, x_13, x_35);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
lean_inc(x_2);
x_17 = x_2;
x_18 = x_42;
goto block_21;
}
else
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
return x_41;
}
}
else
{
uint8_t x_43; 
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_33);
if (x_43 == 0)
{
return x_33;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_33, 0);
x_45 = lean_ctor_get(x_33, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_33);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_27);
if (x_47 == 0)
{
return x_27;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_27, 0);
x_49 = lean_ctor_get(x_27, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_27);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
}
block_21:
{
lean_object* x_19; 
x_19 = lean_nat_add(x_9, x_16);
lean_dec(x_9);
x_8 = x_17;
x_9 = x_19;
x_14 = x_18;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_setMVarUserNamesAt_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_setMVarUserNamesAt_spec__3_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_12, x_13, x_14, x_15, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_setMVarUserNamesAt_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_22; 
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_22 = lean_nat_dec_lt(x_9, x_15);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_14);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; uint8_t x_52; 
lean_dec(x_8);
x_24 = lean_array_fget(x_1, x_9);
x_52 = l_Lean_Expr_isMVar(x_24);
if (x_52 == 0)
{
x_25 = x_52;
goto block_51;
}
else
{
uint8_t x_53; 
x_53 = l_Array_contains___at___Lean_Meta_setMVarUserNamesAt_spec__1(x_6, x_24);
x_25 = x_53;
goto block_51;
}
block_51:
{
if (x_25 == 0)
{
lean_dec(x_24);
lean_inc(x_2);
x_17 = x_2;
x_18 = x_14;
goto block_21;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_Expr_mvarId_x21(x_24);
lean_dec(x_24);
lean_inc(x_26);
x_27 = l_Lean_MVarId_getDecl(x_26, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Name_isAnonymous(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_dec(x_26);
lean_inc(x_2);
x_17 = x_2;
x_18 = x_29;
goto block_21;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_Expr_getAppFn(x_4);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_33 = lean_infer_type(x_32, x_10, x_11, x_12, x_13, x_29);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_9);
x_36 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_setMVarUserNamesAt_spec__3_spec__3___redArg___lam__0___boxed), 11, 4);
lean_closure_set(x_36, 0, x_9);
lean_closure_set(x_36, 1, x_2);
lean_closure_set(x_36, 2, x_3);
lean_closure_set(x_36, 3, x_26);
x_37 = lean_nat_add(x_9, x_5);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_box(0);
x_40 = lean_unbox(x_39);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_41 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_setMVarUserNamesAt_spec__0___redArg(x_34, x_38, x_36, x_40, x_10, x_11, x_12, x_13, x_35);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
lean_inc(x_2);
x_17 = x_2;
x_18 = x_42;
goto block_21;
}
else
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
return x_41;
}
}
else
{
uint8_t x_43; 
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_33);
if (x_43 == 0)
{
return x_33;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_33, 0);
x_45 = lean_ctor_get(x_33, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_33);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_27);
if (x_47 == 0)
{
return x_27;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_27, 0);
x_49 = lean_ctor_get(x_27, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_27);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_nat_add(x_9, x_16);
lean_dec(x_9);
x_20 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_setMVarUserNamesAt_spec__3_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_17, x_19, x_10, x_11, x_12, x_13, x_18);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_setMVarUserNamesAt_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_setMVarUserNamesAt_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_12, x_13, x_14, x_15, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__5___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_expr_eqv(x_4, x_1);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__5___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_expr_eqv(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__6___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_expr_eqv(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__6___redArg(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__6___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_visitLambda_visit___at___Lean_Meta_visitLambda___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__7_spec__7_spec__7___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_3, x_2, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_visitLambda_visit___at___Lean_Meta_visitLambda___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__7_spec__7_spec__7___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___Lean_Meta_visitLambda_visit___at___Lean_Meta_visitLambda___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__7_spec__7_spec__7___redArg___lam__0), 8, 2);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___redArg(x_1, x_2, x_3, x_12, x_5, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_visitLambda_visit___at___Lean_Meta_visitLambda___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__7_spec__7_spec__7(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_withLocalDecl___at___Lean_Meta_visitLambda_visit___at___Lean_Meta_visitLambda___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__7_spec__7_spec__7___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda_visit___at___Lean_Meta_visitLambda___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__7_spec__7___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_push(x_1, x_4);
x_12 = l_Lean_Meta_visitLambda_visit___at___Lean_Meta_visitLambda___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__7_spec__7(x_2, x_11, x_3, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda_visit___at___Lean_Meta_visitLambda___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__7_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_3) == 6)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_dec(x_3);
x_14 = lean_expr_instantiate_rev(x_11, x_2);
lean_dec(x_11);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_14);
x_15 = lean_apply_7(x_1, x_14, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_visitLambda_visit___at___Lean_Meta_visitLambda___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__7_spec__7___lam__0), 10, 3);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_1);
lean_closure_set(x_17, 2, x_12);
x_18 = lean_box(0);
x_19 = lean_unbox(x_18);
x_20 = l_Lean_Meta_withLocalDecl___at___Lean_Meta_visitLambda_visit___at___Lean_Meta_visitLambda___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__7_spec__7_spec__7___redArg(x_10, x_13, x_14, x_17, x_19, x_4, x_5, x_6, x_7, x_8, x_16);
return x_20;
}
else
{
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_expr_instantiate_rev(x_3, x_2);
lean_dec(x_2);
lean_dec(x_3);
x_22 = lean_apply_7(x_1, x_21, x_4, x_5, x_6, x_7, x_8, x_9);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Meta_visitLambda___redArg___closed__0;
x_10 = l_Lean_Meta_visitLambda_visit___at___Lean_Meta_visitLambda___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__7_spec__7(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall_visit___at___Lean_Meta_visitForall___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__10_spec__10___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_push(x_1, x_4);
x_12 = l_Lean_Meta_visitForall_visit___at___Lean_Meta_visitForall___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__10_spec__10(x_2, x_11, x_3, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall_visit___at___Lean_Meta_visitForall___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__10_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_3) == 7)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
lean_dec(x_3);
x_14 = lean_expr_instantiate_rev(x_11, x_2);
lean_dec(x_11);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_14);
x_15 = lean_apply_7(x_1, x_14, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_visitForall_visit___at___Lean_Meta_visitForall___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__10_spec__10___lam__0), 10, 3);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_1);
lean_closure_set(x_17, 2, x_12);
x_18 = lean_box(0);
x_19 = lean_unbox(x_18);
x_20 = l_Lean_Meta_withLocalDecl___at___Lean_Meta_visitLambda_visit___at___Lean_Meta_visitLambda___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__7_spec__7_spec__7___redArg(x_10, x_13, x_14, x_17, x_19, x_4, x_5, x_6, x_7, x_8, x_16);
return x_20;
}
else
{
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_expr_instantiate_rev(x_3, x_2);
lean_dec(x_2);
lean_dec(x_3);
x_22 = lean_apply_7(x_1, x_21, x_4, x_5, x_6, x_7, x_8, x_9);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Meta_visitLambda___redArg___closed__0;
x_10 = l_Lean_Meta_visitForall_visit___at___Lean_Meta_visitForall___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__10_spec__10(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Meta_visitLet_visit___at___Lean_Meta_visitLet___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__12_spec__12_spec__12___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___Lean_Meta_visitLambda_visit___at___Lean_Meta_visitLambda___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__7_spec__7_spec__7___redArg___lam__0), 8, 2);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___redArg(x_1, x_2, x_3, x_12, x_5, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Meta_visitLet_visit___at___Lean_Meta_visitLet___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__12_spec__12_spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_withLetDecl___at___Lean_Meta_visitLet_visit___at___Lean_Meta_visitLet___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__12_spec__12_spec__12___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet_visit___at___Lean_Meta_visitLet___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__12_spec__12___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_push(x_1, x_4);
x_12 = l_Lean_Meta_visitLet_visit___at___Lean_Meta_visitLet___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__12_spec__12(x_2, x_11, x_3, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet_visit___at___Lean_Meta_visitLet___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__12_spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_3) == 8)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 3);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_expr_instantiate_rev(x_11, x_2);
lean_dec(x_11);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_14);
x_15 = lean_apply_7(x_1, x_14, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_expr_instantiate_rev(x_12, x_2);
lean_dec(x_12);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_17);
x_18 = lean_apply_7(x_1, x_17, x_4, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_visitLet_visit___at___Lean_Meta_visitLet___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__12_spec__12___lam__0), 10, 3);
lean_closure_set(x_20, 0, x_2);
lean_closure_set(x_20, 1, x_1);
lean_closure_set(x_20, 2, x_13);
x_21 = lean_box(0);
x_22 = lean_unbox(x_21);
x_23 = l_Lean_Meta_withLetDecl___at___Lean_Meta_visitLet_visit___at___Lean_Meta_visitLet___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__12_spec__12_spec__12___redArg(x_10, x_14, x_17, x_20, x_22, x_4, x_5, x_6, x_7, x_8, x_19);
return x_23;
}
else
{
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
else
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_expr_instantiate_rev(x_3, x_2);
lean_dec(x_2);
lean_dec(x_3);
x_25 = lean_apply_7(x_1, x_24, x_4, x_5, x_6, x_7, x_8, x_9);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Meta_visitLambda___redArg___closed__0;
x_10 = l_Lean_Meta_visitLet_visit___at___Lean_Meta_visitLet___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__12_spec__12(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_apply_1(x_2, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5___lam__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_take(x_1, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 1);
x_13 = lean_box(0);
x_21 = lean_array_get_size(x_12);
x_22 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_23 = lean_usize_sub(x_22, x_2);
x_24 = lean_usize_land(x_3, x_23);
x_25 = lean_array_uget(x_12, x_24);
x_26 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__0___redArg(x_4, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_11, x_27);
lean_dec(x_11);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_4);
lean_ctor_set(x_29, 1, x_5);
lean_ctor_set(x_29, 2, x_25);
x_30 = lean_array_uset(x_12, x_24, x_29);
x_31 = lean_unsigned_to_nat(4u);
x_32 = lean_nat_mul(x_28, x_31);
x_33 = lean_unsigned_to_nat(3u);
x_34 = lean_nat_div(x_32, x_33);
lean_dec(x_32);
x_35 = lean_array_get_size(x_30);
x_36 = lean_nat_dec_le(x_34, x_35);
lean_dec(x_35);
lean_dec(x_34);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__1___redArg(x_30);
lean_ctor_set(x_8, 1, x_37);
lean_ctor_set(x_8, 0, x_28);
x_14 = x_8;
goto block_20;
}
else
{
lean_ctor_set(x_8, 1, x_30);
lean_ctor_set(x_8, 0, x_28);
x_14 = x_8;
goto block_20;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_box(0);
x_39 = lean_array_uset(x_12, x_24, x_38);
x_40 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__6___redArg(x_4, x_5, x_25);
x_41 = lean_array_uset(x_39, x_24, x_40);
lean_ctor_set(x_8, 1, x_41);
x_14 = x_8;
goto block_20;
}
block_20:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_st_ref_set(x_1, x_14, x_9);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_13);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_51; size_t x_52; size_t x_53; size_t x_54; lean_object* x_55; uint8_t x_56; 
x_42 = lean_ctor_get(x_8, 0);
x_43 = lean_ctor_get(x_8, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_8);
x_44 = lean_box(0);
x_51 = lean_array_get_size(x_43);
x_52 = lean_usize_of_nat(x_51);
lean_dec(x_51);
x_53 = lean_usize_sub(x_52, x_2);
x_54 = lean_usize_land(x_3, x_53);
x_55 = lean_array_uget(x_43, x_54);
x_56 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__0___redArg(x_4, x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_add(x_42, x_57);
lean_dec(x_42);
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_4);
lean_ctor_set(x_59, 1, x_5);
lean_ctor_set(x_59, 2, x_55);
x_60 = lean_array_uset(x_43, x_54, x_59);
x_61 = lean_unsigned_to_nat(4u);
x_62 = lean_nat_mul(x_58, x_61);
x_63 = lean_unsigned_to_nat(3u);
x_64 = lean_nat_div(x_62, x_63);
lean_dec(x_62);
x_65 = lean_array_get_size(x_60);
x_66 = lean_nat_dec_le(x_64, x_65);
lean_dec(x_65);
lean_dec(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit_spec__1___redArg(x_60);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_58);
lean_ctor_set(x_68, 1, x_67);
x_45 = x_68;
goto block_50;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_58);
lean_ctor_set(x_69, 1, x_60);
x_45 = x_69;
goto block_50;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_box(0);
x_71 = lean_array_uset(x_43, x_54, x_70);
x_72 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__6___redArg(x_4, x_5, x_55);
x_73 = lean_array_uset(x_71, x_54, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_42);
lean_ctor_set(x_74, 1, x_73);
x_45 = x_74;
goto block_50;
}
block_50:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_st_ref_set(x_1, x_45, x_9);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_inc(x_3);
x_9 = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(x_9, 0, lean_box(0));
lean_closure_set(x_9, 1, lean_box(0));
lean_closure_set(x_9, 2, x_3);
x_10 = l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5___lam__0(lean_box(0), x_9, x_4, x_5, x_6, x_7, x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; size_t x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_37; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_array_get_size(x_14);
x_16 = l_Lean_Expr_hash(x_2);
x_17 = 32;
x_18 = lean_uint64_shift_right(x_16, x_17);
x_19 = lean_uint64_xor(x_16, x_18);
x_20 = 16;
x_21 = lean_uint64_shift_right(x_19, x_20);
x_22 = lean_uint64_xor(x_19, x_21);
x_23 = lean_uint64_to_usize(x_22);
x_24 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_25 = 1;
x_41 = lean_usize_sub(x_24, x_25);
x_42 = lean_usize_land(x_23, x_41);
x_43 = lean_array_uget(x_14, x_42);
lean_dec(x_14);
x_44 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__5___redArg(x_2, x_43);
lean_dec(x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
lean_free_object(x_10);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_45 = lean_apply_6(x_1, x_2, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_1);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_box(0);
x_26 = x_49;
x_27 = x_48;
goto block_36;
}
else
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
lean_dec(x_45);
x_51 = lean_ctor_get(x_2, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_2, 1);
lean_inc(x_52);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_53 = l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5(x_1, x_51, x_3, x_4, x_5, x_6, x_7, x_50);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_55 = l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5(x_1, x_52, x_3, x_4, x_5, x_6, x_7, x_54);
x_37 = x_55;
goto block_40;
}
else
{
lean_dec(x_52);
lean_dec(x_1);
x_37 = x_53;
goto block_40;
}
}
case 6:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_45, 1);
lean_inc(x_56);
lean_dec(x_45);
x_57 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5___lam__2), 8, 1);
lean_closure_set(x_57, 0, x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_58 = l_Lean_Meta_visitLambda___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__7(x_57, x_2, x_3, x_4, x_5, x_6, x_7, x_56);
x_37 = x_58;
goto block_40;
}
case 7:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_45, 1);
lean_inc(x_59);
lean_dec(x_45);
x_60 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5___lam__2), 8, 1);
lean_closure_set(x_60, 0, x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_61 = l_Lean_Meta_visitForall___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__10(x_60, x_2, x_3, x_4, x_5, x_6, x_7, x_59);
x_37 = x_61;
goto block_40;
}
case 8:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_45, 1);
lean_inc(x_62);
lean_dec(x_45);
x_63 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5___lam__2), 8, 1);
lean_closure_set(x_63, 0, x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_64 = l_Lean_Meta_visitLet___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__12(x_63, x_2, x_3, x_4, x_5, x_6, x_7, x_62);
x_37 = x_64;
goto block_40;
}
case 10:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_45, 1);
lean_inc(x_65);
lean_dec(x_45);
x_66 = lean_ctor_get(x_2, 1);
lean_inc(x_66);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_67 = l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5(x_1, x_66, x_3, x_4, x_5, x_6, x_7, x_65);
x_37 = x_67;
goto block_40;
}
case 11:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_45, 1);
lean_inc(x_68);
lean_dec(x_45);
x_69 = lean_ctor_get(x_2, 2);
lean_inc(x_69);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_70 = l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5(x_1, x_69, x_3, x_4, x_5, x_6, x_7, x_68);
x_37 = x_70;
goto block_40;
}
default: 
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_1);
x_71 = lean_ctor_get(x_45, 1);
lean_inc(x_71);
lean_dec(x_45);
x_72 = lean_box(0);
x_26 = x_72;
x_27 = x_71;
goto block_36;
}
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_45);
if (x_73 == 0)
{
return x_45;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_45, 0);
x_75 = lean_ctor_get(x_45, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_45);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
lean_object* x_77; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_77 = lean_ctor_get(x_44, 0);
lean_inc(x_77);
lean_dec(x_44);
lean_ctor_set(x_10, 0, x_77);
return x_10;
}
block_36:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5___boxed__const__1;
x_29 = lean_box_usize(x_23);
lean_inc(x_26);
x_30 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5___lam__1___boxed), 6, 5);
lean_closure_set(x_30, 0, x_3);
lean_closure_set(x_30, 1, x_28);
lean_closure_set(x_30, 2, x_29);
lean_closure_set(x_30, 3, x_2);
lean_closure_set(x_30, 4, x_26);
x_31 = l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5___lam__0(lean_box(0), x_30, x_4, x_5, x_6, x_7, x_27);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_26);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
block_40:
{
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_26 = x_38;
x_27 = x_39;
goto block_36;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_37;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint64_t x_82; uint64_t x_83; uint64_t x_84; uint64_t x_85; uint64_t x_86; uint64_t x_87; uint64_t x_88; size_t x_89; size_t x_90; size_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_102; size_t x_106; size_t x_107; lean_object* x_108; lean_object* x_109; 
x_78 = lean_ctor_get(x_10, 0);
x_79 = lean_ctor_get(x_10, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_10);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_array_get_size(x_80);
x_82 = l_Lean_Expr_hash(x_2);
x_83 = 32;
x_84 = lean_uint64_shift_right(x_82, x_83);
x_85 = lean_uint64_xor(x_82, x_84);
x_86 = 16;
x_87 = lean_uint64_shift_right(x_85, x_86);
x_88 = lean_uint64_xor(x_85, x_87);
x_89 = lean_uint64_to_usize(x_88);
x_90 = lean_usize_of_nat(x_81);
lean_dec(x_81);
x_91 = 1;
x_106 = lean_usize_sub(x_90, x_91);
x_107 = lean_usize_land(x_89, x_106);
x_108 = lean_array_uget(x_80, x_107);
lean_dec(x_80);
x_109 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__5___redArg(x_2, x_108);
lean_dec(x_108);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; 
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_110 = lean_apply_6(x_1, x_2, x_4, x_5, x_6, x_7, x_79);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; uint8_t x_112; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_unbox(x_111);
lean_dec(x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_1);
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
lean_dec(x_110);
x_114 = lean_box(0);
x_92 = x_114;
x_93 = x_113;
goto block_101;
}
else
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_115 = lean_ctor_get(x_110, 1);
lean_inc(x_115);
lean_dec(x_110);
x_116 = lean_ctor_get(x_2, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_2, 1);
lean_inc(x_117);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_118 = l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5(x_1, x_116, x_3, x_4, x_5, x_6, x_7, x_115);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
lean_dec(x_118);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_120 = l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5(x_1, x_117, x_3, x_4, x_5, x_6, x_7, x_119);
x_102 = x_120;
goto block_105;
}
else
{
lean_dec(x_117);
lean_dec(x_1);
x_102 = x_118;
goto block_105;
}
}
case 6:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_110, 1);
lean_inc(x_121);
lean_dec(x_110);
x_122 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5___lam__2), 8, 1);
lean_closure_set(x_122, 0, x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_123 = l_Lean_Meta_visitLambda___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__7(x_122, x_2, x_3, x_4, x_5, x_6, x_7, x_121);
x_102 = x_123;
goto block_105;
}
case 7:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_110, 1);
lean_inc(x_124);
lean_dec(x_110);
x_125 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5___lam__2), 8, 1);
lean_closure_set(x_125, 0, x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_126 = l_Lean_Meta_visitForall___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__10(x_125, x_2, x_3, x_4, x_5, x_6, x_7, x_124);
x_102 = x_126;
goto block_105;
}
case 8:
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_110, 1);
lean_inc(x_127);
lean_dec(x_110);
x_128 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5___lam__2), 8, 1);
lean_closure_set(x_128, 0, x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_129 = l_Lean_Meta_visitLet___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__12(x_128, x_2, x_3, x_4, x_5, x_6, x_7, x_127);
x_102 = x_129;
goto block_105;
}
case 10:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_110, 1);
lean_inc(x_130);
lean_dec(x_110);
x_131 = lean_ctor_get(x_2, 1);
lean_inc(x_131);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_132 = l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5(x_1, x_131, x_3, x_4, x_5, x_6, x_7, x_130);
x_102 = x_132;
goto block_105;
}
case 11:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_110, 1);
lean_inc(x_133);
lean_dec(x_110);
x_134 = lean_ctor_get(x_2, 2);
lean_inc(x_134);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_135 = l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5(x_1, x_134, x_3, x_4, x_5, x_6, x_7, x_133);
x_102 = x_135;
goto block_105;
}
default: 
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_1);
x_136 = lean_ctor_get(x_110, 1);
lean_inc(x_136);
lean_dec(x_110);
x_137 = lean_box(0);
x_92 = x_137;
x_93 = x_136;
goto block_101;
}
}
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_138 = lean_ctor_get(x_110, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_110, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_140 = x_110;
} else {
 lean_dec_ref(x_110);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(1, 2, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_139);
return x_141;
}
}
else
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_142 = lean_ctor_get(x_109, 0);
lean_inc(x_142);
lean_dec(x_109);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_79);
return x_143;
}
block_101:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_94 = l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5___boxed__const__1;
x_95 = lean_box_usize(x_89);
lean_inc(x_92);
x_96 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5___lam__1___boxed), 6, 5);
lean_closure_set(x_96, 0, x_3);
lean_closure_set(x_96, 1, x_94);
lean_closure_set(x_96, 2, x_95);
lean_closure_set(x_96, 3, x_2);
lean_closure_set(x_96, 4, x_92);
x_97 = l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5___lam__0(lean_box(0), x_96, x_4, x_5, x_6, x_7, x_93);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_99 = x_97;
} else {
 lean_dec_ref(x_97);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_92);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
block_105:
{
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_92 = x_103;
x_93 = x_104;
goto block_101;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_102;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_apply_1(x_2, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_Lean_Meta_forEachExpr_x27___redArg___closed__5;
x_9 = l_Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5___lam__0(lean_box(0), x_8, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_10);
x_12 = l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5(x_2, x_1, x_10, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(x_15, 0, lean_box(0));
lean_closure_set(x_15, 1, lean_box(0));
lean_closure_set(x_15, 2, x_10);
x_16 = l_Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5___lam__0(lean_box(0), x_15, x_3, x_4, x_5, x_6, x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_13);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_dec(x_10);
x_11 = lean_box(1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_box(1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5___lam__0), 7, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = l_Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_setMVarUserNamesAt___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_setMVarUserNamesAt___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Expr_isApp(x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = l_Lean_Meta_setMVarUserNamesAt___lam__0___closed__0;
x_14 = l_Lean_Expr_getAppNumArgs(x_4);
lean_inc(x_14);
x_15 = lean_mk_array(x_14, x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_14, x_16);
lean_dec(x_14);
lean_inc(x_4);
x_18 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_4, x_15, x_17);
x_19 = lean_array_get_size(x_18);
lean_inc(x_1);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_16);
x_21 = lean_box(0);
x_22 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_setMVarUserNamesAt_spec__3___redArg(x_18, x_21, x_2, x_4, x_16, x_3, x_20, x_21, x_1, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_20);
lean_dec(x_4);
lean_dec(x_18);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
return x_22;
}
}
}
}
static lean_object* _init_l_Lean_Meta_setMVarUserNamesAt___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_setMVarUserNamesAt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Meta_setMVarUserNamesAt___closed__0;
x_10 = lean_st_mk_ref(x_9, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_1, x_4, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_11);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_setMVarUserNamesAt___lam__0___boxed), 9, 3);
lean_closure_set(x_16, 0, x_8);
lean_closure_set(x_16, 1, x_11);
lean_closure_set(x_16, 2, x_2);
x_17 = l_Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5(x_14, x_16, x_3, x_4, x_5, x_6, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_get(x_11, x_18);
lean_dec(x_11);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_11);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_17);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_setMVarUserNamesAt_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_setMVarUserNamesAt_spec__0___redArg(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_setMVarUserNamesAt_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_setMVarUserNamesAt_spec__0(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_contains___at___Lean_Meta_setMVarUserNamesAt_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Array_contains___at___Lean_Meta_setMVarUserNamesAt_spec__1_spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___Lean_Meta_setMVarUserNamesAt_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at___Lean_Meta_setMVarUserNamesAt_spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_setMVarUserNamesAt_spec__3_spec__3___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_setMVarUserNamesAt_spec__3_spec__3___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_setMVarUserNamesAt_spec__3_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_setMVarUserNamesAt_spec__3_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_setMVarUserNamesAt_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Meta_setMVarUserNamesAt_spec__3_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_setMVarUserNamesAt_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_setMVarUserNamesAt_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_setMVarUserNamesAt_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_setMVarUserNamesAt_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__5___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__5(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_visitLambda_visit___at___Lean_Meta_visitLambda___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__7_spec__7_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l_Lean_Meta_withLocalDecl___at___Lean_Meta_visitLambda_visit___at___Lean_Meta_visitLambda___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__7_spec__7_spec__7___redArg(x_1, x_12, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_visitLambda_visit___at___Lean_Meta_visitLambda___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__7_spec__7_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = lean_unbox(x_6);
lean_dec(x_6);
x_15 = l_Lean_Meta_withLocalDecl___at___Lean_Meta_visitLambda_visit___at___Lean_Meta_visitLambda___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__7_spec__7_spec__7(x_1, x_2, x_13, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Meta_visitLet_visit___at___Lean_Meta_visitLet___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__12_spec__12_spec__12___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_Meta_withLetDecl___at___Lean_Meta_visitLet_visit___at___Lean_Meta_visitLet___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__12_spec__12_spec__12___redArg(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___Lean_Meta_visitLet_visit___at___Lean_Meta_visitLet___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__12_spec__12_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_Lean_Meta_withLetDecl___at___Lean_Meta_visitLet_visit___at___Lean_Meta_visitLet___at___Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5_spec__12_spec__12_spec__12(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5___lam__1(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_setMVarUserNamesAt___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_setMVarUserNamesAt___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_resetMVarUserNames_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_4, x_3);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_5);
x_10 = lean_st_ref_take(x_6, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_array_uget(x_2, x_4);
x_16 = lean_box(0);
x_17 = l_Lean_MetavarContext_setMVarUserNameTemporarily(x_14, x_15, x_16);
lean_ctor_set(x_11, 0, x_17);
x_18 = lean_st_ref_set(x_6, x_11, x_12);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = 1;
x_21 = lean_usize_add(x_4, x_20);
lean_inc(x_1);
{
size_t _tmp_3 = x_21;
lean_object* _tmp_4 = x_1;
lean_object* _tmp_6 = x_19;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_7 = _tmp_6;
}
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
x_25 = lean_ctor_get(x_11, 2);
x_26 = lean_ctor_get(x_11, 3);
x_27 = lean_ctor_get(x_11, 4);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_28 = lean_array_uget(x_2, x_4);
x_29 = lean_box(0);
x_30 = l_Lean_MetavarContext_setMVarUserNameTemporarily(x_23, x_28, x_29);
x_31 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_24);
lean_ctor_set(x_31, 2, x_25);
lean_ctor_set(x_31, 3, x_26);
lean_ctor_set(x_31, 4, x_27);
x_32 = lean_st_ref_set(x_6, x_31, x_12);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = 1;
x_35 = lean_usize_add(x_4, x_34);
lean_inc(x_1);
{
size_t _tmp_3 = x_35;
lean_object* _tmp_4 = x_1;
lean_object* _tmp_6 = x_33;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_7 = _tmp_6;
}
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_resetMVarUserNames_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_resetMVarUserNames_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_resetMVarUserNames(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_box(0);
x_8 = lean_array_size(x_1);
x_9 = 0;
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_resetMVarUserNames_spec__0___redArg(x_7, x_1, x_8, x_9, x_7, x_3, x_6);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_7);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_resetMVarUserNames_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_resetMVarUserNames_spec__0___redArg(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_resetMVarUserNames_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_resetMVarUserNames_spec__0(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_resetMVarUserNames___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_resetMVarUserNames(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___at___Lean_Meta_mkForallFVars_x27_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_MVarId_getDecl(x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Name_isAnonymous(x_11);
lean_dec(x_11);
x_13 = lean_box(x_12);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Name_isAnonymous(x_16);
lean_dec(x_16);
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
return x_8;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_8, 0);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_8);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_1);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_6);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Meta_mkForallFVars_x27_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_2, x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget(x_1, x_2);
x_11 = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___at___Lean_Meta_mkForallFVars_x27_spec__0(x_10, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
if (x_13 == 0)
{
lean_object* x_14; size_t x_15; size_t x_16; 
lean_dec(x_12);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = 1;
x_16 = lean_usize_add(x_2, x_15);
x_2 = x_16;
x_8 = x_14;
goto _start;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_11, 0);
lean_dec(x_19);
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec(x_11);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
return x_11;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_8);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkForallFVars_x27_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_5, x_4);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
x_15 = lean_array_uget(x_3, x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_16 = lean_infer_type(x_15, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_19 = lean_apply_7(x_1, x_17, x_7, x_8, x_9, x_10, x_11, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; size_t x_21; size_t x_22; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = 1;
x_22 = lean_usize_add(x_5, x_21);
lean_inc(x_2);
{
size_t _tmp_4 = x_22;
lean_object* _tmp_5 = x_2;
lean_object* _tmp_11 = x_20;
x_5 = _tmp_4;
x_6 = _tmp_5;
x_12 = _tmp_11;
}
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_19;
}
}
else
{
uint8_t x_24; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars_x27___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_setMVarUserNamesAt(x_2, x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_take(x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Array_append___redArg(x_13, x_10);
lean_dec(x_10);
x_16 = lean_st_ref_set(x_3, x_15, x_14);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_9);
if (x_23 == 0)
{
return x_9;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_9, 0);
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_9);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars_x27___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_st_ref_get(x_1, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_resetMVarUserNames(x_9, x_2, x_3, x_4, x_5, x_10);
lean_dec(x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_get_size(x_1);
x_18 = lean_nat_dec_lt(x_16, x_17);
if (x_18 == 0)
{
lean_dec(x_17);
x_8 = x_18;
x_9 = x_7;
goto block_15;
}
else
{
if (x_18 == 0)
{
lean_dec(x_17);
x_8 = x_18;
x_9 = x_7;
goto block_15;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_21 = l_Array_anyMUnsafe_any___at___Lean_Meta_mkForallFVars_x27_spec__1(x_1, x_19, x_20, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_unbox(x_22);
lean_dec(x_22);
x_8 = x_25;
x_9 = x_24;
goto block_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_41; size_t x_42; lean_object* x_43; 
lean_dec(x_22);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = l_Lean_Meta_setMVarUserNamesAt___closed__0;
x_28 = lean_st_mk_ref(x_27, x_26);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_1);
x_31 = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVars_x27___lam__0___boxed), 8, 1);
lean_closure_set(x_31, 0, x_1);
x_41 = lean_box(0);
x_42 = lean_array_size(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_29);
x_43 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkForallFVars_x27_spec__2(x_31, x_41, x_1, x_42, x_19, x_41, x_29, x_3, x_4, x_5, x_6, x_30);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_45 = l_Lean_Meta_mkForallFVars_x27___lam__0(x_1, x_2, x_29, x_3, x_4, x_5, x_6, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_box(0);
x_48 = lean_box(1);
x_49 = lean_unbox(x_47);
x_50 = lean_unbox(x_48);
x_51 = l_Lean_Meta_mkForallFVars(x_1, x_2, x_49, x_18, x_50, x_3, x_4, x_5, x_6, x_46);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_52);
x_55 = l_Lean_Meta_mkForallFVars_x27___lam__1(x_29, x_3, x_4, x_5, x_6, x_54, x_53);
lean_dec(x_54);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_st_ref_get(x_29, x_56);
lean_dec(x_29);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
lean_ctor_set(x_57, 0, x_52);
return x_57;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_52);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_51, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_51, 1);
lean_inc(x_63);
lean_dec(x_51);
x_32 = x_62;
x_33 = x_63;
goto block_40;
}
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_2);
lean_dec(x_1);
x_64 = lean_ctor_get(x_45, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_45, 1);
lean_inc(x_65);
lean_dec(x_45);
x_32 = x_64;
x_33 = x_65;
goto block_40;
}
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_2);
lean_dec(x_1);
x_66 = lean_ctor_get(x_43, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_43, 1);
lean_inc(x_67);
lean_dec(x_43);
x_32 = x_66;
x_33 = x_67;
goto block_40;
}
block_40:
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_box(0);
x_35 = l_Lean_Meta_mkForallFVars_x27___lam__1(x_29, x_3, x_4, x_5, x_6, x_34, x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_29);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 0, x_32);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
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
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_21);
if (x_68 == 0)
{
return x_21;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_21, 0);
x_70 = lean_ctor_get(x_21, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_21);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
block_15:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_box(1);
x_11 = lean_box(1);
x_12 = lean_unbox(x_10);
x_13 = lean_unbox(x_11);
x_14 = l_Lean_Meta_mkForallFVars(x_1, x_2, x_8, x_12, x_13, x_3, x_4, x_5, x_6, x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___at___Lean_Meta_mkForallFVars_x27_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_shouldInferBinderName___at___Lean_Meta_mkForallFVars_x27_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Meta_mkForallFVars_x27_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = l_Array_anyMUnsafe_any___at___Lean_Meta_mkForallFVars_x27_spec__1(x_1, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkForallFVars_x27_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_mkForallFVars_x27_spec__2(x_1, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars_x27___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_mkForallFVars_x27___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallFVars_x27___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_mkForallFVars_x27___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_MonadCache(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_ForEachExpr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_MonadCache(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_visitLambda___redArg___closed__0 = _init_l_Lean_Meta_visitLambda___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_visitLambda___redArg___closed__0);
l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__5___closed__0 = _init_l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__5___closed__0();
lean_mark_persistent(l_Lean_Meta_forEachExpr_x27_visit___redArg___lam__5___closed__0);
l_Lean_Meta_forEachExpr_x27_visit___redArg___closed__0 = _init_l_Lean_Meta_forEachExpr_x27_visit___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_forEachExpr_x27_visit___redArg___closed__0);
l_Lean_Meta_forEachExpr_x27_visit___redArg___closed__1 = _init_l_Lean_Meta_forEachExpr_x27_visit___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_forEachExpr_x27_visit___redArg___closed__1);
l_Lean_Meta_forEachExpr_x27___redArg___closed__0 = _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_forEachExpr_x27___redArg___closed__0);
l_Lean_Meta_forEachExpr_x27___redArg___closed__1 = _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_forEachExpr_x27___redArg___closed__1);
l_Lean_Meta_forEachExpr_x27___redArg___closed__2 = _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__2();
lean_mark_persistent(l_Lean_Meta_forEachExpr_x27___redArg___closed__2);
l_Lean_Meta_forEachExpr_x27___redArg___closed__3 = _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__3();
lean_mark_persistent(l_Lean_Meta_forEachExpr_x27___redArg___closed__3);
l_Lean_Meta_forEachExpr_x27___redArg___closed__4 = _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__4();
lean_mark_persistent(l_Lean_Meta_forEachExpr_x27___redArg___closed__4);
l_Lean_Meta_forEachExpr_x27___redArg___closed__5 = _init_l_Lean_Meta_forEachExpr_x27___redArg___closed__5();
lean_mark_persistent(l_Lean_Meta_forEachExpr_x27___redArg___closed__5);
l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5___boxed__const__1 = _init_l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5___boxed__const__1();
lean_mark_persistent(l_Lean_Meta_forEachExpr_x27_visit___at___Lean_Meta_forEachExpr_x27___at___Lean_Meta_forEachExpr___at___Lean_Meta_setMVarUserNamesAt_spec__5_spec__5_spec__5___boxed__const__1);
l_Lean_Meta_setMVarUserNamesAt___lam__0___closed__0 = _init_l_Lean_Meta_setMVarUserNamesAt___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_setMVarUserNamesAt___lam__0___closed__0);
l_Lean_Meta_setMVarUserNamesAt___closed__0 = _init_l_Lean_Meta_setMVarUserNamesAt___closed__0();
lean_mark_persistent(l_Lean_Meta_setMVarUserNamesAt___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
