// Lean compiler output
// Module: Init.Lean.AbstractMetavarContext
// Imports: Init.Control.Reader Init.Control.Conditional Init.Data.Option.Default Init.Lean.LocalContext
#include "runtime/lean.h"
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
uint8_t l_PersistentArray_anyMAux___main___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__3(lean_object*, lean_object*);
lean_object* l_PersistentArray_anyMAux___main___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_AssocList_contains___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_isLevelAssigned___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_has_fvar(lean_object*);
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_getMCtx(lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_DependsOn_visit(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_hasAssignedLevelMVar___main___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_localDeclDependsOn___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_getMCtx___boxed(lean_object*, lean_object*);
lean_object* l_mkHashMap___at_Lean_AbstractMetavarContext_exprDependsOn___spec__2(lean_object*);
lean_object* l___private_Init_Lean_Expr_3__withAppRevAux___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__5(lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_panicWithPos___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_letName___closed__1;
lean_object* l_HashMapImp_insert___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ummapAux___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__4(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
extern lean_object* l_Lean_exprIsInhabited;
lean_object* l_HashMapImp_contains___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__1___boxed(lean_object*, lean_object*);
size_t lean_expr_hash(lean_object*);
lean_object* l___private_Init_Lean_Expr_3__withAppRevAux___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_exprDependsOn(lean_object*);
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_visit___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_monadInhabited___rarg(lean_object*, lean_object*);
lean_object* l_HashMapImp_moveEntries___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__6(lean_object*, lean_object*, lean_object*);
uint8_t lean_level_has_mvar(lean_object*);
lean_object* l_HashMapImp_expand___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__4(lean_object*, lean_object*);
uint8_t l_AssocList_contains___main___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__2(lean_object*, lean_object*);
lean_object* lean_expr_mk_let(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_hasAssignedMVar___main(lean_object*);
lean_object* l_StateT_Monad___rarg(lean_object*);
lean_object* l_Lean_AbstractMetavarContext_instantiateLevelMVars___main(lean_object*);
lean_object* l_mkHashMap___at_Lean_AbstractMetavarContext_instantiateMVars___spec__1(lean_object*);
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main(lean_object*);
uint8_t l_PersistentArray_anyM___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__2(lean_object*, lean_object*);
lean_object* l_panicWithPos___at_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___spec__1___rarg___closed__2;
lean_object* l_Lean_AbstractMetavarContext_hasAssignedMVar(lean_object*);
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateLevelMVars(lean_object*);
lean_object* l_Lean_AbstractMetavarContext_exprDependsOn___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_hasAssignedLevelMVar(lean_object*);
lean_object* l_Lean_AbstractMetavarContext_DependsOn_main(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_AbstractMetavarContext_exprDependsOn___rarg___closed__1;
lean_object* l_Lean_AbstractMetavarContext_hasAssignedLevelMVar___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayed___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_DependsOn_dep___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Nat_foldRevAux___main___at_Lean_LocalContext_mkBinding___spec__1___closed__1;
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateLevelMVars___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ummapAux___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_DependsOn_dep___main___rarg___closed__1;
lean_object* l_Lean_mkAppRev(lean_object*, lean_object*);
uint8_t l_List_foldr___main___at_Lean_AbstractMetavarContext_hasAssignedMVar___main___spec__1___rarg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Id_Monad;
lean_object* l_PersistentArray_anyM___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_AssocList_replace___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_panicWithPos___at_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___spec__1(lean_object*);
lean_object* lean_level_update_succ(lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache(lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_isLevelAssigned(lean_object*);
uint8_t l_Lean_AbstractMetavarContext_isExprAssigned___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
uint8_t l_AssocList_contains___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__4(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateForall_x21___closed__1;
extern lean_object* l_panicWithPos___rarg___closed__3;
extern lean_object* l_Lean_Expr_constName___closed__1;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_List_foldr___main___at_Lean_AbstractMetavarContext_hasAssignedMVar___main___spec__1(lean_object*);
extern lean_object* l_Lean_Expr_updateProj_x21___closed__1;
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_hasAssignedLevelMVar___main(lean_object*);
lean_object* l_Lean_LocalContext_findFVar(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_AssocList_replace___main___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__7(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_AbstractMetavarContext_hasAssignedMVar___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_contains___main___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux(lean_object*);
uint8_t l_Lean_AbstractMetavarContext_hasAssignedMVar___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_expr_update_const(lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_instantiateLevelMVars(lean_object*);
lean_object* l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_DependsOn_main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_AbstractMetavarContext_isLevelAssigned___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_hasAssignedMVar___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Array_anyMAux___main___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldr___main___at_Lean_AbstractMetavarContext_hasAssignedMVar___main___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_mkHashSet___at_Lean_AbstractMetavarContext_exprDependsOn___spec__1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_instantiateMVars(lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
extern lean_object* l_panicWithPos___rarg___closed__1;
lean_object* l_HashMapImp_moveEntries___main___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_isExprAssigned(lean_object*);
lean_object* l_Lean_AbstractMetavarContext_instantiateMVars___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___rarg___closed__1;
lean_object* l_AssocList_find___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_visit___boxed(lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_getMCtx___rarg(lean_object*);
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_main(lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_instantiateLevelMVars___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Level_updateSucc_x21___closed__1;
lean_object* l_List_mmap___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_DependsOn_dep___main(lean_object*);
lean_object* l_AssocList_find___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Array_anyMAux___main___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
lean_object* l_panic(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_AbstractMetavarContext_hasAssignedLevelMVar___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_instantiateLevelMVars___main___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Level_updateIMax_x21___closed__1;
lean_object* l_Lean_AbstractMetavarContext_localDeclDependsOn(lean_object*);
extern lean_object* l_Lean_Expr_updateLambda_x21___closed__1;
uint8_t l_Lean_AbstractMetavarContext_hasAssignedLevelMVar___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
extern lean_object* l_HashMap_Inhabited___closed__1;
lean_object* l_Array_anyMAux___main___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__6___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_AbstractMetavarContext_hasAssignedMVar___main___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mmap___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__3(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_AssocList_mfoldl___main___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__6(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayed(lean_object*);
lean_object* l_mkHashMapImp___rarg(lean_object*);
lean_object* l_AssocList_mfoldl___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__7(lean_object*, lean_object*);
lean_object* l_HashMapImp_expand___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_DependsOn_dep___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_expr_mk_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_DependsOn_dep(lean_object*);
lean_object* l_panicWithPos___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__1___closed__1;
extern lean_object* l_panicWithPos___rarg___closed__2;
lean_object* l_panicWithPos___at_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___spec__1___rarg___closed__1;
uint8_t l_HashMapImp_contains___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__1(lean_object*, lean_object*);
extern uint8_t l_Bool_Inhabited;
lean_object* lean_level_update_max(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_has_expr_mvar(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateMData_x21___closed__1;
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_instantiateMVars___rarg___closed__1;
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at_Lean_Expr_bindingDomain___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_sort(lean_object*, lean_object*);
lean_object* l_panicWithPos___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__2(lean_object*);
lean_object* l_panicWithPos___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main(lean_object*);
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_visit(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_isExprAssigned___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMAux___main___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__1(lean_object*);
uint8_t l_Array_anyMAux___main___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at_Lean_Level_updateSucc_x21___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panicWithPos___at_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_has_level_mvar(lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Lean_LocalDecl_name(lean_object*);
uint8_t l_Lean_AbstractMetavarContext_isLevelAssigned___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_4, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 1;
return x_7;
}
}
}
lean_object* l_Lean_AbstractMetavarContext_isLevelAssigned(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_AbstractMetavarContext_isLevelAssigned___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_AbstractMetavarContext_isLevelAssigned___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_AbstractMetavarContext_isLevelAssigned___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
uint8_t l_Lean_AbstractMetavarContext_isExprAssigned___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 5);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_4, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 1;
return x_7;
}
}
}
lean_object* l_Lean_AbstractMetavarContext_isExprAssigned(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_AbstractMetavarContext_isExprAssigned___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_AbstractMetavarContext_isExprAssigned___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_AbstractMetavarContext_isExprAssigned___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
uint8_t l_Lean_AbstractMetavarContext_hasAssignedLevelMVar___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
lean_inc(x_4);
x_5 = lean_level_has_mvar(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_6 = 0;
return x_6;
}
else
{
x_3 = x_4;
goto _start;
}
}
case 2:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
lean_inc(x_8);
x_10 = lean_level_has_mvar(x_8);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_8);
lean_inc(x_9);
x_11 = lean_level_has_mvar(x_9);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_12 = 0;
return x_12;
}
else
{
x_3 = x_9;
goto _start;
}
}
else
{
uint8_t x_14; 
lean_inc(x_2);
lean_inc(x_1);
x_14 = l_Lean_AbstractMetavarContext_hasAssignedLevelMVar___main___rarg(x_1, x_2, x_8);
if (x_14 == 0)
{
uint8_t x_15; 
lean_inc(x_9);
x_15 = lean_level_has_mvar(x_9);
if (x_15 == 0)
{
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
else
{
x_3 = x_9;
goto _start;
}
}
else
{
uint8_t x_17; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_17 = 1;
return x_17;
}
}
}
case 3:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
lean_dec(x_3);
lean_inc(x_18);
x_20 = lean_level_has_mvar(x_18);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_18);
lean_inc(x_19);
x_21 = lean_level_has_mvar(x_19);
if (x_21 == 0)
{
uint8_t x_22; 
lean_dec(x_19);
lean_dec(x_2);
lean_dec(x_1);
x_22 = 0;
return x_22;
}
else
{
x_3 = x_19;
goto _start;
}
}
else
{
uint8_t x_24; 
lean_inc(x_2);
lean_inc(x_1);
x_24 = l_Lean_AbstractMetavarContext_hasAssignedLevelMVar___main___rarg(x_1, x_2, x_18);
if (x_24 == 0)
{
uint8_t x_25; 
lean_inc(x_19);
x_25 = lean_level_has_mvar(x_19);
if (x_25 == 0)
{
lean_dec(x_19);
lean_dec(x_2);
lean_dec(x_1);
return x_24;
}
else
{
x_3 = x_19;
goto _start;
}
}
else
{
uint8_t x_27; 
lean_dec(x_19);
lean_dec(x_2);
lean_dec(x_1);
x_27 = 1;
return x_27;
}
}
}
case 5:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
lean_dec(x_3);
x_29 = lean_ctor_get(x_1, 2);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_apply_2(x_29, x_2, x_28);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = 0;
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_30);
x_32 = 1;
return x_32;
}
}
default: 
{
uint8_t x_33; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = 0;
return x_33;
}
}
}
}
lean_object* l_Lean_AbstractMetavarContext_hasAssignedLevelMVar___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_AbstractMetavarContext_hasAssignedLevelMVar___main___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_AbstractMetavarContext_hasAssignedLevelMVar___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_AbstractMetavarContext_hasAssignedLevelMVar___main___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
uint8_t l_Lean_AbstractMetavarContext_hasAssignedLevelMVar___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_AbstractMetavarContext_hasAssignedLevelMVar___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_AbstractMetavarContext_hasAssignedLevelMVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_AbstractMetavarContext_hasAssignedLevelMVar___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_AbstractMetavarContext_hasAssignedLevelMVar___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_AbstractMetavarContext_hasAssignedLevelMVar___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
uint8_t l_List_foldr___main___at_Lean_AbstractMetavarContext_hasAssignedMVar___main___spec__1___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
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
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_List_foldr___main___at_Lean_AbstractMetavarContext_hasAssignedMVar___main___spec__1___rarg(x_1, x_2, x_3, x_6);
x_8 = l_Lean_AbstractMetavarContext_hasAssignedLevelMVar___main___rarg(x_1, x_2, x_5);
if (x_8 == 0)
{
return x_7;
}
else
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
}
}
}
lean_object* l_List_foldr___main___at_Lean_AbstractMetavarContext_hasAssignedMVar___main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldr___main___at_Lean_AbstractMetavarContext_hasAssignedMVar___main___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
uint8_t l_Lean_AbstractMetavarContext_hasAssignedMVar___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 2:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 5);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_5, x_2, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_6);
x_8 = 1;
return x_8;
}
}
case 3:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l_Lean_AbstractMetavarContext_hasAssignedLevelMVar___main___rarg(x_1, x_2, x_9);
return x_10;
}
case 4:
{
lean_object* x_11; uint8_t x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_dec(x_3);
x_12 = 0;
x_13 = l_List_foldr___main___at_Lean_AbstractMetavarContext_hasAssignedMVar___main___spec__1___rarg(x_1, x_2, x_12, x_11);
return x_13;
}
case 5:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_dec(x_3);
x_16 = lean_expr_has_expr_mvar(x_14);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = lean_expr_has_level_mvar(x_14);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_14);
x_18 = lean_expr_has_expr_mvar(x_15);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = lean_expr_has_level_mvar(x_15);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_20 = 0;
return x_20;
}
else
{
x_3 = x_15;
goto _start;
}
}
else
{
x_3 = x_15;
goto _start;
}
}
else
{
uint8_t x_23; 
lean_inc(x_2);
lean_inc(x_1);
x_23 = l_Lean_AbstractMetavarContext_hasAssignedMVar___main___rarg(x_1, x_2, x_14);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = lean_expr_has_expr_mvar(x_15);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = lean_expr_has_level_mvar(x_15);
if (x_25 == 0)
{
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
return x_23;
}
else
{
x_3 = x_15;
goto _start;
}
}
else
{
x_3 = x_15;
goto _start;
}
}
else
{
uint8_t x_28; 
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_28 = 1;
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_inc(x_2);
lean_inc(x_1);
x_29 = l_Lean_AbstractMetavarContext_hasAssignedMVar___main___rarg(x_1, x_2, x_14);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = lean_expr_has_expr_mvar(x_15);
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = lean_expr_has_level_mvar(x_15);
if (x_31 == 0)
{
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
return x_29;
}
else
{
x_3 = x_15;
goto _start;
}
}
else
{
x_3 = x_15;
goto _start;
}
}
else
{
uint8_t x_34; 
lean_dec(x_15);
lean_dec(x_2);
lean_dec(x_1);
x_34 = 1;
return x_34;
}
}
}
case 6:
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_3, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_3, 2);
lean_inc(x_36);
lean_dec(x_3);
x_37 = lean_expr_has_expr_mvar(x_35);
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = lean_expr_has_level_mvar(x_35);
if (x_38 == 0)
{
uint8_t x_39; 
lean_dec(x_35);
x_39 = lean_expr_has_expr_mvar(x_36);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = lean_expr_has_level_mvar(x_36);
if (x_40 == 0)
{
uint8_t x_41; 
lean_dec(x_36);
lean_dec(x_2);
lean_dec(x_1);
x_41 = 0;
return x_41;
}
else
{
x_3 = x_36;
goto _start;
}
}
else
{
x_3 = x_36;
goto _start;
}
}
else
{
uint8_t x_44; 
lean_inc(x_2);
lean_inc(x_1);
x_44 = l_Lean_AbstractMetavarContext_hasAssignedMVar___main___rarg(x_1, x_2, x_35);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = lean_expr_has_expr_mvar(x_36);
if (x_45 == 0)
{
uint8_t x_46; 
x_46 = lean_expr_has_level_mvar(x_36);
if (x_46 == 0)
{
lean_dec(x_36);
lean_dec(x_2);
lean_dec(x_1);
return x_44;
}
else
{
x_3 = x_36;
goto _start;
}
}
else
{
x_3 = x_36;
goto _start;
}
}
else
{
uint8_t x_49; 
lean_dec(x_36);
lean_dec(x_2);
lean_dec(x_1);
x_49 = 1;
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_inc(x_2);
lean_inc(x_1);
x_50 = l_Lean_AbstractMetavarContext_hasAssignedMVar___main___rarg(x_1, x_2, x_35);
if (x_50 == 0)
{
uint8_t x_51; 
x_51 = lean_expr_has_expr_mvar(x_36);
if (x_51 == 0)
{
uint8_t x_52; 
x_52 = lean_expr_has_level_mvar(x_36);
if (x_52 == 0)
{
lean_dec(x_36);
lean_dec(x_2);
lean_dec(x_1);
return x_50;
}
else
{
x_3 = x_36;
goto _start;
}
}
else
{
x_3 = x_36;
goto _start;
}
}
else
{
uint8_t x_55; 
lean_dec(x_36);
lean_dec(x_2);
lean_dec(x_1);
x_55 = 1;
return x_55;
}
}
}
case 7:
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_3, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_3, 2);
lean_inc(x_57);
lean_dec(x_3);
x_58 = lean_expr_has_expr_mvar(x_56);
if (x_58 == 0)
{
uint8_t x_59; 
x_59 = lean_expr_has_level_mvar(x_56);
if (x_59 == 0)
{
uint8_t x_60; 
lean_dec(x_56);
x_60 = lean_expr_has_expr_mvar(x_57);
if (x_60 == 0)
{
uint8_t x_61; 
x_61 = lean_expr_has_level_mvar(x_57);
if (x_61 == 0)
{
uint8_t x_62; 
lean_dec(x_57);
lean_dec(x_2);
lean_dec(x_1);
x_62 = 0;
return x_62;
}
else
{
x_3 = x_57;
goto _start;
}
}
else
{
x_3 = x_57;
goto _start;
}
}
else
{
uint8_t x_65; 
lean_inc(x_2);
lean_inc(x_1);
x_65 = l_Lean_AbstractMetavarContext_hasAssignedMVar___main___rarg(x_1, x_2, x_56);
if (x_65 == 0)
{
uint8_t x_66; 
x_66 = lean_expr_has_expr_mvar(x_57);
if (x_66 == 0)
{
uint8_t x_67; 
x_67 = lean_expr_has_level_mvar(x_57);
if (x_67 == 0)
{
lean_dec(x_57);
lean_dec(x_2);
lean_dec(x_1);
return x_65;
}
else
{
x_3 = x_57;
goto _start;
}
}
else
{
x_3 = x_57;
goto _start;
}
}
else
{
uint8_t x_70; 
lean_dec(x_57);
lean_dec(x_2);
lean_dec(x_1);
x_70 = 1;
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_inc(x_2);
lean_inc(x_1);
x_71 = l_Lean_AbstractMetavarContext_hasAssignedMVar___main___rarg(x_1, x_2, x_56);
if (x_71 == 0)
{
uint8_t x_72; 
x_72 = lean_expr_has_expr_mvar(x_57);
if (x_72 == 0)
{
uint8_t x_73; 
x_73 = lean_expr_has_level_mvar(x_57);
if (x_73 == 0)
{
lean_dec(x_57);
lean_dec(x_2);
lean_dec(x_1);
return x_71;
}
else
{
x_3 = x_57;
goto _start;
}
}
else
{
x_3 = x_57;
goto _start;
}
}
else
{
uint8_t x_76; 
lean_dec(x_57);
lean_dec(x_2);
lean_dec(x_1);
x_76 = 1;
return x_76;
}
}
}
case 8:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_101; 
x_77 = lean_ctor_get(x_3, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_3, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_3, 3);
lean_inc(x_79);
lean_dec(x_3);
x_101 = lean_expr_has_expr_mvar(x_77);
if (x_101 == 0)
{
uint8_t x_102; 
x_102 = lean_expr_has_level_mvar(x_77);
if (x_102 == 0)
{
uint8_t x_103; 
lean_dec(x_77);
x_103 = 0;
x_80 = x_103;
goto block_100;
}
else
{
uint8_t x_104; 
lean_inc(x_2);
lean_inc(x_1);
x_104 = l_Lean_AbstractMetavarContext_hasAssignedMVar___main___rarg(x_1, x_2, x_77);
if (x_104 == 0)
{
x_80 = x_104;
goto block_100;
}
else
{
uint8_t x_105; 
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_2);
lean_dec(x_1);
x_105 = 1;
return x_105;
}
}
}
else
{
uint8_t x_106; 
lean_inc(x_2);
lean_inc(x_1);
x_106 = l_Lean_AbstractMetavarContext_hasAssignedMVar___main___rarg(x_1, x_2, x_77);
if (x_106 == 0)
{
x_80 = x_106;
goto block_100;
}
else
{
uint8_t x_107; 
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_2);
lean_dec(x_1);
x_107 = 1;
return x_107;
}
}
block_100:
{
uint8_t x_81; 
x_81 = lean_expr_has_expr_mvar(x_78);
if (x_81 == 0)
{
uint8_t x_82; 
x_82 = lean_expr_has_level_mvar(x_78);
if (x_82 == 0)
{
lean_dec(x_78);
if (x_80 == 0)
{
uint8_t x_83; 
x_83 = lean_expr_has_expr_mvar(x_79);
if (x_83 == 0)
{
uint8_t x_84; 
x_84 = lean_expr_has_level_mvar(x_79);
if (x_84 == 0)
{
lean_dec(x_79);
lean_dec(x_2);
lean_dec(x_1);
return x_80;
}
else
{
x_3 = x_79;
goto _start;
}
}
else
{
x_3 = x_79;
goto _start;
}
}
else
{
uint8_t x_87; 
lean_dec(x_79);
lean_dec(x_2);
lean_dec(x_1);
x_87 = 1;
return x_87;
}
}
else
{
uint8_t x_88; 
lean_inc(x_2);
lean_inc(x_1);
x_88 = l_Lean_AbstractMetavarContext_hasAssignedMVar___main___rarg(x_1, x_2, x_78);
if (x_88 == 0)
{
uint8_t x_89; 
x_89 = lean_expr_has_expr_mvar(x_79);
if (x_89 == 0)
{
uint8_t x_90; 
x_90 = lean_expr_has_level_mvar(x_79);
if (x_90 == 0)
{
lean_dec(x_79);
lean_dec(x_2);
lean_dec(x_1);
return x_88;
}
else
{
x_3 = x_79;
goto _start;
}
}
else
{
x_3 = x_79;
goto _start;
}
}
else
{
uint8_t x_93; 
lean_dec(x_79);
lean_dec(x_2);
lean_dec(x_1);
x_93 = 1;
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_inc(x_2);
lean_inc(x_1);
x_94 = l_Lean_AbstractMetavarContext_hasAssignedMVar___main___rarg(x_1, x_2, x_78);
if (x_94 == 0)
{
uint8_t x_95; 
x_95 = lean_expr_has_expr_mvar(x_79);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = lean_expr_has_level_mvar(x_79);
if (x_96 == 0)
{
lean_dec(x_79);
lean_dec(x_2);
lean_dec(x_1);
return x_94;
}
else
{
x_3 = x_79;
goto _start;
}
}
else
{
x_3 = x_79;
goto _start;
}
}
else
{
uint8_t x_99; 
lean_dec(x_79);
lean_dec(x_2);
lean_dec(x_1);
x_99 = 1;
return x_99;
}
}
}
}
case 10:
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_ctor_get(x_3, 1);
lean_inc(x_108);
lean_dec(x_3);
x_109 = lean_expr_has_expr_mvar(x_108);
if (x_109 == 0)
{
uint8_t x_110; 
x_110 = lean_expr_has_level_mvar(x_108);
if (x_110 == 0)
{
uint8_t x_111; 
lean_dec(x_108);
lean_dec(x_2);
lean_dec(x_1);
x_111 = 0;
return x_111;
}
else
{
x_3 = x_108;
goto _start;
}
}
else
{
x_3 = x_108;
goto _start;
}
}
case 11:
{
lean_object* x_114; uint8_t x_115; 
x_114 = lean_ctor_get(x_3, 2);
lean_inc(x_114);
lean_dec(x_3);
x_115 = lean_expr_has_expr_mvar(x_114);
if (x_115 == 0)
{
uint8_t x_116; 
x_116 = lean_expr_has_level_mvar(x_114);
if (x_116 == 0)
{
uint8_t x_117; 
lean_dec(x_114);
lean_dec(x_2);
lean_dec(x_1);
x_117 = 0;
return x_117;
}
else
{
x_3 = x_114;
goto _start;
}
}
else
{
x_3 = x_114;
goto _start;
}
}
default: 
{
uint8_t x_120; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_120 = 0;
return x_120;
}
}
}
}
lean_object* l_Lean_AbstractMetavarContext_hasAssignedMVar___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_AbstractMetavarContext_hasAssignedMVar___main___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_List_foldr___main___at_Lean_AbstractMetavarContext_hasAssignedMVar___main___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_List_foldr___main___at_Lean_AbstractMetavarContext_hasAssignedMVar___main___spec__1___rarg(x_1, x_2, x_5, x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_AbstractMetavarContext_hasAssignedMVar___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_AbstractMetavarContext_hasAssignedMVar___main___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
uint8_t l_Lean_AbstractMetavarContext_hasAssignedMVar___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_AbstractMetavarContext_hasAssignedMVar___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_AbstractMetavarContext_hasAssignedMVar(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_AbstractMetavarContext_hasAssignedMVar___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_AbstractMetavarContext_hasAssignedMVar___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_AbstractMetavarContext_hasAssignedMVar___rarg(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Lean_AbstractMetavarContext_instantiateLevelMVars___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = l_Lean_AbstractMetavarContext_instantiateLevelMVars___main___rarg(x_1, x_4, x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_level_update_succ(x_2, x_7);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = lean_level_update_succ(x_2, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
case 2:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_inc(x_1);
x_15 = l_Lean_AbstractMetavarContext_instantiateLevelMVars___main___rarg(x_1, x_13, x_3);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_AbstractMetavarContext_instantiateLevelMVars___main___rarg(x_1, x_14, x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_level_update_max(x_2, x_16, x_20);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_18);
x_24 = lean_level_update_max(x_2, x_16, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
case 3:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
lean_dec(x_2);
lean_inc(x_1);
x_28 = l_Lean_AbstractMetavarContext_instantiateLevelMVars___main___rarg(x_1, x_26, x_3);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_AbstractMetavarContext_instantiateLevelMVars___main___rarg(x_1, x_27, x_29);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
x_33 = l_Lean_Level_updateSucc_x21___closed__1;
x_34 = lean_unsigned_to_nat(218u);
x_35 = lean_unsigned_to_nat(17u);
x_36 = l_Lean_Level_updateIMax_x21___closed__1;
x_37 = l_panicWithPos___at_Lean_Level_updateSucc_x21___spec__1(x_33, x_34, x_35, x_36);
lean_ctor_set(x_30, 0, x_37);
return x_30;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
lean_dec(x_30);
x_39 = l_Lean_Level_updateSucc_x21___closed__1;
x_40 = lean_unsigned_to_nat(218u);
x_41 = lean_unsigned_to_nat(17u);
x_42 = l_Lean_Level_updateIMax_x21___closed__1;
x_43 = l_panicWithPos___at_Lean_Level_updateSucc_x21___spec__1(x_39, x_40, x_41, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_38);
return x_44;
}
}
case 5:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_2, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_1, 2);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_3);
x_47 = lean_apply_2(x_46, x_3, x_45);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
lean_dec(x_45);
lean_dec(x_1);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_2);
lean_ctor_set(x_48, 1, x_3);
return x_48;
}
else
{
lean_object* x_49; uint8_t x_50; 
lean_dec(x_2);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_49);
x_50 = lean_level_has_mvar(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_45);
lean_dec(x_1);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_3);
return x_51;
}
else
{
lean_object* x_52; uint8_t x_53; 
lean_inc(x_1);
x_52 = l_Lean_AbstractMetavarContext_instantiateLevelMVars___main___rarg(x_1, x_49, x_3);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_52, 1);
x_56 = lean_ctor_get(x_1, 3);
lean_inc(x_56);
lean_dec(x_1);
lean_inc(x_54);
x_57 = lean_apply_3(x_56, x_55, x_45, x_54);
lean_ctor_set(x_52, 1, x_57);
return x_52;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_52, 0);
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_52);
x_60 = lean_ctor_get(x_1, 3);
lean_inc(x_60);
lean_dec(x_1);
lean_inc(x_58);
x_61 = lean_apply_3(x_60, x_59, x_45, x_58);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
default: 
{
lean_object* x_63; 
lean_dec(x_1);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_2);
lean_ctor_set(x_63, 1, x_3);
return x_63;
}
}
}
}
lean_object* l_Lean_AbstractMetavarContext_instantiateLevelMVars___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_AbstractMetavarContext_instantiateLevelMVars___main___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_AbstractMetavarContext_instantiateLevelMVars___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_AbstractMetavarContext_instantiateLevelMVars___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_AbstractMetavarContext_instantiateLevelMVars(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_AbstractMetavarContext_instantiateLevelMVars___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateLevelMVars___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lean_AbstractMetavarContext_instantiateLevelMVars___main___rarg(x_1, x_2, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 1);
lean_ctor_set(x_3, 0, x_8);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_10);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = l_Lean_AbstractMetavarContext_instantiateLevelMVars___main___rarg(x_1, x_2, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_17 = x_14;
} else {
 lean_dec_ref(x_14);
 x_17 = lean_box(0);
}
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_13);
if (lean_is_scalar(x_17)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_17;
}
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateLevelMVars(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateLevelMVars___rarg), 3, 0);
return x_2;
}
}
lean_object* l_AssocList_find___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_expr_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_find___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
uint8_t l_AssocList_contains___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_expr_eqv(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
lean_object* l_AssocList_mfoldl___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = lean_expr_hash(x_4);
x_8 = lean_usize_modn(x_7, x_6);
lean_dec(x_6);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = lean_expr_hash(x_12);
x_17 = lean_usize_modn(x_16, x_15);
lean_dec(x_15);
x_18 = lean_array_uget(x_1, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_uset(x_1, x_17, x_19);
x_1 = x_20;
x_2 = x_14;
goto _start;
}
}
}
}
lean_object* l_HashMapImp_moveEntries___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_AssocList_mfoldl___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__7(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
lean_object* l_HashMapImp_expand___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_HashMapImp_moveEntries___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__6(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_AssocList_replace___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__8(x_1, x_2, x_7);
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
x_14 = l_AssocList_replace___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__8(x_1, x_2, x_12);
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
lean_object* l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_expr_hash(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_AssocList_contains___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__4(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_6, x_9, x_14);
x_16 = lean_nat_dec_le(x_13, x_7);
lean_dec(x_7);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_1);
x_17 = l_HashMapImp_expand___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__5(x_13, x_15);
return x_17;
}
else
{
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_18 = l_AssocList_replace___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__8(x_2, x_3, x_10);
x_19 = lean_array_uset(x_6, x_9, x_18);
lean_ctor_set(x_1, 1, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_22 = lean_array_get_size(x_21);
x_23 = lean_expr_hash(x_2);
x_24 = lean_usize_modn(x_23, x_22);
x_25 = lean_array_uget(x_21, x_24);
x_26 = l_AssocList_contains___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__4(x_2, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_20, x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 2, x_25);
x_30 = lean_array_uset(x_21, x_24, x_29);
x_31 = lean_nat_dec_le(x_28, x_22);
lean_dec(x_22);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_HashMapImp_expand___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__5(x_28, x_30);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_22);
x_34 = l_AssocList_replace___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__8(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_4, x_1);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; 
lean_inc(x_1);
x_6 = lean_apply_2(x_2, x_1, x_3);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_12 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_11, x_1, x_10);
lean_ctor_set(x_8, 1, x_12);
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
lean_inc(x_13);
x_16 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_15, x_1, x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_6, 1, x_17);
return x_6;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_6, 1);
x_19 = lean_ctor_get(x_6, 0);
lean_inc(x_18);
lean_inc(x_19);
lean_dec(x_6);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_22 = x_18;
} else {
 lean_dec_ref(x_18);
 x_22 = lean_box(0);
}
lean_inc(x_19);
x_23 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_21, x_1, x_19);
if (lean_is_scalar(x_22)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_22;
}
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_ctor_get(x_5, 0);
lean_inc(x_26);
lean_dec(x_5);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_3);
return x_27;
}
}
}
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___rarg), 3, 0);
return x_3;
}
}
lean_object* l_AssocList_find___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_AssocList_find___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_AssocList_contains___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_visit___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_expr_has_expr_mvar(x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = lean_expr_has_level_mvar(x_2);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_8 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_7, x_2);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; 
lean_inc(x_2);
x_9 = lean_apply_2(x_1, x_2, x_3);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
x_15 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_14, x_2, x_13);
lean_ctor_set(x_11, 1, x_15);
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
lean_inc(x_16);
x_19 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_18, x_2, x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_9, 1, x_20);
return x_9;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_9, 1);
x_22 = lean_ctor_get(x_9, 0);
lean_inc(x_21);
lean_inc(x_22);
lean_dec(x_9);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_25 = x_21;
} else {
 lean_dec_ref(x_21);
 x_25 = lean_box(0);
}
lean_inc(x_22);
x_26 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_24, x_2, x_22);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_2);
lean_dec(x_1);
x_29 = lean_ctor_get(x_8, 0);
lean_inc(x_29);
lean_dec(x_8);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_3);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_3, 1);
lean_inc(x_31);
x_32 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_31, x_2);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; 
lean_inc(x_2);
x_33 = lean_apply_2(x_1, x_2, x_3);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_33, 1);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 0);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
x_39 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_38, x_2, x_37);
lean_ctor_set(x_35, 1, x_39);
return x_33;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_33, 0);
x_41 = lean_ctor_get(x_35, 0);
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_35);
lean_inc(x_40);
x_43 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_42, x_2, x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_33, 1, x_44);
return x_33;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_45 = lean_ctor_get(x_33, 1);
x_46 = lean_ctor_get(x_33, 0);
lean_inc(x_45);
lean_inc(x_46);
lean_dec(x_33);
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
lean_inc(x_46);
x_50 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_48, x_2, x_46);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_46);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_2);
lean_dec(x_1);
x_53 = lean_ctor_get(x_32, 0);
lean_inc(x_53);
lean_dec(x_32);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_3);
return x_54;
}
}
}
}
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_visit(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_AbstractMetavarContext_InstantiateExprMVars_visit___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_visit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_visit(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_getMCtx___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_getMCtx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_AbstractMetavarContext_InstantiateExprMVars_getMCtx___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_getMCtx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_getMCtx(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* _init_l_panicWithPos___at_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___spec__1___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Id_Monad;
x_2 = l_StateT_Monad___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_panicWithPos___at_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___spec__1___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_panicWithPos___at_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___spec__1___rarg___closed__1;
x_3 = l_monadInhabited___rarg(x_2, x_1);
return x_3;
}
}
lean_object* l_panicWithPos___at_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = l_panicWithPos___rarg___closed__1;
x_7 = lean_string_append(x_6, x_1);
x_8 = l_panicWithPos___rarg___closed__2;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_Nat_repr(x_2);
x_11 = lean_string_append(x_9, x_10);
lean_dec(x_10);
x_12 = l_panicWithPos___rarg___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_Nat_repr(x_3);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = l_panicWithPos___rarg___closed__3;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_string_append(x_17, x_4);
x_19 = l_panicWithPos___at_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___spec__1___rarg___closed__2;
x_20 = lean_panic_fn(x_18);
x_21 = lean_apply_1(x_20, x_5);
return x_21;
}
}
lean_object* l_panicWithPos___at_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_panicWithPos___at_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* _init_l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Init.Lean.AbstractMetavarContext");
return x_1;
}
}
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_5, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_5, x_10);
lean_dec(x_5);
x_12 = l_Lean_exprIsInhabited;
x_13 = lean_array_get(x_12, x_4, x_11);
lean_inc(x_3);
x_14 = l_Lean_LocalContext_findFVar(x_3, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_15 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___rarg___closed__1;
x_16 = lean_unsigned_to_nat(193u);
x_17 = lean_unsigned_to_nat(12u);
x_18 = l_Nat_foldRevAux___main___at_Lean_LocalContext_mkBinding___spec__1___closed__1;
x_19 = l_panicWithPos___at_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___spec__1___rarg(x_15, x_16, x_17, x_18, x_7);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
lean_dec(x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; uint8_t x_36; 
x_21 = lean_ctor_get(x_20, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 3);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_20, sizeof(void*)*4);
lean_dec(x_20);
x_36 = lean_expr_has_expr_mvar(x_22);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = lean_expr_has_level_mvar(x_22);
if (x_37 == 0)
{
x_24 = x_22;
x_25 = x_7;
goto block_35;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_7, 1);
lean_inc(x_38);
x_39 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_38, x_22);
lean_dec(x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_inc(x_2);
lean_inc(x_22);
x_40 = lean_apply_2(x_2, x_22, x_7);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
x_43 = !lean_is_exclusive(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
x_45 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_44, x_22, x_42);
lean_ctor_set(x_41, 1, x_45);
x_24 = x_42;
x_25 = x_41;
goto block_35;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_41, 0);
x_47 = lean_ctor_get(x_41, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_41);
lean_inc(x_42);
x_48 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_47, x_22, x_42);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
x_24 = x_42;
x_25 = x_49;
goto block_35;
}
}
else
{
lean_object* x_50; 
lean_dec(x_22);
x_50 = lean_ctor_get(x_39, 0);
lean_inc(x_50);
lean_dec(x_39);
x_24 = x_50;
x_25 = x_7;
goto block_35;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_7, 1);
lean_inc(x_51);
x_52 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_51, x_22);
lean_dec(x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_inc(x_2);
lean_inc(x_22);
x_53 = lean_apply_2(x_2, x_22, x_7);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
lean_dec(x_53);
x_56 = !lean_is_exclusive(x_54);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
x_58 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_57, x_22, x_55);
lean_ctor_set(x_54, 1, x_58);
x_24 = x_55;
x_25 = x_54;
goto block_35;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_54, 0);
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_54);
lean_inc(x_55);
x_61 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_60, x_22, x_55);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_61);
x_24 = x_55;
x_25 = x_62;
goto block_35;
}
}
else
{
lean_object* x_63; 
lean_dec(x_22);
x_63 = lean_ctor_get(x_52, 0);
lean_inc(x_63);
lean_dec(x_52);
x_24 = x_63;
x_25 = x_7;
goto block_35;
}
}
block_35:
{
uint8_t x_26; 
x_26 = lean_expr_has_expr_mvar(x_24);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = lean_expr_has_level_mvar(x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_expr_abstract_range(x_24, x_11, x_4);
lean_dec(x_24);
x_29 = lean_expr_mk_lambda(x_21, x_23, x_28, x_6);
x_5 = x_11;
x_6 = x_29;
x_7 = x_25;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_25);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_25);
return x_34;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_117; 
x_64 = lean_ctor_get(x_20, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_20, 3);
lean_inc(x_65);
x_66 = lean_ctor_get(x_20, 4);
lean_inc(x_66);
lean_dec(x_20);
x_117 = lean_expr_has_expr_mvar(x_65);
if (x_117 == 0)
{
uint8_t x_118; 
x_118 = lean_expr_has_level_mvar(x_65);
if (x_118 == 0)
{
x_67 = x_65;
x_68 = x_7;
goto block_116;
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_7, 1);
lean_inc(x_119);
x_120 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_119, x_65);
lean_dec(x_119);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
lean_inc(x_2);
lean_inc(x_65);
x_121 = lean_apply_2(x_2, x_65, x_7);
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 0);
lean_inc(x_123);
lean_dec(x_121);
x_124 = !lean_is_exclusive(x_122);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
x_126 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_125, x_65, x_123);
lean_ctor_set(x_122, 1, x_126);
x_67 = x_123;
x_68 = x_122;
goto block_116;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_122, 0);
x_128 = lean_ctor_get(x_122, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_122);
lean_inc(x_123);
x_129 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_128, x_65, x_123);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_129);
x_67 = x_123;
x_68 = x_130;
goto block_116;
}
}
else
{
lean_object* x_131; 
lean_dec(x_65);
x_131 = lean_ctor_get(x_120, 0);
lean_inc(x_131);
lean_dec(x_120);
x_67 = x_131;
x_68 = x_7;
goto block_116;
}
}
}
else
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_7, 1);
lean_inc(x_132);
x_133 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_132, x_65);
lean_dec(x_132);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
lean_inc(x_2);
lean_inc(x_65);
x_134 = lean_apply_2(x_2, x_65, x_7);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 0);
lean_inc(x_136);
lean_dec(x_134);
x_137 = !lean_is_exclusive(x_135);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
x_139 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_138, x_65, x_136);
lean_ctor_set(x_135, 1, x_139);
x_67 = x_136;
x_68 = x_135;
goto block_116;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_140 = lean_ctor_get(x_135, 0);
x_141 = lean_ctor_get(x_135, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_135);
lean_inc(x_136);
x_142 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_141, x_65, x_136);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_142);
x_67 = x_136;
x_68 = x_143;
goto block_116;
}
}
else
{
lean_object* x_144; 
lean_dec(x_65);
x_144 = lean_ctor_get(x_133, 0);
lean_inc(x_144);
lean_dec(x_133);
x_67 = x_144;
x_68 = x_7;
goto block_116;
}
}
block_116:
{
lean_object* x_69; lean_object* x_70; uint8_t x_82; 
x_82 = lean_expr_has_expr_mvar(x_67);
if (x_82 == 0)
{
uint8_t x_83; 
x_83 = lean_expr_has_level_mvar(x_67);
if (x_83 == 0)
{
uint8_t x_84; 
x_84 = lean_expr_has_expr_mvar(x_66);
if (x_84 == 0)
{
uint8_t x_85; 
x_85 = lean_expr_has_level_mvar(x_66);
if (x_85 == 0)
{
x_69 = x_66;
x_70 = x_68;
goto block_81;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_68, 1);
lean_inc(x_86);
x_87 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_86, x_66);
lean_dec(x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
lean_inc(x_2);
lean_inc(x_66);
x_88 = lean_apply_2(x_2, x_66, x_68);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 0);
lean_inc(x_90);
lean_dec(x_88);
x_91 = !lean_is_exclusive(x_89);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
x_93 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_92, x_66, x_90);
lean_ctor_set(x_89, 1, x_93);
x_69 = x_90;
x_70 = x_89;
goto block_81;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_89, 0);
x_95 = lean_ctor_get(x_89, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_89);
lean_inc(x_90);
x_96 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_95, x_66, x_90);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_96);
x_69 = x_90;
x_70 = x_97;
goto block_81;
}
}
else
{
lean_object* x_98; 
lean_dec(x_66);
x_98 = lean_ctor_get(x_87, 0);
lean_inc(x_98);
lean_dec(x_87);
x_69 = x_98;
x_70 = x_68;
goto block_81;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_68, 1);
lean_inc(x_99);
x_100 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_99, x_66);
lean_dec(x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
lean_inc(x_2);
lean_inc(x_66);
x_101 = lean_apply_2(x_2, x_66, x_68);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_103);
lean_dec(x_101);
x_104 = !lean_is_exclusive(x_102);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
x_106 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_105, x_66, x_103);
lean_ctor_set(x_102, 1, x_106);
x_69 = x_103;
x_70 = x_102;
goto block_81;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = lean_ctor_get(x_102, 0);
x_108 = lean_ctor_get(x_102, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_102);
lean_inc(x_103);
x_109 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_108, x_66, x_103);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_109);
x_69 = x_103;
x_70 = x_110;
goto block_81;
}
}
else
{
lean_object* x_111; 
lean_dec(x_66);
x_111 = lean_ctor_get(x_100, 0);
lean_inc(x_111);
lean_dec(x_100);
x_69 = x_111;
x_70 = x_68;
goto block_81;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_112 = lean_box(0);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_68);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_114 = lean_box(0);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_68);
return x_115;
}
block_81:
{
uint8_t x_71; 
x_71 = lean_expr_has_expr_mvar(x_69);
if (x_71 == 0)
{
uint8_t x_72; 
x_72 = lean_expr_has_level_mvar(x_69);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_expr_abstract_range(x_67, x_11, x_4);
lean_dec(x_67);
x_74 = lean_expr_abstract_range(x_69, x_11, x_4);
lean_dec(x_69);
x_75 = lean_expr_mk_let(x_64, x_73, x_74, x_6);
x_5 = x_11;
x_6 = x_75;
x_7 = x_70;
goto _start;
}
else
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_64);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_70);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_64);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_70);
return x_80;
}
}
}
}
}
}
else
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_6);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_7);
return x_146;
}
}
}
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l_panicWithPos___at_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_panicWithPos___at_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayed___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_90; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 2);
lean_inc(x_8);
lean_dec(x_4);
x_90 = lean_expr_has_expr_mvar(x_8);
if (x_90 == 0)
{
uint8_t x_91; 
x_91 = lean_expr_has_level_mvar(x_8);
if (x_91 == 0)
{
x_9 = x_8;
x_10 = x_5;
goto block_89;
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_5, 1);
lean_inc(x_92);
x_93 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_92, x_8);
lean_dec(x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_inc(x_2);
lean_inc(x_8);
x_94 = lean_apply_2(x_2, x_8, x_5);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
lean_dec(x_94);
x_97 = !lean_is_exclusive(x_95);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
x_99 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_98, x_8, x_96);
lean_ctor_set(x_95, 1, x_99);
x_9 = x_96;
x_10 = x_95;
goto block_89;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_95, 0);
x_101 = lean_ctor_get(x_95, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_95);
lean_inc(x_96);
x_102 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_101, x_8, x_96);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_102);
x_9 = x_96;
x_10 = x_103;
goto block_89;
}
}
else
{
lean_object* x_104; 
lean_dec(x_8);
x_104 = lean_ctor_get(x_93, 0);
lean_inc(x_104);
lean_dec(x_93);
x_9 = x_104;
x_10 = x_5;
goto block_89;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_5, 1);
lean_inc(x_105);
x_106 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_105, x_8);
lean_dec(x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
lean_inc(x_2);
lean_inc(x_8);
x_107 = lean_apply_2(x_2, x_8, x_5);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 0);
lean_inc(x_109);
lean_dec(x_107);
x_110 = !lean_is_exclusive(x_108);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
x_112 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_111, x_8, x_109);
lean_ctor_set(x_108, 1, x_112);
x_9 = x_109;
x_10 = x_108;
goto block_89;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_108, 0);
x_114 = lean_ctor_get(x_108, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_108);
lean_inc(x_109);
x_115 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_114, x_8, x_109);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_115);
x_9 = x_109;
x_10 = x_116;
goto block_89;
}
}
else
{
lean_object* x_117; 
lean_dec(x_8);
x_117 = lean_ctor_get(x_106, 0);
lean_inc(x_117);
lean_dec(x_106);
x_9 = x_117;
x_10 = x_5;
goto block_89;
}
}
block_89:
{
uint8_t x_11; 
x_11 = lean_expr_has_expr_mvar(x_9);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = lean_expr_has_level_mvar(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_array_get_size(x_7);
x_14 = lean_expr_abstract(x_9, x_7);
lean_inc(x_6);
x_15 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___rarg(x_1, x_2, x_6, x_7, x_13, x_14, x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_1, 9);
lean_inc(x_20);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_apply_5(x_20, x_22, x_3, x_6, x_7, x_9);
lean_ctor_set(x_18, 0, x_23);
x_24 = lean_box(0);
lean_ctor_set(x_15, 0, x_24);
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_18);
x_27 = lean_apply_5(x_20, x_25, x_3, x_6, x_7, x_9);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_box(0);
lean_ctor_set(x_15, 1, x_28);
lean_ctor_set(x_15, 0, x_29);
return x_15;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
lean_dec(x_15);
x_31 = lean_ctor_get(x_1, 9);
lean_inc(x_31);
lean_dec(x_1);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_34 = x_30;
} else {
 lean_dec_ref(x_30);
 x_34 = lean_box(0);
}
x_35 = lean_apply_5(x_31, x_32, x_3, x_6, x_7, x_9);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_39 = !lean_is_exclusive(x_15);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_40 = lean_ctor_get(x_15, 1);
x_41 = lean_ctor_get(x_15, 0);
lean_dec(x_41);
x_42 = lean_ctor_get(x_16, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 6);
lean_inc(x_43);
x_44 = lean_ctor_get(x_1, 11);
lean_inc(x_44);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_40);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_40, 0);
lean_inc(x_3);
x_47 = lean_apply_2(x_44, x_46, x_3);
x_48 = lean_apply_3(x_43, x_47, x_3, x_42);
lean_ctor_set(x_40, 0, x_48);
return x_15;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_40, 0);
x_50 = lean_ctor_get(x_40, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_40);
lean_inc(x_3);
x_51 = lean_apply_2(x_44, x_49, x_3);
x_52 = lean_apply_3(x_43, x_51, x_3, x_42);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
lean_ctor_set(x_15, 1, x_53);
return x_15;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_54 = lean_ctor_get(x_15, 1);
lean_inc(x_54);
lean_dec(x_15);
x_55 = lean_ctor_get(x_16, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_1, 6);
lean_inc(x_56);
x_57 = lean_ctor_get(x_1, 11);
lean_inc(x_57);
lean_dec(x_1);
x_58 = lean_ctor_get(x_54, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_60 = x_54;
} else {
 lean_dec_ref(x_54);
 x_60 = lean_box(0);
}
lean_inc(x_3);
x_61 = lean_apply_2(x_57, x_58, x_3);
x_62 = lean_apply_3(x_56, x_61, x_3, x_55);
if (lean_is_scalar(x_60)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_60;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_59);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_16);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; uint8_t x_66; 
lean_dec(x_2);
x_65 = lean_ctor_get(x_1, 9);
lean_inc(x_65);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_10);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_10, 0);
x_68 = lean_apply_5(x_65, x_67, x_3, x_6, x_7, x_9);
lean_ctor_set(x_10, 0, x_68);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_10);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_71 = lean_ctor_get(x_10, 0);
x_72 = lean_ctor_get(x_10, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_10);
x_73 = lean_apply_5(x_65, x_71, x_3, x_6, x_7, x_9);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
else
{
lean_object* x_77; uint8_t x_78; 
lean_dec(x_2);
x_77 = lean_ctor_get(x_1, 9);
lean_inc(x_77);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_10);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_10, 0);
x_80 = lean_apply_5(x_77, x_79, x_3, x_6, x_7, x_9);
lean_ctor_set(x_10, 0, x_80);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_10);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_83 = lean_ctor_get(x_10, 0);
x_84 = lean_ctor_get(x_10, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_10);
x_85 = lean_apply_5(x_77, x_83, x_3, x_6, x_7, x_9);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
}
}
}
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayed___rarg), 5, 0);
return x_2;
}
}
lean_object* l_panicWithPos___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = l_panicWithPos___rarg___closed__1;
x_7 = lean_string_append(x_6, x_1);
x_8 = l_panicWithPos___rarg___closed__2;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_Nat_repr(x_2);
x_11 = lean_string_append(x_9, x_10);
lean_dec(x_10);
x_12 = l_panicWithPos___rarg___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_Nat_repr(x_3);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = l_panicWithPos___rarg___closed__3;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_string_append(x_17, x_4);
x_19 = l_panicWithPos___at_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___spec__1___rarg___closed__2;
x_20 = lean_panic_fn(x_18);
x_21 = lean_apply_1(x_20, x_5);
return x_21;
}
}
lean_object* l_panicWithPos___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_panicWithPos___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__2___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_4, x_9);
lean_dec(x_4);
x_11 = l_Lean_exprIsInhabited;
x_12 = lean_array_get(x_11, x_3, x_10);
lean_inc(x_2);
x_13 = l_Lean_LocalContext_findFVar(x_2, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_14 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___rarg___closed__1;
x_15 = lean_unsigned_to_nat(193u);
x_16 = lean_unsigned_to_nat(12u);
x_17 = l_Nat_foldRevAux___main___at_Lean_LocalContext_mkBinding___spec__1___closed__1;
x_18 = l_panicWithPos___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__2___rarg(x_14, x_15, x_16, x_17, x_6);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
lean_dec(x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; uint8_t x_35; 
x_20 = lean_ctor_get(x_19, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 3);
lean_inc(x_21);
x_22 = lean_ctor_get_uint8(x_19, sizeof(void*)*4);
lean_dec(x_19);
x_35 = lean_expr_has_expr_mvar(x_21);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = lean_expr_has_level_mvar(x_21);
if (x_36 == 0)
{
x_23 = x_21;
x_24 = x_6;
goto block_34;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_6, 1);
lean_inc(x_37);
x_38 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_37, x_21);
lean_dec(x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_inc(x_21);
lean_inc(x_1);
x_39 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_21, x_6);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
x_44 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_43, x_21, x_41);
lean_ctor_set(x_40, 1, x_44);
x_23 = x_41;
x_24 = x_40;
goto block_34;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_40, 0);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_40);
lean_inc(x_41);
x_47 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_46, x_21, x_41);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
x_23 = x_41;
x_24 = x_48;
goto block_34;
}
}
else
{
lean_object* x_49; 
lean_dec(x_21);
x_49 = lean_ctor_get(x_38, 0);
lean_inc(x_49);
lean_dec(x_38);
x_23 = x_49;
x_24 = x_6;
goto block_34;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_6, 1);
lean_inc(x_50);
x_51 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_50, x_21);
lean_dec(x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_inc(x_21);
lean_inc(x_1);
x_52 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_21, x_6);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
lean_dec(x_52);
x_55 = !lean_is_exclusive(x_53);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
x_57 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_56, x_21, x_54);
lean_ctor_set(x_53, 1, x_57);
x_23 = x_54;
x_24 = x_53;
goto block_34;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_53, 0);
x_59 = lean_ctor_get(x_53, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_53);
lean_inc(x_54);
x_60 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_59, x_21, x_54);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_60);
x_23 = x_54;
x_24 = x_61;
goto block_34;
}
}
else
{
lean_object* x_62; 
lean_dec(x_21);
x_62 = lean_ctor_get(x_51, 0);
lean_inc(x_62);
lean_dec(x_51);
x_23 = x_62;
x_24 = x_6;
goto block_34;
}
}
block_34:
{
uint8_t x_25; 
x_25 = lean_expr_has_expr_mvar(x_23);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = lean_expr_has_level_mvar(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_expr_abstract_range(x_23, x_10, x_3);
lean_dec(x_23);
x_28 = lean_expr_mk_lambda(x_20, x_22, x_27, x_5);
x_4 = x_10;
x_5 = x_28;
x_6 = x_24;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_24);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_24);
return x_33;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_116; 
x_63 = lean_ctor_get(x_19, 2);
lean_inc(x_63);
x_64 = lean_ctor_get(x_19, 3);
lean_inc(x_64);
x_65 = lean_ctor_get(x_19, 4);
lean_inc(x_65);
lean_dec(x_19);
x_116 = lean_expr_has_expr_mvar(x_64);
if (x_116 == 0)
{
uint8_t x_117; 
x_117 = lean_expr_has_level_mvar(x_64);
if (x_117 == 0)
{
x_66 = x_64;
x_67 = x_6;
goto block_115;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_6, 1);
lean_inc(x_118);
x_119 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_118, x_64);
lean_dec(x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
lean_inc(x_64);
lean_inc(x_1);
x_120 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_64, x_6);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 0);
lean_inc(x_122);
lean_dec(x_120);
x_123 = !lean_is_exclusive(x_121);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
x_125 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_124, x_64, x_122);
lean_ctor_set(x_121, 1, x_125);
x_66 = x_122;
x_67 = x_121;
goto block_115;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_126 = lean_ctor_get(x_121, 0);
x_127 = lean_ctor_get(x_121, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_121);
lean_inc(x_122);
x_128 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_127, x_64, x_122);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_128);
x_66 = x_122;
x_67 = x_129;
goto block_115;
}
}
else
{
lean_object* x_130; 
lean_dec(x_64);
x_130 = lean_ctor_get(x_119, 0);
lean_inc(x_130);
lean_dec(x_119);
x_66 = x_130;
x_67 = x_6;
goto block_115;
}
}
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_6, 1);
lean_inc(x_131);
x_132 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_131, x_64);
lean_dec(x_131);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
lean_inc(x_64);
lean_inc(x_1);
x_133 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_64, x_6);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
lean_dec(x_133);
x_136 = !lean_is_exclusive(x_134);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
x_138 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_137, x_64, x_135);
lean_ctor_set(x_134, 1, x_138);
x_66 = x_135;
x_67 = x_134;
goto block_115;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_139 = lean_ctor_get(x_134, 0);
x_140 = lean_ctor_get(x_134, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_134);
lean_inc(x_135);
x_141 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_140, x_64, x_135);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_141);
x_66 = x_135;
x_67 = x_142;
goto block_115;
}
}
else
{
lean_object* x_143; 
lean_dec(x_64);
x_143 = lean_ctor_get(x_132, 0);
lean_inc(x_143);
lean_dec(x_132);
x_66 = x_143;
x_67 = x_6;
goto block_115;
}
}
block_115:
{
lean_object* x_68; lean_object* x_69; uint8_t x_81; 
x_81 = lean_expr_has_expr_mvar(x_66);
if (x_81 == 0)
{
uint8_t x_82; 
x_82 = lean_expr_has_level_mvar(x_66);
if (x_82 == 0)
{
uint8_t x_83; 
x_83 = lean_expr_has_expr_mvar(x_65);
if (x_83 == 0)
{
uint8_t x_84; 
x_84 = lean_expr_has_level_mvar(x_65);
if (x_84 == 0)
{
x_68 = x_65;
x_69 = x_67;
goto block_80;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_67, 1);
lean_inc(x_85);
x_86 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_85, x_65);
lean_dec(x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
lean_inc(x_65);
lean_inc(x_1);
x_87 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_65, x_67);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_89);
lean_dec(x_87);
x_90 = !lean_is_exclusive(x_88);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
x_92 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_91, x_65, x_89);
lean_ctor_set(x_88, 1, x_92);
x_68 = x_89;
x_69 = x_88;
goto block_80;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_88, 0);
x_94 = lean_ctor_get(x_88, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_88);
lean_inc(x_89);
x_95 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_94, x_65, x_89);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_95);
x_68 = x_89;
x_69 = x_96;
goto block_80;
}
}
else
{
lean_object* x_97; 
lean_dec(x_65);
x_97 = lean_ctor_get(x_86, 0);
lean_inc(x_97);
lean_dec(x_86);
x_68 = x_97;
x_69 = x_67;
goto block_80;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_67, 1);
lean_inc(x_98);
x_99 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_98, x_65);
lean_dec(x_98);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
lean_inc(x_65);
lean_inc(x_1);
x_100 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_65, x_67);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 0);
lean_inc(x_102);
lean_dec(x_100);
x_103 = !lean_is_exclusive(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
x_105 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_104, x_65, x_102);
lean_ctor_set(x_101, 1, x_105);
x_68 = x_102;
x_69 = x_101;
goto block_80;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = lean_ctor_get(x_101, 0);
x_107 = lean_ctor_get(x_101, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_101);
lean_inc(x_102);
x_108 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_107, x_65, x_102);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_108);
x_68 = x_102;
x_69 = x_109;
goto block_80;
}
}
else
{
lean_object* x_110; 
lean_dec(x_65);
x_110 = lean_ctor_get(x_99, 0);
lean_inc(x_110);
lean_dec(x_99);
x_68 = x_110;
x_69 = x_67;
goto block_80;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_63);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_111 = lean_box(0);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_67);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_63);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_113 = lean_box(0);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_67);
return x_114;
}
block_80:
{
uint8_t x_70; 
x_70 = lean_expr_has_expr_mvar(x_68);
if (x_70 == 0)
{
uint8_t x_71; 
x_71 = lean_expr_has_level_mvar(x_68);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_expr_abstract_range(x_66, x_10, x_3);
lean_dec(x_66);
x_73 = lean_expr_abstract_range(x_68, x_10, x_3);
lean_dec(x_68);
x_74 = lean_expr_mk_let(x_63, x_72, x_73, x_5);
x_4 = x_10;
x_5 = x_74;
x_6 = x_69;
goto _start;
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_68);
lean_dec(x_66);
lean_dec(x_63);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_69);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_68);
lean_dec(x_66);
lean_dec(x_63);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_69);
return x_79;
}
}
}
}
}
}
else
{
lean_object* x_144; lean_object* x_145; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_5);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_6);
return x_145;
}
}
}
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_List_mmap___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_1);
x_11 = l_Lean_AbstractMetavarContext_instantiateLevelMVars___main___rarg(x_1, x_8, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_ctor_set(x_3, 0, x_13);
x_14 = l_List_mmap___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__3___rarg(x_1, x_9, x_3);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_ctor_set(x_2, 1, x_16);
lean_ctor_set(x_2, 0, x_12);
lean_ctor_set(x_14, 0, x_2);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_14);
lean_ctor_set(x_2, 1, x_17);
lean_ctor_set(x_2, 0, x_12);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_3);
lean_inc(x_1);
x_24 = l_Lean_AbstractMetavarContext_instantiateLevelMVars___main___rarg(x_1, x_20, x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
x_28 = l_List_mmap___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__3___rarg(x_1, x_21, x_27);
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
lean_ctor_set(x_2, 1, x_29);
lean_ctor_set(x_2, 0, x_25);
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_33 = lean_ctor_get(x_2, 0);
x_34 = lean_ctor_get(x_2, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_2);
x_35 = lean_ctor_get(x_3, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_3, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_37 = x_3;
} else {
 lean_dec_ref(x_3);
 x_37 = lean_box(0);
}
lean_inc(x_1);
x_38 = l_Lean_AbstractMetavarContext_instantiateLevelMVars___main___rarg(x_1, x_33, x_35);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
if (lean_is_scalar(x_37)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_37;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_36);
x_42 = l_List_mmap___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__3___rarg(x_1, x_34, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_45 = x_42;
} else {
 lean_dec_ref(x_42);
 x_45 = lean_box(0);
}
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_39);
lean_ctor_set(x_46, 1, x_43);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
}
}
}
lean_object* l_List_mmap___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_mmap___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_ummapAux___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_3);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Array_empty___closed__1;
x_8 = x_3;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_array_fget(x_3, x_2);
x_11 = lean_box(0);
lean_inc(x_10);
x_12 = x_11;
x_13 = lean_array_fset(x_3, x_2, x_12);
x_14 = lean_expr_has_expr_mvar(x_10);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = lean_expr_has_level_mvar(x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_2, x_16);
lean_inc(x_10);
x_18 = x_10;
x_19 = lean_array_fset(x_13, x_2, x_18);
lean_dec(x_2);
x_2 = x_17;
x_3 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_4, 1);
lean_inc(x_21);
x_22 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_21, x_10);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_inc(x_10);
lean_inc(x_1);
x_23 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_10, x_4);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_inc(x_10);
x_28 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_27, x_10, x_25);
lean_ctor_set(x_24, 1, x_28);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_2, x_29);
x_31 = x_25;
x_32 = lean_array_fset(x_13, x_2, x_31);
lean_dec(x_2);
x_2 = x_30;
x_3 = x_32;
x_4 = x_24;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_24, 0);
x_35 = lean_ctor_get(x_24, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_24);
lean_inc(x_25);
lean_inc(x_10);
x_36 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_35, x_10, x_25);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_2, x_38);
x_40 = x_25;
x_41 = lean_array_fset(x_13, x_2, x_40);
lean_dec(x_2);
x_2 = x_39;
x_3 = x_41;
x_4 = x_37;
goto _start;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_22, 0);
lean_inc(x_43);
lean_dec(x_22);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_add(x_2, x_44);
x_46 = x_43;
x_47 = lean_array_fset(x_13, x_2, x_46);
lean_dec(x_2);
x_2 = x_45;
x_3 = x_47;
goto _start;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_4, 1);
lean_inc(x_49);
x_50 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_49, x_10);
lean_dec(x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_inc(x_10);
lean_inc(x_1);
x_51 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_10, x_4);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
lean_dec(x_51);
x_54 = !lean_is_exclusive(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_inc(x_10);
x_56 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_55, x_10, x_53);
lean_ctor_set(x_52, 1, x_56);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_add(x_2, x_57);
x_59 = x_53;
x_60 = lean_array_fset(x_13, x_2, x_59);
lean_dec(x_2);
x_2 = x_58;
x_3 = x_60;
x_4 = x_52;
goto _start;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_62 = lean_ctor_get(x_52, 0);
x_63 = lean_ctor_get(x_52, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_52);
lean_inc(x_53);
lean_inc(x_10);
x_64 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_63, x_10, x_53);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_add(x_2, x_66);
x_68 = x_53;
x_69 = lean_array_fset(x_13, x_2, x_68);
lean_dec(x_2);
x_2 = x_67;
x_3 = x_69;
x_4 = x_65;
goto _start;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_50, 0);
lean_inc(x_71);
lean_dec(x_50);
x_72 = lean_unsigned_to_nat(1u);
x_73 = lean_nat_add(x_2, x_72);
x_74 = x_71;
x_75 = lean_array_fset(x_13, x_2, x_74);
lean_dec(x_2);
x_2 = x_73;
x_3 = x_75;
goto _start;
}
}
}
}
}
lean_object* l_Array_ummapAux___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_ummapAux___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__4___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Expr_3__withAppRevAux___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; uint8_t x_75; 
x_5 = l_Lean_Expr_isMVar(x_2);
x_75 = lean_expr_has_expr_mvar(x_2);
if (x_75 == 0)
{
uint8_t x_76; 
x_76 = lean_expr_has_level_mvar(x_2);
if (x_76 == 0)
{
x_6 = x_2;
x_7 = x_4;
goto block_74;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_4, 1);
lean_inc(x_77);
x_78 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_77, x_2);
lean_dec(x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
lean_inc(x_2);
lean_inc(x_1);
x_79 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_2, x_4);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
lean_dec(x_79);
x_82 = !lean_is_exclusive(x_80);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
x_84 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_83, x_2, x_81);
lean_ctor_set(x_80, 1, x_84);
x_6 = x_81;
x_7 = x_80;
goto block_74;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_80, 0);
x_86 = lean_ctor_get(x_80, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_80);
lean_inc(x_81);
x_87 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_86, x_2, x_81);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_87);
x_6 = x_81;
x_7 = x_88;
goto block_74;
}
}
else
{
lean_object* x_89; 
lean_dec(x_2);
x_89 = lean_ctor_get(x_78, 0);
lean_inc(x_89);
lean_dec(x_78);
x_6 = x_89;
x_7 = x_4;
goto block_74;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_4, 1);
lean_inc(x_90);
x_91 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_90, x_2);
lean_dec(x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
lean_inc(x_2);
lean_inc(x_1);
x_92 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_2, x_4);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 0);
lean_inc(x_94);
lean_dec(x_92);
x_95 = !lean_is_exclusive(x_93);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
x_97 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_96, x_2, x_94);
lean_ctor_set(x_93, 1, x_97);
x_6 = x_94;
x_7 = x_93;
goto block_74;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_93, 0);
x_99 = lean_ctor_get(x_93, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_93);
lean_inc(x_94);
x_100 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_99, x_2, x_94);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_100);
x_6 = x_94;
x_7 = x_101;
goto block_74;
}
}
else
{
lean_object* x_102; 
lean_dec(x_2);
x_102 = lean_ctor_get(x_91, 0);
lean_inc(x_102);
lean_dec(x_91);
x_6 = x_102;
x_7 = x_4;
goto block_74;
}
}
block_74:
{
lean_object* x_8; 
if (x_5 == 0)
{
lean_object* x_19; 
x_19 = lean_box(0);
x_8 = x_19;
goto block_18;
}
else
{
uint8_t x_20; 
x_20 = l_Lean_Expr_isLambda(x_6);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_box(0);
x_8 = x_21;
goto block_18;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_Lean_Expr_betaRev(x_6, x_3);
lean_dec(x_6);
x_23 = lean_expr_has_expr_mvar(x_22);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = lean_expr_has_level_mvar(x_22);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_7);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
x_27 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_26, x_22);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; uint8_t x_29; 
lean_inc(x_22);
x_28 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_22, x_7);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_28, 1);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 0);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
x_34 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_33, x_22, x_32);
lean_ctor_set(x_30, 1, x_34);
return x_28;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_28, 0);
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
lean_inc(x_35);
x_38 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_37, x_22, x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_28, 1, x_39);
return x_28;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_28, 1);
x_41 = lean_ctor_get(x_28, 0);
lean_inc(x_40);
lean_inc(x_41);
lean_dec(x_28);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_44 = x_40;
} else {
 lean_dec_ref(x_40);
 x_44 = lean_box(0);
}
lean_inc(x_41);
x_45 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_43, x_22, x_41);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_41);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_22);
lean_dec(x_1);
x_48 = lean_ctor_get(x_27, 0);
lean_inc(x_48);
lean_dec(x_27);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_7);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_7, 1);
lean_inc(x_50);
x_51 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_50, x_22);
lean_dec(x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; uint8_t x_53; 
lean_inc(x_22);
x_52 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_22, x_7);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_52, 1);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_52, 0);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
x_58 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_57, x_22, x_56);
lean_ctor_set(x_54, 1, x_58);
return x_52;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_52, 0);
x_60 = lean_ctor_get(x_54, 0);
x_61 = lean_ctor_get(x_54, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_54);
lean_inc(x_59);
x_62 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_61, x_22, x_59);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_52, 1, x_63);
return x_52;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_64 = lean_ctor_get(x_52, 1);
x_65 = lean_ctor_get(x_52, 0);
lean_inc(x_64);
lean_inc(x_65);
lean_dec(x_52);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_68 = x_64;
} else {
 lean_dec_ref(x_64);
 x_68 = lean_box(0);
}
lean_inc(x_65);
x_69 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_67, x_22, x_65);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_66);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_65);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_22);
lean_dec(x_1);
x_72 = lean_ctor_get(x_51, 0);
lean_inc(x_72);
lean_dec(x_51);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_7);
return x_73;
}
}
}
}
block_18:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_dec(x_8);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_ummapAux___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__4___rarg(x_1, x_9, x_3, x_7);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Lean_mkAppRev(x_6, x_12);
lean_dec(x_12);
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
x_16 = l_Lean_mkAppRev(x_6, x_14);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
}
case 1:
{
uint8_t x_103; lean_object* x_104; lean_object* x_105; uint8_t x_173; 
x_103 = l_Lean_Expr_isMVar(x_2);
x_173 = lean_expr_has_expr_mvar(x_2);
if (x_173 == 0)
{
uint8_t x_174; 
x_174 = lean_expr_has_level_mvar(x_2);
if (x_174 == 0)
{
x_104 = x_2;
x_105 = x_4;
goto block_172;
}
else
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_4, 1);
lean_inc(x_175);
x_176 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_175, x_2);
lean_dec(x_175);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
lean_inc(x_2);
lean_inc(x_1);
x_177 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_2, x_4);
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 0);
lean_inc(x_179);
lean_dec(x_177);
x_180 = !lean_is_exclusive(x_178);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
x_182 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_181, x_2, x_179);
lean_ctor_set(x_178, 1, x_182);
x_104 = x_179;
x_105 = x_178;
goto block_172;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_183 = lean_ctor_get(x_178, 0);
x_184 = lean_ctor_get(x_178, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_178);
lean_inc(x_179);
x_185 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_184, x_2, x_179);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_183);
lean_ctor_set(x_186, 1, x_185);
x_104 = x_179;
x_105 = x_186;
goto block_172;
}
}
else
{
lean_object* x_187; 
lean_dec(x_2);
x_187 = lean_ctor_get(x_176, 0);
lean_inc(x_187);
lean_dec(x_176);
x_104 = x_187;
x_105 = x_4;
goto block_172;
}
}
}
else
{
lean_object* x_188; lean_object* x_189; 
x_188 = lean_ctor_get(x_4, 1);
lean_inc(x_188);
x_189 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_188, x_2);
lean_dec(x_188);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; 
lean_inc(x_2);
lean_inc(x_1);
x_190 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_2, x_4);
x_191 = lean_ctor_get(x_190, 1);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 0);
lean_inc(x_192);
lean_dec(x_190);
x_193 = !lean_is_exclusive(x_191);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
x_195 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_194, x_2, x_192);
lean_ctor_set(x_191, 1, x_195);
x_104 = x_192;
x_105 = x_191;
goto block_172;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_196 = lean_ctor_get(x_191, 0);
x_197 = lean_ctor_get(x_191, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_191);
lean_inc(x_192);
x_198 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_197, x_2, x_192);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_196);
lean_ctor_set(x_199, 1, x_198);
x_104 = x_192;
x_105 = x_199;
goto block_172;
}
}
else
{
lean_object* x_200; 
lean_dec(x_2);
x_200 = lean_ctor_get(x_189, 0);
lean_inc(x_200);
lean_dec(x_189);
x_104 = x_200;
x_105 = x_4;
goto block_172;
}
}
block_172:
{
lean_object* x_106; 
if (x_103 == 0)
{
lean_object* x_117; 
x_117 = lean_box(0);
x_106 = x_117;
goto block_116;
}
else
{
uint8_t x_118; 
x_118 = l_Lean_Expr_isLambda(x_104);
if (x_118 == 0)
{
lean_object* x_119; 
x_119 = lean_box(0);
x_106 = x_119;
goto block_116;
}
else
{
lean_object* x_120; uint8_t x_121; 
x_120 = l_Lean_Expr_betaRev(x_104, x_3);
lean_dec(x_104);
x_121 = lean_expr_has_expr_mvar(x_120);
if (x_121 == 0)
{
uint8_t x_122; 
x_122 = lean_expr_has_level_mvar(x_120);
if (x_122 == 0)
{
lean_object* x_123; 
lean_dec(x_1);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_105);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_105, 1);
lean_inc(x_124);
x_125 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_124, x_120);
lean_dec(x_124);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; uint8_t x_127; 
lean_inc(x_120);
x_126 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_120, x_105);
x_127 = !lean_is_exclusive(x_126);
if (x_127 == 0)
{
lean_object* x_128; uint8_t x_129; 
x_128 = lean_ctor_get(x_126, 1);
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_126, 0);
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
x_132 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_131, x_120, x_130);
lean_ctor_set(x_128, 1, x_132);
return x_126;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_133 = lean_ctor_get(x_126, 0);
x_134 = lean_ctor_get(x_128, 0);
x_135 = lean_ctor_get(x_128, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_128);
lean_inc(x_133);
x_136 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_135, x_120, x_133);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_136);
lean_ctor_set(x_126, 1, x_137);
return x_126;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_138 = lean_ctor_get(x_126, 1);
x_139 = lean_ctor_get(x_126, 0);
lean_inc(x_138);
lean_inc(x_139);
lean_dec(x_126);
x_140 = lean_ctor_get(x_138, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_142 = x_138;
} else {
 lean_dec_ref(x_138);
 x_142 = lean_box(0);
}
lean_inc(x_139);
x_143 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_141, x_120, x_139);
if (lean_is_scalar(x_142)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_142;
}
lean_ctor_set(x_144, 0, x_140);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_139);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
else
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_120);
lean_dec(x_1);
x_146 = lean_ctor_get(x_125, 0);
lean_inc(x_146);
lean_dec(x_125);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_105);
return x_147;
}
}
}
else
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_105, 1);
lean_inc(x_148);
x_149 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_148, x_120);
lean_dec(x_148);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; uint8_t x_151; 
lean_inc(x_120);
x_150 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_120, x_105);
x_151 = !lean_is_exclusive(x_150);
if (x_151 == 0)
{
lean_object* x_152; uint8_t x_153; 
x_152 = lean_ctor_get(x_150, 1);
x_153 = !lean_is_exclusive(x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_150, 0);
x_155 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
x_156 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_155, x_120, x_154);
lean_ctor_set(x_152, 1, x_156);
return x_150;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_157 = lean_ctor_get(x_150, 0);
x_158 = lean_ctor_get(x_152, 0);
x_159 = lean_ctor_get(x_152, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_152);
lean_inc(x_157);
x_160 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_159, x_120, x_157);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_160);
lean_ctor_set(x_150, 1, x_161);
return x_150;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_162 = lean_ctor_get(x_150, 1);
x_163 = lean_ctor_get(x_150, 0);
lean_inc(x_162);
lean_inc(x_163);
lean_dec(x_150);
x_164 = lean_ctor_get(x_162, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_162, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_166 = x_162;
} else {
 lean_dec_ref(x_162);
 x_166 = lean_box(0);
}
lean_inc(x_163);
x_167 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_165, x_120, x_163);
if (lean_is_scalar(x_166)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_166;
}
lean_ctor_set(x_168, 0, x_164);
lean_ctor_set(x_168, 1, x_167);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_163);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
else
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_120);
lean_dec(x_1);
x_170 = lean_ctor_get(x_149, 0);
lean_inc(x_170);
lean_dec(x_149);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_105);
return x_171;
}
}
}
}
block_116:
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
lean_dec(x_106);
x_107 = lean_unsigned_to_nat(0u);
x_108 = l_Array_ummapAux___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__4___rarg(x_1, x_107, x_3, x_105);
x_109 = !lean_is_exclusive(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_108, 0);
x_111 = l_Lean_mkAppRev(x_104, x_110);
lean_dec(x_110);
lean_ctor_set(x_108, 0, x_111);
return x_108;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_108, 0);
x_113 = lean_ctor_get(x_108, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_108);
x_114 = l_Lean_mkAppRev(x_104, x_112);
lean_dec(x_112);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
}
case 2:
{
uint8_t x_201; lean_object* x_202; lean_object* x_203; uint8_t x_271; 
x_201 = l_Lean_Expr_isMVar(x_2);
x_271 = lean_expr_has_expr_mvar(x_2);
if (x_271 == 0)
{
uint8_t x_272; 
x_272 = lean_expr_has_level_mvar(x_2);
if (x_272 == 0)
{
x_202 = x_2;
x_203 = x_4;
goto block_270;
}
else
{
lean_object* x_273; lean_object* x_274; 
x_273 = lean_ctor_get(x_4, 1);
lean_inc(x_273);
x_274 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_273, x_2);
lean_dec(x_273);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; 
lean_inc(x_2);
lean_inc(x_1);
x_275 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_2, x_4);
x_276 = lean_ctor_get(x_275, 1);
lean_inc(x_276);
x_277 = lean_ctor_get(x_275, 0);
lean_inc(x_277);
lean_dec(x_275);
x_278 = !lean_is_exclusive(x_276);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; 
x_279 = lean_ctor_get(x_276, 1);
lean_inc(x_277);
x_280 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_279, x_2, x_277);
lean_ctor_set(x_276, 1, x_280);
x_202 = x_277;
x_203 = x_276;
goto block_270;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_281 = lean_ctor_get(x_276, 0);
x_282 = lean_ctor_get(x_276, 1);
lean_inc(x_282);
lean_inc(x_281);
lean_dec(x_276);
lean_inc(x_277);
x_283 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_282, x_2, x_277);
x_284 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_284, 0, x_281);
lean_ctor_set(x_284, 1, x_283);
x_202 = x_277;
x_203 = x_284;
goto block_270;
}
}
else
{
lean_object* x_285; 
lean_dec(x_2);
x_285 = lean_ctor_get(x_274, 0);
lean_inc(x_285);
lean_dec(x_274);
x_202 = x_285;
x_203 = x_4;
goto block_270;
}
}
}
else
{
lean_object* x_286; lean_object* x_287; 
x_286 = lean_ctor_get(x_4, 1);
lean_inc(x_286);
x_287 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_286, x_2);
lean_dec(x_286);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; 
lean_inc(x_2);
lean_inc(x_1);
x_288 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_2, x_4);
x_289 = lean_ctor_get(x_288, 1);
lean_inc(x_289);
x_290 = lean_ctor_get(x_288, 0);
lean_inc(x_290);
lean_dec(x_288);
x_291 = !lean_is_exclusive(x_289);
if (x_291 == 0)
{
lean_object* x_292; lean_object* x_293; 
x_292 = lean_ctor_get(x_289, 1);
lean_inc(x_290);
x_293 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_292, x_2, x_290);
lean_ctor_set(x_289, 1, x_293);
x_202 = x_290;
x_203 = x_289;
goto block_270;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_294 = lean_ctor_get(x_289, 0);
x_295 = lean_ctor_get(x_289, 1);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_289);
lean_inc(x_290);
x_296 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_295, x_2, x_290);
x_297 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_297, 0, x_294);
lean_ctor_set(x_297, 1, x_296);
x_202 = x_290;
x_203 = x_297;
goto block_270;
}
}
else
{
lean_object* x_298; 
lean_dec(x_2);
x_298 = lean_ctor_get(x_287, 0);
lean_inc(x_298);
lean_dec(x_287);
x_202 = x_298;
x_203 = x_4;
goto block_270;
}
}
block_270:
{
lean_object* x_204; 
if (x_201 == 0)
{
lean_object* x_215; 
x_215 = lean_box(0);
x_204 = x_215;
goto block_214;
}
else
{
uint8_t x_216; 
x_216 = l_Lean_Expr_isLambda(x_202);
if (x_216 == 0)
{
lean_object* x_217; 
x_217 = lean_box(0);
x_204 = x_217;
goto block_214;
}
else
{
lean_object* x_218; uint8_t x_219; 
x_218 = l_Lean_Expr_betaRev(x_202, x_3);
lean_dec(x_202);
x_219 = lean_expr_has_expr_mvar(x_218);
if (x_219 == 0)
{
uint8_t x_220; 
x_220 = lean_expr_has_level_mvar(x_218);
if (x_220 == 0)
{
lean_object* x_221; 
lean_dec(x_1);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_218);
lean_ctor_set(x_221, 1, x_203);
return x_221;
}
else
{
lean_object* x_222; lean_object* x_223; 
x_222 = lean_ctor_get(x_203, 1);
lean_inc(x_222);
x_223 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_222, x_218);
lean_dec(x_222);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; uint8_t x_225; 
lean_inc(x_218);
x_224 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_218, x_203);
x_225 = !lean_is_exclusive(x_224);
if (x_225 == 0)
{
lean_object* x_226; uint8_t x_227; 
x_226 = lean_ctor_get(x_224, 1);
x_227 = !lean_is_exclusive(x_226);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_224, 0);
x_229 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
x_230 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_229, x_218, x_228);
lean_ctor_set(x_226, 1, x_230);
return x_224;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_231 = lean_ctor_get(x_224, 0);
x_232 = lean_ctor_get(x_226, 0);
x_233 = lean_ctor_get(x_226, 1);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_226);
lean_inc(x_231);
x_234 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_233, x_218, x_231);
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_232);
lean_ctor_set(x_235, 1, x_234);
lean_ctor_set(x_224, 1, x_235);
return x_224;
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_236 = lean_ctor_get(x_224, 1);
x_237 = lean_ctor_get(x_224, 0);
lean_inc(x_236);
lean_inc(x_237);
lean_dec(x_224);
x_238 = lean_ctor_get(x_236, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_236, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_240 = x_236;
} else {
 lean_dec_ref(x_236);
 x_240 = lean_box(0);
}
lean_inc(x_237);
x_241 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_239, x_218, x_237);
if (lean_is_scalar(x_240)) {
 x_242 = lean_alloc_ctor(0, 2, 0);
} else {
 x_242 = x_240;
}
lean_ctor_set(x_242, 0, x_238);
lean_ctor_set(x_242, 1, x_241);
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_237);
lean_ctor_set(x_243, 1, x_242);
return x_243;
}
}
else
{
lean_object* x_244; lean_object* x_245; 
lean_dec(x_218);
lean_dec(x_1);
x_244 = lean_ctor_get(x_223, 0);
lean_inc(x_244);
lean_dec(x_223);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_203);
return x_245;
}
}
}
else
{
lean_object* x_246; lean_object* x_247; 
x_246 = lean_ctor_get(x_203, 1);
lean_inc(x_246);
x_247 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_246, x_218);
lean_dec(x_246);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; uint8_t x_249; 
lean_inc(x_218);
x_248 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_218, x_203);
x_249 = !lean_is_exclusive(x_248);
if (x_249 == 0)
{
lean_object* x_250; uint8_t x_251; 
x_250 = lean_ctor_get(x_248, 1);
x_251 = !lean_is_exclusive(x_250);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_248, 0);
x_253 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
x_254 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_253, x_218, x_252);
lean_ctor_set(x_250, 1, x_254);
return x_248;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_255 = lean_ctor_get(x_248, 0);
x_256 = lean_ctor_get(x_250, 0);
x_257 = lean_ctor_get(x_250, 1);
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_250);
lean_inc(x_255);
x_258 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_257, x_218, x_255);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_256);
lean_ctor_set(x_259, 1, x_258);
lean_ctor_set(x_248, 1, x_259);
return x_248;
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_260 = lean_ctor_get(x_248, 1);
x_261 = lean_ctor_get(x_248, 0);
lean_inc(x_260);
lean_inc(x_261);
lean_dec(x_248);
x_262 = lean_ctor_get(x_260, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_260, 1);
lean_inc(x_263);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 x_264 = x_260;
} else {
 lean_dec_ref(x_260);
 x_264 = lean_box(0);
}
lean_inc(x_261);
x_265 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_263, x_218, x_261);
if (lean_is_scalar(x_264)) {
 x_266 = lean_alloc_ctor(0, 2, 0);
} else {
 x_266 = x_264;
}
lean_ctor_set(x_266, 0, x_262);
lean_ctor_set(x_266, 1, x_265);
x_267 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_267, 0, x_261);
lean_ctor_set(x_267, 1, x_266);
return x_267;
}
}
else
{
lean_object* x_268; lean_object* x_269; 
lean_dec(x_218);
lean_dec(x_1);
x_268 = lean_ctor_get(x_247, 0);
lean_inc(x_268);
lean_dec(x_247);
x_269 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_203);
return x_269;
}
}
}
}
block_214:
{
lean_object* x_205; lean_object* x_206; uint8_t x_207; 
lean_dec(x_204);
x_205 = lean_unsigned_to_nat(0u);
x_206 = l_Array_ummapAux___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__4___rarg(x_1, x_205, x_3, x_203);
x_207 = !lean_is_exclusive(x_206);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_206, 0);
x_209 = l_Lean_mkAppRev(x_202, x_208);
lean_dec(x_208);
lean_ctor_set(x_206, 0, x_209);
return x_206;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_210 = lean_ctor_get(x_206, 0);
x_211 = lean_ctor_get(x_206, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_206);
x_212 = l_Lean_mkAppRev(x_202, x_210);
lean_dec(x_210);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_211);
return x_213;
}
}
}
}
case 3:
{
uint8_t x_299; lean_object* x_300; lean_object* x_301; uint8_t x_369; 
x_299 = l_Lean_Expr_isMVar(x_2);
x_369 = lean_expr_has_expr_mvar(x_2);
if (x_369 == 0)
{
uint8_t x_370; 
x_370 = lean_expr_has_level_mvar(x_2);
if (x_370 == 0)
{
x_300 = x_2;
x_301 = x_4;
goto block_368;
}
else
{
lean_object* x_371; lean_object* x_372; 
x_371 = lean_ctor_get(x_4, 1);
lean_inc(x_371);
x_372 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_371, x_2);
lean_dec(x_371);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; uint8_t x_376; 
lean_inc(x_2);
lean_inc(x_1);
x_373 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_2, x_4);
x_374 = lean_ctor_get(x_373, 1);
lean_inc(x_374);
x_375 = lean_ctor_get(x_373, 0);
lean_inc(x_375);
lean_dec(x_373);
x_376 = !lean_is_exclusive(x_374);
if (x_376 == 0)
{
lean_object* x_377; lean_object* x_378; 
x_377 = lean_ctor_get(x_374, 1);
lean_inc(x_375);
x_378 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_377, x_2, x_375);
lean_ctor_set(x_374, 1, x_378);
x_300 = x_375;
x_301 = x_374;
goto block_368;
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_379 = lean_ctor_get(x_374, 0);
x_380 = lean_ctor_get(x_374, 1);
lean_inc(x_380);
lean_inc(x_379);
lean_dec(x_374);
lean_inc(x_375);
x_381 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_380, x_2, x_375);
x_382 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_382, 0, x_379);
lean_ctor_set(x_382, 1, x_381);
x_300 = x_375;
x_301 = x_382;
goto block_368;
}
}
else
{
lean_object* x_383; 
lean_dec(x_2);
x_383 = lean_ctor_get(x_372, 0);
lean_inc(x_383);
lean_dec(x_372);
x_300 = x_383;
x_301 = x_4;
goto block_368;
}
}
}
else
{
lean_object* x_384; lean_object* x_385; 
x_384 = lean_ctor_get(x_4, 1);
lean_inc(x_384);
x_385 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_384, x_2);
lean_dec(x_384);
if (lean_obj_tag(x_385) == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; uint8_t x_389; 
lean_inc(x_2);
lean_inc(x_1);
x_386 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_2, x_4);
x_387 = lean_ctor_get(x_386, 1);
lean_inc(x_387);
x_388 = lean_ctor_get(x_386, 0);
lean_inc(x_388);
lean_dec(x_386);
x_389 = !lean_is_exclusive(x_387);
if (x_389 == 0)
{
lean_object* x_390; lean_object* x_391; 
x_390 = lean_ctor_get(x_387, 1);
lean_inc(x_388);
x_391 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_390, x_2, x_388);
lean_ctor_set(x_387, 1, x_391);
x_300 = x_388;
x_301 = x_387;
goto block_368;
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_392 = lean_ctor_get(x_387, 0);
x_393 = lean_ctor_get(x_387, 1);
lean_inc(x_393);
lean_inc(x_392);
lean_dec(x_387);
lean_inc(x_388);
x_394 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_393, x_2, x_388);
x_395 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_395, 0, x_392);
lean_ctor_set(x_395, 1, x_394);
x_300 = x_388;
x_301 = x_395;
goto block_368;
}
}
else
{
lean_object* x_396; 
lean_dec(x_2);
x_396 = lean_ctor_get(x_385, 0);
lean_inc(x_396);
lean_dec(x_385);
x_300 = x_396;
x_301 = x_4;
goto block_368;
}
}
block_368:
{
lean_object* x_302; 
if (x_299 == 0)
{
lean_object* x_313; 
x_313 = lean_box(0);
x_302 = x_313;
goto block_312;
}
else
{
uint8_t x_314; 
x_314 = l_Lean_Expr_isLambda(x_300);
if (x_314 == 0)
{
lean_object* x_315; 
x_315 = lean_box(0);
x_302 = x_315;
goto block_312;
}
else
{
lean_object* x_316; uint8_t x_317; 
x_316 = l_Lean_Expr_betaRev(x_300, x_3);
lean_dec(x_300);
x_317 = lean_expr_has_expr_mvar(x_316);
if (x_317 == 0)
{
uint8_t x_318; 
x_318 = lean_expr_has_level_mvar(x_316);
if (x_318 == 0)
{
lean_object* x_319; 
lean_dec(x_1);
x_319 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_319, 0, x_316);
lean_ctor_set(x_319, 1, x_301);
return x_319;
}
else
{
lean_object* x_320; lean_object* x_321; 
x_320 = lean_ctor_get(x_301, 1);
lean_inc(x_320);
x_321 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_320, x_316);
lean_dec(x_320);
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_322; uint8_t x_323; 
lean_inc(x_316);
x_322 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_316, x_301);
x_323 = !lean_is_exclusive(x_322);
if (x_323 == 0)
{
lean_object* x_324; uint8_t x_325; 
x_324 = lean_ctor_get(x_322, 1);
x_325 = !lean_is_exclusive(x_324);
if (x_325 == 0)
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_326 = lean_ctor_get(x_322, 0);
x_327 = lean_ctor_get(x_324, 1);
lean_inc(x_326);
x_328 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_327, x_316, x_326);
lean_ctor_set(x_324, 1, x_328);
return x_322;
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_329 = lean_ctor_get(x_322, 0);
x_330 = lean_ctor_get(x_324, 0);
x_331 = lean_ctor_get(x_324, 1);
lean_inc(x_331);
lean_inc(x_330);
lean_dec(x_324);
lean_inc(x_329);
x_332 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_331, x_316, x_329);
x_333 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_333, 0, x_330);
lean_ctor_set(x_333, 1, x_332);
lean_ctor_set(x_322, 1, x_333);
return x_322;
}
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_334 = lean_ctor_get(x_322, 1);
x_335 = lean_ctor_get(x_322, 0);
lean_inc(x_334);
lean_inc(x_335);
lean_dec(x_322);
x_336 = lean_ctor_get(x_334, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_334, 1);
lean_inc(x_337);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 lean_ctor_release(x_334, 1);
 x_338 = x_334;
} else {
 lean_dec_ref(x_334);
 x_338 = lean_box(0);
}
lean_inc(x_335);
x_339 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_337, x_316, x_335);
if (lean_is_scalar(x_338)) {
 x_340 = lean_alloc_ctor(0, 2, 0);
} else {
 x_340 = x_338;
}
lean_ctor_set(x_340, 0, x_336);
lean_ctor_set(x_340, 1, x_339);
x_341 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_341, 0, x_335);
lean_ctor_set(x_341, 1, x_340);
return x_341;
}
}
else
{
lean_object* x_342; lean_object* x_343; 
lean_dec(x_316);
lean_dec(x_1);
x_342 = lean_ctor_get(x_321, 0);
lean_inc(x_342);
lean_dec(x_321);
x_343 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_343, 0, x_342);
lean_ctor_set(x_343, 1, x_301);
return x_343;
}
}
}
else
{
lean_object* x_344; lean_object* x_345; 
x_344 = lean_ctor_get(x_301, 1);
lean_inc(x_344);
x_345 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_344, x_316);
lean_dec(x_344);
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_346; uint8_t x_347; 
lean_inc(x_316);
x_346 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_316, x_301);
x_347 = !lean_is_exclusive(x_346);
if (x_347 == 0)
{
lean_object* x_348; uint8_t x_349; 
x_348 = lean_ctor_get(x_346, 1);
x_349 = !lean_is_exclusive(x_348);
if (x_349 == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_350 = lean_ctor_get(x_346, 0);
x_351 = lean_ctor_get(x_348, 1);
lean_inc(x_350);
x_352 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_351, x_316, x_350);
lean_ctor_set(x_348, 1, x_352);
return x_346;
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_353 = lean_ctor_get(x_346, 0);
x_354 = lean_ctor_get(x_348, 0);
x_355 = lean_ctor_get(x_348, 1);
lean_inc(x_355);
lean_inc(x_354);
lean_dec(x_348);
lean_inc(x_353);
x_356 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_355, x_316, x_353);
x_357 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_357, 0, x_354);
lean_ctor_set(x_357, 1, x_356);
lean_ctor_set(x_346, 1, x_357);
return x_346;
}
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_358 = lean_ctor_get(x_346, 1);
x_359 = lean_ctor_get(x_346, 0);
lean_inc(x_358);
lean_inc(x_359);
lean_dec(x_346);
x_360 = lean_ctor_get(x_358, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_358, 1);
lean_inc(x_361);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 lean_ctor_release(x_358, 1);
 x_362 = x_358;
} else {
 lean_dec_ref(x_358);
 x_362 = lean_box(0);
}
lean_inc(x_359);
x_363 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_361, x_316, x_359);
if (lean_is_scalar(x_362)) {
 x_364 = lean_alloc_ctor(0, 2, 0);
} else {
 x_364 = x_362;
}
lean_ctor_set(x_364, 0, x_360);
lean_ctor_set(x_364, 1, x_363);
x_365 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_365, 0, x_359);
lean_ctor_set(x_365, 1, x_364);
return x_365;
}
}
else
{
lean_object* x_366; lean_object* x_367; 
lean_dec(x_316);
lean_dec(x_1);
x_366 = lean_ctor_get(x_345, 0);
lean_inc(x_366);
lean_dec(x_345);
x_367 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_301);
return x_367;
}
}
}
}
block_312:
{
lean_object* x_303; lean_object* x_304; uint8_t x_305; 
lean_dec(x_302);
x_303 = lean_unsigned_to_nat(0u);
x_304 = l_Array_ummapAux___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__4___rarg(x_1, x_303, x_3, x_301);
x_305 = !lean_is_exclusive(x_304);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; 
x_306 = lean_ctor_get(x_304, 0);
x_307 = l_Lean_mkAppRev(x_300, x_306);
lean_dec(x_306);
lean_ctor_set(x_304, 0, x_307);
return x_304;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_308 = lean_ctor_get(x_304, 0);
x_309 = lean_ctor_get(x_304, 1);
lean_inc(x_309);
lean_inc(x_308);
lean_dec(x_304);
x_310 = l_Lean_mkAppRev(x_300, x_308);
lean_dec(x_308);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_309);
return x_311;
}
}
}
}
case 4:
{
uint8_t x_397; lean_object* x_398; lean_object* x_399; uint8_t x_467; 
x_397 = l_Lean_Expr_isMVar(x_2);
x_467 = lean_expr_has_expr_mvar(x_2);
if (x_467 == 0)
{
uint8_t x_468; 
x_468 = lean_expr_has_level_mvar(x_2);
if (x_468 == 0)
{
x_398 = x_2;
x_399 = x_4;
goto block_466;
}
else
{
lean_object* x_469; lean_object* x_470; 
x_469 = lean_ctor_get(x_4, 1);
lean_inc(x_469);
x_470 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_469, x_2);
lean_dec(x_469);
if (lean_obj_tag(x_470) == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; uint8_t x_474; 
lean_inc(x_2);
lean_inc(x_1);
x_471 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_2, x_4);
x_472 = lean_ctor_get(x_471, 1);
lean_inc(x_472);
x_473 = lean_ctor_get(x_471, 0);
lean_inc(x_473);
lean_dec(x_471);
x_474 = !lean_is_exclusive(x_472);
if (x_474 == 0)
{
lean_object* x_475; lean_object* x_476; 
x_475 = lean_ctor_get(x_472, 1);
lean_inc(x_473);
x_476 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_475, x_2, x_473);
lean_ctor_set(x_472, 1, x_476);
x_398 = x_473;
x_399 = x_472;
goto block_466;
}
else
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; 
x_477 = lean_ctor_get(x_472, 0);
x_478 = lean_ctor_get(x_472, 1);
lean_inc(x_478);
lean_inc(x_477);
lean_dec(x_472);
lean_inc(x_473);
x_479 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_478, x_2, x_473);
x_480 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_480, 0, x_477);
lean_ctor_set(x_480, 1, x_479);
x_398 = x_473;
x_399 = x_480;
goto block_466;
}
}
else
{
lean_object* x_481; 
lean_dec(x_2);
x_481 = lean_ctor_get(x_470, 0);
lean_inc(x_481);
lean_dec(x_470);
x_398 = x_481;
x_399 = x_4;
goto block_466;
}
}
}
else
{
lean_object* x_482; lean_object* x_483; 
x_482 = lean_ctor_get(x_4, 1);
lean_inc(x_482);
x_483 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_482, x_2);
lean_dec(x_482);
if (lean_obj_tag(x_483) == 0)
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; uint8_t x_487; 
lean_inc(x_2);
lean_inc(x_1);
x_484 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_2, x_4);
x_485 = lean_ctor_get(x_484, 1);
lean_inc(x_485);
x_486 = lean_ctor_get(x_484, 0);
lean_inc(x_486);
lean_dec(x_484);
x_487 = !lean_is_exclusive(x_485);
if (x_487 == 0)
{
lean_object* x_488; lean_object* x_489; 
x_488 = lean_ctor_get(x_485, 1);
lean_inc(x_486);
x_489 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_488, x_2, x_486);
lean_ctor_set(x_485, 1, x_489);
x_398 = x_486;
x_399 = x_485;
goto block_466;
}
else
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_490 = lean_ctor_get(x_485, 0);
x_491 = lean_ctor_get(x_485, 1);
lean_inc(x_491);
lean_inc(x_490);
lean_dec(x_485);
lean_inc(x_486);
x_492 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_491, x_2, x_486);
x_493 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_493, 0, x_490);
lean_ctor_set(x_493, 1, x_492);
x_398 = x_486;
x_399 = x_493;
goto block_466;
}
}
else
{
lean_object* x_494; 
lean_dec(x_2);
x_494 = lean_ctor_get(x_483, 0);
lean_inc(x_494);
lean_dec(x_483);
x_398 = x_494;
x_399 = x_4;
goto block_466;
}
}
block_466:
{
lean_object* x_400; 
if (x_397 == 0)
{
lean_object* x_411; 
x_411 = lean_box(0);
x_400 = x_411;
goto block_410;
}
else
{
uint8_t x_412; 
x_412 = l_Lean_Expr_isLambda(x_398);
if (x_412 == 0)
{
lean_object* x_413; 
x_413 = lean_box(0);
x_400 = x_413;
goto block_410;
}
else
{
lean_object* x_414; uint8_t x_415; 
x_414 = l_Lean_Expr_betaRev(x_398, x_3);
lean_dec(x_398);
x_415 = lean_expr_has_expr_mvar(x_414);
if (x_415 == 0)
{
uint8_t x_416; 
x_416 = lean_expr_has_level_mvar(x_414);
if (x_416 == 0)
{
lean_object* x_417; 
lean_dec(x_1);
x_417 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_417, 0, x_414);
lean_ctor_set(x_417, 1, x_399);
return x_417;
}
else
{
lean_object* x_418; lean_object* x_419; 
x_418 = lean_ctor_get(x_399, 1);
lean_inc(x_418);
x_419 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_418, x_414);
lean_dec(x_418);
if (lean_obj_tag(x_419) == 0)
{
lean_object* x_420; uint8_t x_421; 
lean_inc(x_414);
x_420 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_414, x_399);
x_421 = !lean_is_exclusive(x_420);
if (x_421 == 0)
{
lean_object* x_422; uint8_t x_423; 
x_422 = lean_ctor_get(x_420, 1);
x_423 = !lean_is_exclusive(x_422);
if (x_423 == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_424 = lean_ctor_get(x_420, 0);
x_425 = lean_ctor_get(x_422, 1);
lean_inc(x_424);
x_426 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_425, x_414, x_424);
lean_ctor_set(x_422, 1, x_426);
return x_420;
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_427 = lean_ctor_get(x_420, 0);
x_428 = lean_ctor_get(x_422, 0);
x_429 = lean_ctor_get(x_422, 1);
lean_inc(x_429);
lean_inc(x_428);
lean_dec(x_422);
lean_inc(x_427);
x_430 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_429, x_414, x_427);
x_431 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_431, 0, x_428);
lean_ctor_set(x_431, 1, x_430);
lean_ctor_set(x_420, 1, x_431);
return x_420;
}
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_432 = lean_ctor_get(x_420, 1);
x_433 = lean_ctor_get(x_420, 0);
lean_inc(x_432);
lean_inc(x_433);
lean_dec(x_420);
x_434 = lean_ctor_get(x_432, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_432, 1);
lean_inc(x_435);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 x_436 = x_432;
} else {
 lean_dec_ref(x_432);
 x_436 = lean_box(0);
}
lean_inc(x_433);
x_437 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_435, x_414, x_433);
if (lean_is_scalar(x_436)) {
 x_438 = lean_alloc_ctor(0, 2, 0);
} else {
 x_438 = x_436;
}
lean_ctor_set(x_438, 0, x_434);
lean_ctor_set(x_438, 1, x_437);
x_439 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_439, 0, x_433);
lean_ctor_set(x_439, 1, x_438);
return x_439;
}
}
else
{
lean_object* x_440; lean_object* x_441; 
lean_dec(x_414);
lean_dec(x_1);
x_440 = lean_ctor_get(x_419, 0);
lean_inc(x_440);
lean_dec(x_419);
x_441 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_441, 0, x_440);
lean_ctor_set(x_441, 1, x_399);
return x_441;
}
}
}
else
{
lean_object* x_442; lean_object* x_443; 
x_442 = lean_ctor_get(x_399, 1);
lean_inc(x_442);
x_443 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_442, x_414);
lean_dec(x_442);
if (lean_obj_tag(x_443) == 0)
{
lean_object* x_444; uint8_t x_445; 
lean_inc(x_414);
x_444 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_414, x_399);
x_445 = !lean_is_exclusive(x_444);
if (x_445 == 0)
{
lean_object* x_446; uint8_t x_447; 
x_446 = lean_ctor_get(x_444, 1);
x_447 = !lean_is_exclusive(x_446);
if (x_447 == 0)
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_448 = lean_ctor_get(x_444, 0);
x_449 = lean_ctor_get(x_446, 1);
lean_inc(x_448);
x_450 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_449, x_414, x_448);
lean_ctor_set(x_446, 1, x_450);
return x_444;
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_451 = lean_ctor_get(x_444, 0);
x_452 = lean_ctor_get(x_446, 0);
x_453 = lean_ctor_get(x_446, 1);
lean_inc(x_453);
lean_inc(x_452);
lean_dec(x_446);
lean_inc(x_451);
x_454 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_453, x_414, x_451);
x_455 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_455, 0, x_452);
lean_ctor_set(x_455, 1, x_454);
lean_ctor_set(x_444, 1, x_455);
return x_444;
}
}
else
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; 
x_456 = lean_ctor_get(x_444, 1);
x_457 = lean_ctor_get(x_444, 0);
lean_inc(x_456);
lean_inc(x_457);
lean_dec(x_444);
x_458 = lean_ctor_get(x_456, 0);
lean_inc(x_458);
x_459 = lean_ctor_get(x_456, 1);
lean_inc(x_459);
if (lean_is_exclusive(x_456)) {
 lean_ctor_release(x_456, 0);
 lean_ctor_release(x_456, 1);
 x_460 = x_456;
} else {
 lean_dec_ref(x_456);
 x_460 = lean_box(0);
}
lean_inc(x_457);
x_461 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_459, x_414, x_457);
if (lean_is_scalar(x_460)) {
 x_462 = lean_alloc_ctor(0, 2, 0);
} else {
 x_462 = x_460;
}
lean_ctor_set(x_462, 0, x_458);
lean_ctor_set(x_462, 1, x_461);
x_463 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_463, 0, x_457);
lean_ctor_set(x_463, 1, x_462);
return x_463;
}
}
else
{
lean_object* x_464; lean_object* x_465; 
lean_dec(x_414);
lean_dec(x_1);
x_464 = lean_ctor_get(x_443, 0);
lean_inc(x_464);
lean_dec(x_443);
x_465 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_465, 0, x_464);
lean_ctor_set(x_465, 1, x_399);
return x_465;
}
}
}
}
block_410:
{
lean_object* x_401; lean_object* x_402; uint8_t x_403; 
lean_dec(x_400);
x_401 = lean_unsigned_to_nat(0u);
x_402 = l_Array_ummapAux___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__4___rarg(x_1, x_401, x_3, x_399);
x_403 = !lean_is_exclusive(x_402);
if (x_403 == 0)
{
lean_object* x_404; lean_object* x_405; 
x_404 = lean_ctor_get(x_402, 0);
x_405 = l_Lean_mkAppRev(x_398, x_404);
lean_dec(x_404);
lean_ctor_set(x_402, 0, x_405);
return x_402;
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_406 = lean_ctor_get(x_402, 0);
x_407 = lean_ctor_get(x_402, 1);
lean_inc(x_407);
lean_inc(x_406);
lean_dec(x_402);
x_408 = l_Lean_mkAppRev(x_398, x_406);
lean_dec(x_406);
x_409 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_409, 0, x_408);
lean_ctor_set(x_409, 1, x_407);
return x_409;
}
}
}
}
case 5:
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; 
x_495 = lean_ctor_get(x_2, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_2, 1);
lean_inc(x_496);
lean_dec(x_2);
x_497 = lean_array_push(x_3, x_496);
x_2 = x_495;
x_3 = x_497;
goto _start;
}
case 6:
{
uint8_t x_499; lean_object* x_500; lean_object* x_501; uint8_t x_569; 
x_499 = l_Lean_Expr_isMVar(x_2);
x_569 = lean_expr_has_expr_mvar(x_2);
if (x_569 == 0)
{
uint8_t x_570; 
x_570 = lean_expr_has_level_mvar(x_2);
if (x_570 == 0)
{
x_500 = x_2;
x_501 = x_4;
goto block_568;
}
else
{
lean_object* x_571; lean_object* x_572; 
x_571 = lean_ctor_get(x_4, 1);
lean_inc(x_571);
x_572 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_571, x_2);
lean_dec(x_571);
if (lean_obj_tag(x_572) == 0)
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; uint8_t x_576; 
lean_inc(x_2);
lean_inc(x_1);
x_573 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_2, x_4);
x_574 = lean_ctor_get(x_573, 1);
lean_inc(x_574);
x_575 = lean_ctor_get(x_573, 0);
lean_inc(x_575);
lean_dec(x_573);
x_576 = !lean_is_exclusive(x_574);
if (x_576 == 0)
{
lean_object* x_577; lean_object* x_578; 
x_577 = lean_ctor_get(x_574, 1);
lean_inc(x_575);
x_578 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_577, x_2, x_575);
lean_ctor_set(x_574, 1, x_578);
x_500 = x_575;
x_501 = x_574;
goto block_568;
}
else
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; 
x_579 = lean_ctor_get(x_574, 0);
x_580 = lean_ctor_get(x_574, 1);
lean_inc(x_580);
lean_inc(x_579);
lean_dec(x_574);
lean_inc(x_575);
x_581 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_580, x_2, x_575);
x_582 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_582, 0, x_579);
lean_ctor_set(x_582, 1, x_581);
x_500 = x_575;
x_501 = x_582;
goto block_568;
}
}
else
{
lean_object* x_583; 
lean_dec(x_2);
x_583 = lean_ctor_get(x_572, 0);
lean_inc(x_583);
lean_dec(x_572);
x_500 = x_583;
x_501 = x_4;
goto block_568;
}
}
}
else
{
lean_object* x_584; lean_object* x_585; 
x_584 = lean_ctor_get(x_4, 1);
lean_inc(x_584);
x_585 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_584, x_2);
lean_dec(x_584);
if (lean_obj_tag(x_585) == 0)
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; uint8_t x_589; 
lean_inc(x_2);
lean_inc(x_1);
x_586 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_2, x_4);
x_587 = lean_ctor_get(x_586, 1);
lean_inc(x_587);
x_588 = lean_ctor_get(x_586, 0);
lean_inc(x_588);
lean_dec(x_586);
x_589 = !lean_is_exclusive(x_587);
if (x_589 == 0)
{
lean_object* x_590; lean_object* x_591; 
x_590 = lean_ctor_get(x_587, 1);
lean_inc(x_588);
x_591 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_590, x_2, x_588);
lean_ctor_set(x_587, 1, x_591);
x_500 = x_588;
x_501 = x_587;
goto block_568;
}
else
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; 
x_592 = lean_ctor_get(x_587, 0);
x_593 = lean_ctor_get(x_587, 1);
lean_inc(x_593);
lean_inc(x_592);
lean_dec(x_587);
lean_inc(x_588);
x_594 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_593, x_2, x_588);
x_595 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_595, 0, x_592);
lean_ctor_set(x_595, 1, x_594);
x_500 = x_588;
x_501 = x_595;
goto block_568;
}
}
else
{
lean_object* x_596; 
lean_dec(x_2);
x_596 = lean_ctor_get(x_585, 0);
lean_inc(x_596);
lean_dec(x_585);
x_500 = x_596;
x_501 = x_4;
goto block_568;
}
}
block_568:
{
lean_object* x_502; 
if (x_499 == 0)
{
lean_object* x_513; 
x_513 = lean_box(0);
x_502 = x_513;
goto block_512;
}
else
{
uint8_t x_514; 
x_514 = l_Lean_Expr_isLambda(x_500);
if (x_514 == 0)
{
lean_object* x_515; 
x_515 = lean_box(0);
x_502 = x_515;
goto block_512;
}
else
{
lean_object* x_516; uint8_t x_517; 
x_516 = l_Lean_Expr_betaRev(x_500, x_3);
lean_dec(x_500);
x_517 = lean_expr_has_expr_mvar(x_516);
if (x_517 == 0)
{
uint8_t x_518; 
x_518 = lean_expr_has_level_mvar(x_516);
if (x_518 == 0)
{
lean_object* x_519; 
lean_dec(x_1);
x_519 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_519, 0, x_516);
lean_ctor_set(x_519, 1, x_501);
return x_519;
}
else
{
lean_object* x_520; lean_object* x_521; 
x_520 = lean_ctor_get(x_501, 1);
lean_inc(x_520);
x_521 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_520, x_516);
lean_dec(x_520);
if (lean_obj_tag(x_521) == 0)
{
lean_object* x_522; uint8_t x_523; 
lean_inc(x_516);
x_522 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_516, x_501);
x_523 = !lean_is_exclusive(x_522);
if (x_523 == 0)
{
lean_object* x_524; uint8_t x_525; 
x_524 = lean_ctor_get(x_522, 1);
x_525 = !lean_is_exclusive(x_524);
if (x_525 == 0)
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; 
x_526 = lean_ctor_get(x_522, 0);
x_527 = lean_ctor_get(x_524, 1);
lean_inc(x_526);
x_528 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_527, x_516, x_526);
lean_ctor_set(x_524, 1, x_528);
return x_522;
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
x_529 = lean_ctor_get(x_522, 0);
x_530 = lean_ctor_get(x_524, 0);
x_531 = lean_ctor_get(x_524, 1);
lean_inc(x_531);
lean_inc(x_530);
lean_dec(x_524);
lean_inc(x_529);
x_532 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_531, x_516, x_529);
x_533 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_533, 0, x_530);
lean_ctor_set(x_533, 1, x_532);
lean_ctor_set(x_522, 1, x_533);
return x_522;
}
}
else
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; 
x_534 = lean_ctor_get(x_522, 1);
x_535 = lean_ctor_get(x_522, 0);
lean_inc(x_534);
lean_inc(x_535);
lean_dec(x_522);
x_536 = lean_ctor_get(x_534, 0);
lean_inc(x_536);
x_537 = lean_ctor_get(x_534, 1);
lean_inc(x_537);
if (lean_is_exclusive(x_534)) {
 lean_ctor_release(x_534, 0);
 lean_ctor_release(x_534, 1);
 x_538 = x_534;
} else {
 lean_dec_ref(x_534);
 x_538 = lean_box(0);
}
lean_inc(x_535);
x_539 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_537, x_516, x_535);
if (lean_is_scalar(x_538)) {
 x_540 = lean_alloc_ctor(0, 2, 0);
} else {
 x_540 = x_538;
}
lean_ctor_set(x_540, 0, x_536);
lean_ctor_set(x_540, 1, x_539);
x_541 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_541, 0, x_535);
lean_ctor_set(x_541, 1, x_540);
return x_541;
}
}
else
{
lean_object* x_542; lean_object* x_543; 
lean_dec(x_516);
lean_dec(x_1);
x_542 = lean_ctor_get(x_521, 0);
lean_inc(x_542);
lean_dec(x_521);
x_543 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_543, 0, x_542);
lean_ctor_set(x_543, 1, x_501);
return x_543;
}
}
}
else
{
lean_object* x_544; lean_object* x_545; 
x_544 = lean_ctor_get(x_501, 1);
lean_inc(x_544);
x_545 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_544, x_516);
lean_dec(x_544);
if (lean_obj_tag(x_545) == 0)
{
lean_object* x_546; uint8_t x_547; 
lean_inc(x_516);
x_546 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_516, x_501);
x_547 = !lean_is_exclusive(x_546);
if (x_547 == 0)
{
lean_object* x_548; uint8_t x_549; 
x_548 = lean_ctor_get(x_546, 1);
x_549 = !lean_is_exclusive(x_548);
if (x_549 == 0)
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; 
x_550 = lean_ctor_get(x_546, 0);
x_551 = lean_ctor_get(x_548, 1);
lean_inc(x_550);
x_552 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_551, x_516, x_550);
lean_ctor_set(x_548, 1, x_552);
return x_546;
}
else
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; 
x_553 = lean_ctor_get(x_546, 0);
x_554 = lean_ctor_get(x_548, 0);
x_555 = lean_ctor_get(x_548, 1);
lean_inc(x_555);
lean_inc(x_554);
lean_dec(x_548);
lean_inc(x_553);
x_556 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_555, x_516, x_553);
x_557 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_557, 0, x_554);
lean_ctor_set(x_557, 1, x_556);
lean_ctor_set(x_546, 1, x_557);
return x_546;
}
}
else
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; 
x_558 = lean_ctor_get(x_546, 1);
x_559 = lean_ctor_get(x_546, 0);
lean_inc(x_558);
lean_inc(x_559);
lean_dec(x_546);
x_560 = lean_ctor_get(x_558, 0);
lean_inc(x_560);
x_561 = lean_ctor_get(x_558, 1);
lean_inc(x_561);
if (lean_is_exclusive(x_558)) {
 lean_ctor_release(x_558, 0);
 lean_ctor_release(x_558, 1);
 x_562 = x_558;
} else {
 lean_dec_ref(x_558);
 x_562 = lean_box(0);
}
lean_inc(x_559);
x_563 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_561, x_516, x_559);
if (lean_is_scalar(x_562)) {
 x_564 = lean_alloc_ctor(0, 2, 0);
} else {
 x_564 = x_562;
}
lean_ctor_set(x_564, 0, x_560);
lean_ctor_set(x_564, 1, x_563);
x_565 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_565, 0, x_559);
lean_ctor_set(x_565, 1, x_564);
return x_565;
}
}
else
{
lean_object* x_566; lean_object* x_567; 
lean_dec(x_516);
lean_dec(x_1);
x_566 = lean_ctor_get(x_545, 0);
lean_inc(x_566);
lean_dec(x_545);
x_567 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_567, 0, x_566);
lean_ctor_set(x_567, 1, x_501);
return x_567;
}
}
}
}
block_512:
{
lean_object* x_503; lean_object* x_504; uint8_t x_505; 
lean_dec(x_502);
x_503 = lean_unsigned_to_nat(0u);
x_504 = l_Array_ummapAux___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__4___rarg(x_1, x_503, x_3, x_501);
x_505 = !lean_is_exclusive(x_504);
if (x_505 == 0)
{
lean_object* x_506; lean_object* x_507; 
x_506 = lean_ctor_get(x_504, 0);
x_507 = l_Lean_mkAppRev(x_500, x_506);
lean_dec(x_506);
lean_ctor_set(x_504, 0, x_507);
return x_504;
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; 
x_508 = lean_ctor_get(x_504, 0);
x_509 = lean_ctor_get(x_504, 1);
lean_inc(x_509);
lean_inc(x_508);
lean_dec(x_504);
x_510 = l_Lean_mkAppRev(x_500, x_508);
lean_dec(x_508);
x_511 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_511, 0, x_510);
lean_ctor_set(x_511, 1, x_509);
return x_511;
}
}
}
}
case 7:
{
uint8_t x_597; lean_object* x_598; lean_object* x_599; uint8_t x_667; 
x_597 = l_Lean_Expr_isMVar(x_2);
x_667 = lean_expr_has_expr_mvar(x_2);
if (x_667 == 0)
{
uint8_t x_668; 
x_668 = lean_expr_has_level_mvar(x_2);
if (x_668 == 0)
{
x_598 = x_2;
x_599 = x_4;
goto block_666;
}
else
{
lean_object* x_669; lean_object* x_670; 
x_669 = lean_ctor_get(x_4, 1);
lean_inc(x_669);
x_670 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_669, x_2);
lean_dec(x_669);
if (lean_obj_tag(x_670) == 0)
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; uint8_t x_674; 
lean_inc(x_2);
lean_inc(x_1);
x_671 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_2, x_4);
x_672 = lean_ctor_get(x_671, 1);
lean_inc(x_672);
x_673 = lean_ctor_get(x_671, 0);
lean_inc(x_673);
lean_dec(x_671);
x_674 = !lean_is_exclusive(x_672);
if (x_674 == 0)
{
lean_object* x_675; lean_object* x_676; 
x_675 = lean_ctor_get(x_672, 1);
lean_inc(x_673);
x_676 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_675, x_2, x_673);
lean_ctor_set(x_672, 1, x_676);
x_598 = x_673;
x_599 = x_672;
goto block_666;
}
else
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; 
x_677 = lean_ctor_get(x_672, 0);
x_678 = lean_ctor_get(x_672, 1);
lean_inc(x_678);
lean_inc(x_677);
lean_dec(x_672);
lean_inc(x_673);
x_679 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_678, x_2, x_673);
x_680 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_680, 0, x_677);
lean_ctor_set(x_680, 1, x_679);
x_598 = x_673;
x_599 = x_680;
goto block_666;
}
}
else
{
lean_object* x_681; 
lean_dec(x_2);
x_681 = lean_ctor_get(x_670, 0);
lean_inc(x_681);
lean_dec(x_670);
x_598 = x_681;
x_599 = x_4;
goto block_666;
}
}
}
else
{
lean_object* x_682; lean_object* x_683; 
x_682 = lean_ctor_get(x_4, 1);
lean_inc(x_682);
x_683 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_682, x_2);
lean_dec(x_682);
if (lean_obj_tag(x_683) == 0)
{
lean_object* x_684; lean_object* x_685; lean_object* x_686; uint8_t x_687; 
lean_inc(x_2);
lean_inc(x_1);
x_684 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_2, x_4);
x_685 = lean_ctor_get(x_684, 1);
lean_inc(x_685);
x_686 = lean_ctor_get(x_684, 0);
lean_inc(x_686);
lean_dec(x_684);
x_687 = !lean_is_exclusive(x_685);
if (x_687 == 0)
{
lean_object* x_688; lean_object* x_689; 
x_688 = lean_ctor_get(x_685, 1);
lean_inc(x_686);
x_689 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_688, x_2, x_686);
lean_ctor_set(x_685, 1, x_689);
x_598 = x_686;
x_599 = x_685;
goto block_666;
}
else
{
lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; 
x_690 = lean_ctor_get(x_685, 0);
x_691 = lean_ctor_get(x_685, 1);
lean_inc(x_691);
lean_inc(x_690);
lean_dec(x_685);
lean_inc(x_686);
x_692 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_691, x_2, x_686);
x_693 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_693, 0, x_690);
lean_ctor_set(x_693, 1, x_692);
x_598 = x_686;
x_599 = x_693;
goto block_666;
}
}
else
{
lean_object* x_694; 
lean_dec(x_2);
x_694 = lean_ctor_get(x_683, 0);
lean_inc(x_694);
lean_dec(x_683);
x_598 = x_694;
x_599 = x_4;
goto block_666;
}
}
block_666:
{
lean_object* x_600; 
if (x_597 == 0)
{
lean_object* x_611; 
x_611 = lean_box(0);
x_600 = x_611;
goto block_610;
}
else
{
uint8_t x_612; 
x_612 = l_Lean_Expr_isLambda(x_598);
if (x_612 == 0)
{
lean_object* x_613; 
x_613 = lean_box(0);
x_600 = x_613;
goto block_610;
}
else
{
lean_object* x_614; uint8_t x_615; 
x_614 = l_Lean_Expr_betaRev(x_598, x_3);
lean_dec(x_598);
x_615 = lean_expr_has_expr_mvar(x_614);
if (x_615 == 0)
{
uint8_t x_616; 
x_616 = lean_expr_has_level_mvar(x_614);
if (x_616 == 0)
{
lean_object* x_617; 
lean_dec(x_1);
x_617 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_617, 0, x_614);
lean_ctor_set(x_617, 1, x_599);
return x_617;
}
else
{
lean_object* x_618; lean_object* x_619; 
x_618 = lean_ctor_get(x_599, 1);
lean_inc(x_618);
x_619 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_618, x_614);
lean_dec(x_618);
if (lean_obj_tag(x_619) == 0)
{
lean_object* x_620; uint8_t x_621; 
lean_inc(x_614);
x_620 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_614, x_599);
x_621 = !lean_is_exclusive(x_620);
if (x_621 == 0)
{
lean_object* x_622; uint8_t x_623; 
x_622 = lean_ctor_get(x_620, 1);
x_623 = !lean_is_exclusive(x_622);
if (x_623 == 0)
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; 
x_624 = lean_ctor_get(x_620, 0);
x_625 = lean_ctor_get(x_622, 1);
lean_inc(x_624);
x_626 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_625, x_614, x_624);
lean_ctor_set(x_622, 1, x_626);
return x_620;
}
else
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; 
x_627 = lean_ctor_get(x_620, 0);
x_628 = lean_ctor_get(x_622, 0);
x_629 = lean_ctor_get(x_622, 1);
lean_inc(x_629);
lean_inc(x_628);
lean_dec(x_622);
lean_inc(x_627);
x_630 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_629, x_614, x_627);
x_631 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_631, 0, x_628);
lean_ctor_set(x_631, 1, x_630);
lean_ctor_set(x_620, 1, x_631);
return x_620;
}
}
else
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; 
x_632 = lean_ctor_get(x_620, 1);
x_633 = lean_ctor_get(x_620, 0);
lean_inc(x_632);
lean_inc(x_633);
lean_dec(x_620);
x_634 = lean_ctor_get(x_632, 0);
lean_inc(x_634);
x_635 = lean_ctor_get(x_632, 1);
lean_inc(x_635);
if (lean_is_exclusive(x_632)) {
 lean_ctor_release(x_632, 0);
 lean_ctor_release(x_632, 1);
 x_636 = x_632;
} else {
 lean_dec_ref(x_632);
 x_636 = lean_box(0);
}
lean_inc(x_633);
x_637 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_635, x_614, x_633);
if (lean_is_scalar(x_636)) {
 x_638 = lean_alloc_ctor(0, 2, 0);
} else {
 x_638 = x_636;
}
lean_ctor_set(x_638, 0, x_634);
lean_ctor_set(x_638, 1, x_637);
x_639 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_639, 0, x_633);
lean_ctor_set(x_639, 1, x_638);
return x_639;
}
}
else
{
lean_object* x_640; lean_object* x_641; 
lean_dec(x_614);
lean_dec(x_1);
x_640 = lean_ctor_get(x_619, 0);
lean_inc(x_640);
lean_dec(x_619);
x_641 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_641, 0, x_640);
lean_ctor_set(x_641, 1, x_599);
return x_641;
}
}
}
else
{
lean_object* x_642; lean_object* x_643; 
x_642 = lean_ctor_get(x_599, 1);
lean_inc(x_642);
x_643 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_642, x_614);
lean_dec(x_642);
if (lean_obj_tag(x_643) == 0)
{
lean_object* x_644; uint8_t x_645; 
lean_inc(x_614);
x_644 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_614, x_599);
x_645 = !lean_is_exclusive(x_644);
if (x_645 == 0)
{
lean_object* x_646; uint8_t x_647; 
x_646 = lean_ctor_get(x_644, 1);
x_647 = !lean_is_exclusive(x_646);
if (x_647 == 0)
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; 
x_648 = lean_ctor_get(x_644, 0);
x_649 = lean_ctor_get(x_646, 1);
lean_inc(x_648);
x_650 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_649, x_614, x_648);
lean_ctor_set(x_646, 1, x_650);
return x_644;
}
else
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; 
x_651 = lean_ctor_get(x_644, 0);
x_652 = lean_ctor_get(x_646, 0);
x_653 = lean_ctor_get(x_646, 1);
lean_inc(x_653);
lean_inc(x_652);
lean_dec(x_646);
lean_inc(x_651);
x_654 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_653, x_614, x_651);
x_655 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_655, 0, x_652);
lean_ctor_set(x_655, 1, x_654);
lean_ctor_set(x_644, 1, x_655);
return x_644;
}
}
else
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; 
x_656 = lean_ctor_get(x_644, 1);
x_657 = lean_ctor_get(x_644, 0);
lean_inc(x_656);
lean_inc(x_657);
lean_dec(x_644);
x_658 = lean_ctor_get(x_656, 0);
lean_inc(x_658);
x_659 = lean_ctor_get(x_656, 1);
lean_inc(x_659);
if (lean_is_exclusive(x_656)) {
 lean_ctor_release(x_656, 0);
 lean_ctor_release(x_656, 1);
 x_660 = x_656;
} else {
 lean_dec_ref(x_656);
 x_660 = lean_box(0);
}
lean_inc(x_657);
x_661 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_659, x_614, x_657);
if (lean_is_scalar(x_660)) {
 x_662 = lean_alloc_ctor(0, 2, 0);
} else {
 x_662 = x_660;
}
lean_ctor_set(x_662, 0, x_658);
lean_ctor_set(x_662, 1, x_661);
x_663 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_663, 0, x_657);
lean_ctor_set(x_663, 1, x_662);
return x_663;
}
}
else
{
lean_object* x_664; lean_object* x_665; 
lean_dec(x_614);
lean_dec(x_1);
x_664 = lean_ctor_get(x_643, 0);
lean_inc(x_664);
lean_dec(x_643);
x_665 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_665, 0, x_664);
lean_ctor_set(x_665, 1, x_599);
return x_665;
}
}
}
}
block_610:
{
lean_object* x_601; lean_object* x_602; uint8_t x_603; 
lean_dec(x_600);
x_601 = lean_unsigned_to_nat(0u);
x_602 = l_Array_ummapAux___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__4___rarg(x_1, x_601, x_3, x_599);
x_603 = !lean_is_exclusive(x_602);
if (x_603 == 0)
{
lean_object* x_604; lean_object* x_605; 
x_604 = lean_ctor_get(x_602, 0);
x_605 = l_Lean_mkAppRev(x_598, x_604);
lean_dec(x_604);
lean_ctor_set(x_602, 0, x_605);
return x_602;
}
else
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; 
x_606 = lean_ctor_get(x_602, 0);
x_607 = lean_ctor_get(x_602, 1);
lean_inc(x_607);
lean_inc(x_606);
lean_dec(x_602);
x_608 = l_Lean_mkAppRev(x_598, x_606);
lean_dec(x_606);
x_609 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_609, 0, x_608);
lean_ctor_set(x_609, 1, x_607);
return x_609;
}
}
}
}
case 8:
{
uint8_t x_695; lean_object* x_696; lean_object* x_697; uint8_t x_765; 
x_695 = l_Lean_Expr_isMVar(x_2);
x_765 = lean_expr_has_expr_mvar(x_2);
if (x_765 == 0)
{
uint8_t x_766; 
x_766 = lean_expr_has_level_mvar(x_2);
if (x_766 == 0)
{
x_696 = x_2;
x_697 = x_4;
goto block_764;
}
else
{
lean_object* x_767; lean_object* x_768; 
x_767 = lean_ctor_get(x_4, 1);
lean_inc(x_767);
x_768 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_767, x_2);
lean_dec(x_767);
if (lean_obj_tag(x_768) == 0)
{
lean_object* x_769; lean_object* x_770; lean_object* x_771; uint8_t x_772; 
lean_inc(x_2);
lean_inc(x_1);
x_769 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_2, x_4);
x_770 = lean_ctor_get(x_769, 1);
lean_inc(x_770);
x_771 = lean_ctor_get(x_769, 0);
lean_inc(x_771);
lean_dec(x_769);
x_772 = !lean_is_exclusive(x_770);
if (x_772 == 0)
{
lean_object* x_773; lean_object* x_774; 
x_773 = lean_ctor_get(x_770, 1);
lean_inc(x_771);
x_774 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_773, x_2, x_771);
lean_ctor_set(x_770, 1, x_774);
x_696 = x_771;
x_697 = x_770;
goto block_764;
}
else
{
lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; 
x_775 = lean_ctor_get(x_770, 0);
x_776 = lean_ctor_get(x_770, 1);
lean_inc(x_776);
lean_inc(x_775);
lean_dec(x_770);
lean_inc(x_771);
x_777 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_776, x_2, x_771);
x_778 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_778, 0, x_775);
lean_ctor_set(x_778, 1, x_777);
x_696 = x_771;
x_697 = x_778;
goto block_764;
}
}
else
{
lean_object* x_779; 
lean_dec(x_2);
x_779 = lean_ctor_get(x_768, 0);
lean_inc(x_779);
lean_dec(x_768);
x_696 = x_779;
x_697 = x_4;
goto block_764;
}
}
}
else
{
lean_object* x_780; lean_object* x_781; 
x_780 = lean_ctor_get(x_4, 1);
lean_inc(x_780);
x_781 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_780, x_2);
lean_dec(x_780);
if (lean_obj_tag(x_781) == 0)
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; uint8_t x_785; 
lean_inc(x_2);
lean_inc(x_1);
x_782 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_2, x_4);
x_783 = lean_ctor_get(x_782, 1);
lean_inc(x_783);
x_784 = lean_ctor_get(x_782, 0);
lean_inc(x_784);
lean_dec(x_782);
x_785 = !lean_is_exclusive(x_783);
if (x_785 == 0)
{
lean_object* x_786; lean_object* x_787; 
x_786 = lean_ctor_get(x_783, 1);
lean_inc(x_784);
x_787 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_786, x_2, x_784);
lean_ctor_set(x_783, 1, x_787);
x_696 = x_784;
x_697 = x_783;
goto block_764;
}
else
{
lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; 
x_788 = lean_ctor_get(x_783, 0);
x_789 = lean_ctor_get(x_783, 1);
lean_inc(x_789);
lean_inc(x_788);
lean_dec(x_783);
lean_inc(x_784);
x_790 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_789, x_2, x_784);
x_791 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_791, 0, x_788);
lean_ctor_set(x_791, 1, x_790);
x_696 = x_784;
x_697 = x_791;
goto block_764;
}
}
else
{
lean_object* x_792; 
lean_dec(x_2);
x_792 = lean_ctor_get(x_781, 0);
lean_inc(x_792);
lean_dec(x_781);
x_696 = x_792;
x_697 = x_4;
goto block_764;
}
}
block_764:
{
lean_object* x_698; 
if (x_695 == 0)
{
lean_object* x_709; 
x_709 = lean_box(0);
x_698 = x_709;
goto block_708;
}
else
{
uint8_t x_710; 
x_710 = l_Lean_Expr_isLambda(x_696);
if (x_710 == 0)
{
lean_object* x_711; 
x_711 = lean_box(0);
x_698 = x_711;
goto block_708;
}
else
{
lean_object* x_712; uint8_t x_713; 
x_712 = l_Lean_Expr_betaRev(x_696, x_3);
lean_dec(x_696);
x_713 = lean_expr_has_expr_mvar(x_712);
if (x_713 == 0)
{
uint8_t x_714; 
x_714 = lean_expr_has_level_mvar(x_712);
if (x_714 == 0)
{
lean_object* x_715; 
lean_dec(x_1);
x_715 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_715, 0, x_712);
lean_ctor_set(x_715, 1, x_697);
return x_715;
}
else
{
lean_object* x_716; lean_object* x_717; 
x_716 = lean_ctor_get(x_697, 1);
lean_inc(x_716);
x_717 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_716, x_712);
lean_dec(x_716);
if (lean_obj_tag(x_717) == 0)
{
lean_object* x_718; uint8_t x_719; 
lean_inc(x_712);
x_718 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_712, x_697);
x_719 = !lean_is_exclusive(x_718);
if (x_719 == 0)
{
lean_object* x_720; uint8_t x_721; 
x_720 = lean_ctor_get(x_718, 1);
x_721 = !lean_is_exclusive(x_720);
if (x_721 == 0)
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; 
x_722 = lean_ctor_get(x_718, 0);
x_723 = lean_ctor_get(x_720, 1);
lean_inc(x_722);
x_724 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_723, x_712, x_722);
lean_ctor_set(x_720, 1, x_724);
return x_718;
}
else
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; 
x_725 = lean_ctor_get(x_718, 0);
x_726 = lean_ctor_get(x_720, 0);
x_727 = lean_ctor_get(x_720, 1);
lean_inc(x_727);
lean_inc(x_726);
lean_dec(x_720);
lean_inc(x_725);
x_728 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_727, x_712, x_725);
x_729 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_729, 0, x_726);
lean_ctor_set(x_729, 1, x_728);
lean_ctor_set(x_718, 1, x_729);
return x_718;
}
}
else
{
lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; 
x_730 = lean_ctor_get(x_718, 1);
x_731 = lean_ctor_get(x_718, 0);
lean_inc(x_730);
lean_inc(x_731);
lean_dec(x_718);
x_732 = lean_ctor_get(x_730, 0);
lean_inc(x_732);
x_733 = lean_ctor_get(x_730, 1);
lean_inc(x_733);
if (lean_is_exclusive(x_730)) {
 lean_ctor_release(x_730, 0);
 lean_ctor_release(x_730, 1);
 x_734 = x_730;
} else {
 lean_dec_ref(x_730);
 x_734 = lean_box(0);
}
lean_inc(x_731);
x_735 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_733, x_712, x_731);
if (lean_is_scalar(x_734)) {
 x_736 = lean_alloc_ctor(0, 2, 0);
} else {
 x_736 = x_734;
}
lean_ctor_set(x_736, 0, x_732);
lean_ctor_set(x_736, 1, x_735);
x_737 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_737, 0, x_731);
lean_ctor_set(x_737, 1, x_736);
return x_737;
}
}
else
{
lean_object* x_738; lean_object* x_739; 
lean_dec(x_712);
lean_dec(x_1);
x_738 = lean_ctor_get(x_717, 0);
lean_inc(x_738);
lean_dec(x_717);
x_739 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_739, 0, x_738);
lean_ctor_set(x_739, 1, x_697);
return x_739;
}
}
}
else
{
lean_object* x_740; lean_object* x_741; 
x_740 = lean_ctor_get(x_697, 1);
lean_inc(x_740);
x_741 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_740, x_712);
lean_dec(x_740);
if (lean_obj_tag(x_741) == 0)
{
lean_object* x_742; uint8_t x_743; 
lean_inc(x_712);
x_742 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_712, x_697);
x_743 = !lean_is_exclusive(x_742);
if (x_743 == 0)
{
lean_object* x_744; uint8_t x_745; 
x_744 = lean_ctor_get(x_742, 1);
x_745 = !lean_is_exclusive(x_744);
if (x_745 == 0)
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; 
x_746 = lean_ctor_get(x_742, 0);
x_747 = lean_ctor_get(x_744, 1);
lean_inc(x_746);
x_748 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_747, x_712, x_746);
lean_ctor_set(x_744, 1, x_748);
return x_742;
}
else
{
lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; 
x_749 = lean_ctor_get(x_742, 0);
x_750 = lean_ctor_get(x_744, 0);
x_751 = lean_ctor_get(x_744, 1);
lean_inc(x_751);
lean_inc(x_750);
lean_dec(x_744);
lean_inc(x_749);
x_752 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_751, x_712, x_749);
x_753 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_753, 0, x_750);
lean_ctor_set(x_753, 1, x_752);
lean_ctor_set(x_742, 1, x_753);
return x_742;
}
}
else
{
lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; 
x_754 = lean_ctor_get(x_742, 1);
x_755 = lean_ctor_get(x_742, 0);
lean_inc(x_754);
lean_inc(x_755);
lean_dec(x_742);
x_756 = lean_ctor_get(x_754, 0);
lean_inc(x_756);
x_757 = lean_ctor_get(x_754, 1);
lean_inc(x_757);
if (lean_is_exclusive(x_754)) {
 lean_ctor_release(x_754, 0);
 lean_ctor_release(x_754, 1);
 x_758 = x_754;
} else {
 lean_dec_ref(x_754);
 x_758 = lean_box(0);
}
lean_inc(x_755);
x_759 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_757, x_712, x_755);
if (lean_is_scalar(x_758)) {
 x_760 = lean_alloc_ctor(0, 2, 0);
} else {
 x_760 = x_758;
}
lean_ctor_set(x_760, 0, x_756);
lean_ctor_set(x_760, 1, x_759);
x_761 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_761, 0, x_755);
lean_ctor_set(x_761, 1, x_760);
return x_761;
}
}
else
{
lean_object* x_762; lean_object* x_763; 
lean_dec(x_712);
lean_dec(x_1);
x_762 = lean_ctor_get(x_741, 0);
lean_inc(x_762);
lean_dec(x_741);
x_763 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_763, 0, x_762);
lean_ctor_set(x_763, 1, x_697);
return x_763;
}
}
}
}
block_708:
{
lean_object* x_699; lean_object* x_700; uint8_t x_701; 
lean_dec(x_698);
x_699 = lean_unsigned_to_nat(0u);
x_700 = l_Array_ummapAux___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__4___rarg(x_1, x_699, x_3, x_697);
x_701 = !lean_is_exclusive(x_700);
if (x_701 == 0)
{
lean_object* x_702; lean_object* x_703; 
x_702 = lean_ctor_get(x_700, 0);
x_703 = l_Lean_mkAppRev(x_696, x_702);
lean_dec(x_702);
lean_ctor_set(x_700, 0, x_703);
return x_700;
}
else
{
lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; 
x_704 = lean_ctor_get(x_700, 0);
x_705 = lean_ctor_get(x_700, 1);
lean_inc(x_705);
lean_inc(x_704);
lean_dec(x_700);
x_706 = l_Lean_mkAppRev(x_696, x_704);
lean_dec(x_704);
x_707 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_707, 0, x_706);
lean_ctor_set(x_707, 1, x_705);
return x_707;
}
}
}
}
case 9:
{
uint8_t x_793; lean_object* x_794; lean_object* x_795; uint8_t x_863; 
x_793 = l_Lean_Expr_isMVar(x_2);
x_863 = lean_expr_has_expr_mvar(x_2);
if (x_863 == 0)
{
uint8_t x_864; 
x_864 = lean_expr_has_level_mvar(x_2);
if (x_864 == 0)
{
x_794 = x_2;
x_795 = x_4;
goto block_862;
}
else
{
lean_object* x_865; lean_object* x_866; 
x_865 = lean_ctor_get(x_4, 1);
lean_inc(x_865);
x_866 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_865, x_2);
lean_dec(x_865);
if (lean_obj_tag(x_866) == 0)
{
lean_object* x_867; lean_object* x_868; lean_object* x_869; uint8_t x_870; 
lean_inc(x_2);
lean_inc(x_1);
x_867 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_2, x_4);
x_868 = lean_ctor_get(x_867, 1);
lean_inc(x_868);
x_869 = lean_ctor_get(x_867, 0);
lean_inc(x_869);
lean_dec(x_867);
x_870 = !lean_is_exclusive(x_868);
if (x_870 == 0)
{
lean_object* x_871; lean_object* x_872; 
x_871 = lean_ctor_get(x_868, 1);
lean_inc(x_869);
x_872 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_871, x_2, x_869);
lean_ctor_set(x_868, 1, x_872);
x_794 = x_869;
x_795 = x_868;
goto block_862;
}
else
{
lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; 
x_873 = lean_ctor_get(x_868, 0);
x_874 = lean_ctor_get(x_868, 1);
lean_inc(x_874);
lean_inc(x_873);
lean_dec(x_868);
lean_inc(x_869);
x_875 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_874, x_2, x_869);
x_876 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_876, 0, x_873);
lean_ctor_set(x_876, 1, x_875);
x_794 = x_869;
x_795 = x_876;
goto block_862;
}
}
else
{
lean_object* x_877; 
lean_dec(x_2);
x_877 = lean_ctor_get(x_866, 0);
lean_inc(x_877);
lean_dec(x_866);
x_794 = x_877;
x_795 = x_4;
goto block_862;
}
}
}
else
{
lean_object* x_878; lean_object* x_879; 
x_878 = lean_ctor_get(x_4, 1);
lean_inc(x_878);
x_879 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_878, x_2);
lean_dec(x_878);
if (lean_obj_tag(x_879) == 0)
{
lean_object* x_880; lean_object* x_881; lean_object* x_882; uint8_t x_883; 
lean_inc(x_2);
lean_inc(x_1);
x_880 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_2, x_4);
x_881 = lean_ctor_get(x_880, 1);
lean_inc(x_881);
x_882 = lean_ctor_get(x_880, 0);
lean_inc(x_882);
lean_dec(x_880);
x_883 = !lean_is_exclusive(x_881);
if (x_883 == 0)
{
lean_object* x_884; lean_object* x_885; 
x_884 = lean_ctor_get(x_881, 1);
lean_inc(x_882);
x_885 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_884, x_2, x_882);
lean_ctor_set(x_881, 1, x_885);
x_794 = x_882;
x_795 = x_881;
goto block_862;
}
else
{
lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; 
x_886 = lean_ctor_get(x_881, 0);
x_887 = lean_ctor_get(x_881, 1);
lean_inc(x_887);
lean_inc(x_886);
lean_dec(x_881);
lean_inc(x_882);
x_888 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_887, x_2, x_882);
x_889 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_889, 0, x_886);
lean_ctor_set(x_889, 1, x_888);
x_794 = x_882;
x_795 = x_889;
goto block_862;
}
}
else
{
lean_object* x_890; 
lean_dec(x_2);
x_890 = lean_ctor_get(x_879, 0);
lean_inc(x_890);
lean_dec(x_879);
x_794 = x_890;
x_795 = x_4;
goto block_862;
}
}
block_862:
{
lean_object* x_796; 
if (x_793 == 0)
{
lean_object* x_807; 
x_807 = lean_box(0);
x_796 = x_807;
goto block_806;
}
else
{
uint8_t x_808; 
x_808 = l_Lean_Expr_isLambda(x_794);
if (x_808 == 0)
{
lean_object* x_809; 
x_809 = lean_box(0);
x_796 = x_809;
goto block_806;
}
else
{
lean_object* x_810; uint8_t x_811; 
x_810 = l_Lean_Expr_betaRev(x_794, x_3);
lean_dec(x_794);
x_811 = lean_expr_has_expr_mvar(x_810);
if (x_811 == 0)
{
uint8_t x_812; 
x_812 = lean_expr_has_level_mvar(x_810);
if (x_812 == 0)
{
lean_object* x_813; 
lean_dec(x_1);
x_813 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_813, 0, x_810);
lean_ctor_set(x_813, 1, x_795);
return x_813;
}
else
{
lean_object* x_814; lean_object* x_815; 
x_814 = lean_ctor_get(x_795, 1);
lean_inc(x_814);
x_815 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_814, x_810);
lean_dec(x_814);
if (lean_obj_tag(x_815) == 0)
{
lean_object* x_816; uint8_t x_817; 
lean_inc(x_810);
x_816 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_810, x_795);
x_817 = !lean_is_exclusive(x_816);
if (x_817 == 0)
{
lean_object* x_818; uint8_t x_819; 
x_818 = lean_ctor_get(x_816, 1);
x_819 = !lean_is_exclusive(x_818);
if (x_819 == 0)
{
lean_object* x_820; lean_object* x_821; lean_object* x_822; 
x_820 = lean_ctor_get(x_816, 0);
x_821 = lean_ctor_get(x_818, 1);
lean_inc(x_820);
x_822 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_821, x_810, x_820);
lean_ctor_set(x_818, 1, x_822);
return x_816;
}
else
{
lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; 
x_823 = lean_ctor_get(x_816, 0);
x_824 = lean_ctor_get(x_818, 0);
x_825 = lean_ctor_get(x_818, 1);
lean_inc(x_825);
lean_inc(x_824);
lean_dec(x_818);
lean_inc(x_823);
x_826 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_825, x_810, x_823);
x_827 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_827, 0, x_824);
lean_ctor_set(x_827, 1, x_826);
lean_ctor_set(x_816, 1, x_827);
return x_816;
}
}
else
{
lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; 
x_828 = lean_ctor_get(x_816, 1);
x_829 = lean_ctor_get(x_816, 0);
lean_inc(x_828);
lean_inc(x_829);
lean_dec(x_816);
x_830 = lean_ctor_get(x_828, 0);
lean_inc(x_830);
x_831 = lean_ctor_get(x_828, 1);
lean_inc(x_831);
if (lean_is_exclusive(x_828)) {
 lean_ctor_release(x_828, 0);
 lean_ctor_release(x_828, 1);
 x_832 = x_828;
} else {
 lean_dec_ref(x_828);
 x_832 = lean_box(0);
}
lean_inc(x_829);
x_833 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_831, x_810, x_829);
if (lean_is_scalar(x_832)) {
 x_834 = lean_alloc_ctor(0, 2, 0);
} else {
 x_834 = x_832;
}
lean_ctor_set(x_834, 0, x_830);
lean_ctor_set(x_834, 1, x_833);
x_835 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_835, 0, x_829);
lean_ctor_set(x_835, 1, x_834);
return x_835;
}
}
else
{
lean_object* x_836; lean_object* x_837; 
lean_dec(x_810);
lean_dec(x_1);
x_836 = lean_ctor_get(x_815, 0);
lean_inc(x_836);
lean_dec(x_815);
x_837 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_837, 0, x_836);
lean_ctor_set(x_837, 1, x_795);
return x_837;
}
}
}
else
{
lean_object* x_838; lean_object* x_839; 
x_838 = lean_ctor_get(x_795, 1);
lean_inc(x_838);
x_839 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_838, x_810);
lean_dec(x_838);
if (lean_obj_tag(x_839) == 0)
{
lean_object* x_840; uint8_t x_841; 
lean_inc(x_810);
x_840 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_810, x_795);
x_841 = !lean_is_exclusive(x_840);
if (x_841 == 0)
{
lean_object* x_842; uint8_t x_843; 
x_842 = lean_ctor_get(x_840, 1);
x_843 = !lean_is_exclusive(x_842);
if (x_843 == 0)
{
lean_object* x_844; lean_object* x_845; lean_object* x_846; 
x_844 = lean_ctor_get(x_840, 0);
x_845 = lean_ctor_get(x_842, 1);
lean_inc(x_844);
x_846 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_845, x_810, x_844);
lean_ctor_set(x_842, 1, x_846);
return x_840;
}
else
{
lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; 
x_847 = lean_ctor_get(x_840, 0);
x_848 = lean_ctor_get(x_842, 0);
x_849 = lean_ctor_get(x_842, 1);
lean_inc(x_849);
lean_inc(x_848);
lean_dec(x_842);
lean_inc(x_847);
x_850 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_849, x_810, x_847);
x_851 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_851, 0, x_848);
lean_ctor_set(x_851, 1, x_850);
lean_ctor_set(x_840, 1, x_851);
return x_840;
}
}
else
{
lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; 
x_852 = lean_ctor_get(x_840, 1);
x_853 = lean_ctor_get(x_840, 0);
lean_inc(x_852);
lean_inc(x_853);
lean_dec(x_840);
x_854 = lean_ctor_get(x_852, 0);
lean_inc(x_854);
x_855 = lean_ctor_get(x_852, 1);
lean_inc(x_855);
if (lean_is_exclusive(x_852)) {
 lean_ctor_release(x_852, 0);
 lean_ctor_release(x_852, 1);
 x_856 = x_852;
} else {
 lean_dec_ref(x_852);
 x_856 = lean_box(0);
}
lean_inc(x_853);
x_857 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_855, x_810, x_853);
if (lean_is_scalar(x_856)) {
 x_858 = lean_alloc_ctor(0, 2, 0);
} else {
 x_858 = x_856;
}
lean_ctor_set(x_858, 0, x_854);
lean_ctor_set(x_858, 1, x_857);
x_859 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_859, 0, x_853);
lean_ctor_set(x_859, 1, x_858);
return x_859;
}
}
else
{
lean_object* x_860; lean_object* x_861; 
lean_dec(x_810);
lean_dec(x_1);
x_860 = lean_ctor_get(x_839, 0);
lean_inc(x_860);
lean_dec(x_839);
x_861 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_861, 0, x_860);
lean_ctor_set(x_861, 1, x_795);
return x_861;
}
}
}
}
block_806:
{
lean_object* x_797; lean_object* x_798; uint8_t x_799; 
lean_dec(x_796);
x_797 = lean_unsigned_to_nat(0u);
x_798 = l_Array_ummapAux___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__4___rarg(x_1, x_797, x_3, x_795);
x_799 = !lean_is_exclusive(x_798);
if (x_799 == 0)
{
lean_object* x_800; lean_object* x_801; 
x_800 = lean_ctor_get(x_798, 0);
x_801 = l_Lean_mkAppRev(x_794, x_800);
lean_dec(x_800);
lean_ctor_set(x_798, 0, x_801);
return x_798;
}
else
{
lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; 
x_802 = lean_ctor_get(x_798, 0);
x_803 = lean_ctor_get(x_798, 1);
lean_inc(x_803);
lean_inc(x_802);
lean_dec(x_798);
x_804 = l_Lean_mkAppRev(x_794, x_802);
lean_dec(x_802);
x_805 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_805, 0, x_804);
lean_ctor_set(x_805, 1, x_803);
return x_805;
}
}
}
}
case 10:
{
uint8_t x_891; lean_object* x_892; lean_object* x_893; uint8_t x_961; 
x_891 = l_Lean_Expr_isMVar(x_2);
x_961 = lean_expr_has_expr_mvar(x_2);
if (x_961 == 0)
{
uint8_t x_962; 
x_962 = lean_expr_has_level_mvar(x_2);
if (x_962 == 0)
{
x_892 = x_2;
x_893 = x_4;
goto block_960;
}
else
{
lean_object* x_963; lean_object* x_964; 
x_963 = lean_ctor_get(x_4, 1);
lean_inc(x_963);
x_964 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_963, x_2);
lean_dec(x_963);
if (lean_obj_tag(x_964) == 0)
{
lean_object* x_965; lean_object* x_966; lean_object* x_967; uint8_t x_968; 
lean_inc(x_2);
lean_inc(x_1);
x_965 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_2, x_4);
x_966 = lean_ctor_get(x_965, 1);
lean_inc(x_966);
x_967 = lean_ctor_get(x_965, 0);
lean_inc(x_967);
lean_dec(x_965);
x_968 = !lean_is_exclusive(x_966);
if (x_968 == 0)
{
lean_object* x_969; lean_object* x_970; 
x_969 = lean_ctor_get(x_966, 1);
lean_inc(x_967);
x_970 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_969, x_2, x_967);
lean_ctor_set(x_966, 1, x_970);
x_892 = x_967;
x_893 = x_966;
goto block_960;
}
else
{
lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; 
x_971 = lean_ctor_get(x_966, 0);
x_972 = lean_ctor_get(x_966, 1);
lean_inc(x_972);
lean_inc(x_971);
lean_dec(x_966);
lean_inc(x_967);
x_973 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_972, x_2, x_967);
x_974 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_974, 0, x_971);
lean_ctor_set(x_974, 1, x_973);
x_892 = x_967;
x_893 = x_974;
goto block_960;
}
}
else
{
lean_object* x_975; 
lean_dec(x_2);
x_975 = lean_ctor_get(x_964, 0);
lean_inc(x_975);
lean_dec(x_964);
x_892 = x_975;
x_893 = x_4;
goto block_960;
}
}
}
else
{
lean_object* x_976; lean_object* x_977; 
x_976 = lean_ctor_get(x_4, 1);
lean_inc(x_976);
x_977 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_976, x_2);
lean_dec(x_976);
if (lean_obj_tag(x_977) == 0)
{
lean_object* x_978; lean_object* x_979; lean_object* x_980; uint8_t x_981; 
lean_inc(x_2);
lean_inc(x_1);
x_978 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_2, x_4);
x_979 = lean_ctor_get(x_978, 1);
lean_inc(x_979);
x_980 = lean_ctor_get(x_978, 0);
lean_inc(x_980);
lean_dec(x_978);
x_981 = !lean_is_exclusive(x_979);
if (x_981 == 0)
{
lean_object* x_982; lean_object* x_983; 
x_982 = lean_ctor_get(x_979, 1);
lean_inc(x_980);
x_983 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_982, x_2, x_980);
lean_ctor_set(x_979, 1, x_983);
x_892 = x_980;
x_893 = x_979;
goto block_960;
}
else
{
lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; 
x_984 = lean_ctor_get(x_979, 0);
x_985 = lean_ctor_get(x_979, 1);
lean_inc(x_985);
lean_inc(x_984);
lean_dec(x_979);
lean_inc(x_980);
x_986 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_985, x_2, x_980);
x_987 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_987, 0, x_984);
lean_ctor_set(x_987, 1, x_986);
x_892 = x_980;
x_893 = x_987;
goto block_960;
}
}
else
{
lean_object* x_988; 
lean_dec(x_2);
x_988 = lean_ctor_get(x_977, 0);
lean_inc(x_988);
lean_dec(x_977);
x_892 = x_988;
x_893 = x_4;
goto block_960;
}
}
block_960:
{
lean_object* x_894; 
if (x_891 == 0)
{
lean_object* x_905; 
x_905 = lean_box(0);
x_894 = x_905;
goto block_904;
}
else
{
uint8_t x_906; 
x_906 = l_Lean_Expr_isLambda(x_892);
if (x_906 == 0)
{
lean_object* x_907; 
x_907 = lean_box(0);
x_894 = x_907;
goto block_904;
}
else
{
lean_object* x_908; uint8_t x_909; 
x_908 = l_Lean_Expr_betaRev(x_892, x_3);
lean_dec(x_892);
x_909 = lean_expr_has_expr_mvar(x_908);
if (x_909 == 0)
{
uint8_t x_910; 
x_910 = lean_expr_has_level_mvar(x_908);
if (x_910 == 0)
{
lean_object* x_911; 
lean_dec(x_1);
x_911 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_911, 0, x_908);
lean_ctor_set(x_911, 1, x_893);
return x_911;
}
else
{
lean_object* x_912; lean_object* x_913; 
x_912 = lean_ctor_get(x_893, 1);
lean_inc(x_912);
x_913 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_912, x_908);
lean_dec(x_912);
if (lean_obj_tag(x_913) == 0)
{
lean_object* x_914; uint8_t x_915; 
lean_inc(x_908);
x_914 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_908, x_893);
x_915 = !lean_is_exclusive(x_914);
if (x_915 == 0)
{
lean_object* x_916; uint8_t x_917; 
x_916 = lean_ctor_get(x_914, 1);
x_917 = !lean_is_exclusive(x_916);
if (x_917 == 0)
{
lean_object* x_918; lean_object* x_919; lean_object* x_920; 
x_918 = lean_ctor_get(x_914, 0);
x_919 = lean_ctor_get(x_916, 1);
lean_inc(x_918);
x_920 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_919, x_908, x_918);
lean_ctor_set(x_916, 1, x_920);
return x_914;
}
else
{
lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; 
x_921 = lean_ctor_get(x_914, 0);
x_922 = lean_ctor_get(x_916, 0);
x_923 = lean_ctor_get(x_916, 1);
lean_inc(x_923);
lean_inc(x_922);
lean_dec(x_916);
lean_inc(x_921);
x_924 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_923, x_908, x_921);
x_925 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_925, 0, x_922);
lean_ctor_set(x_925, 1, x_924);
lean_ctor_set(x_914, 1, x_925);
return x_914;
}
}
else
{
lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; 
x_926 = lean_ctor_get(x_914, 1);
x_927 = lean_ctor_get(x_914, 0);
lean_inc(x_926);
lean_inc(x_927);
lean_dec(x_914);
x_928 = lean_ctor_get(x_926, 0);
lean_inc(x_928);
x_929 = lean_ctor_get(x_926, 1);
lean_inc(x_929);
if (lean_is_exclusive(x_926)) {
 lean_ctor_release(x_926, 0);
 lean_ctor_release(x_926, 1);
 x_930 = x_926;
} else {
 lean_dec_ref(x_926);
 x_930 = lean_box(0);
}
lean_inc(x_927);
x_931 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_929, x_908, x_927);
if (lean_is_scalar(x_930)) {
 x_932 = lean_alloc_ctor(0, 2, 0);
} else {
 x_932 = x_930;
}
lean_ctor_set(x_932, 0, x_928);
lean_ctor_set(x_932, 1, x_931);
x_933 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_933, 0, x_927);
lean_ctor_set(x_933, 1, x_932);
return x_933;
}
}
else
{
lean_object* x_934; lean_object* x_935; 
lean_dec(x_908);
lean_dec(x_1);
x_934 = lean_ctor_get(x_913, 0);
lean_inc(x_934);
lean_dec(x_913);
x_935 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_935, 0, x_934);
lean_ctor_set(x_935, 1, x_893);
return x_935;
}
}
}
else
{
lean_object* x_936; lean_object* x_937; 
x_936 = lean_ctor_get(x_893, 1);
lean_inc(x_936);
x_937 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_936, x_908);
lean_dec(x_936);
if (lean_obj_tag(x_937) == 0)
{
lean_object* x_938; uint8_t x_939; 
lean_inc(x_908);
x_938 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_908, x_893);
x_939 = !lean_is_exclusive(x_938);
if (x_939 == 0)
{
lean_object* x_940; uint8_t x_941; 
x_940 = lean_ctor_get(x_938, 1);
x_941 = !lean_is_exclusive(x_940);
if (x_941 == 0)
{
lean_object* x_942; lean_object* x_943; lean_object* x_944; 
x_942 = lean_ctor_get(x_938, 0);
x_943 = lean_ctor_get(x_940, 1);
lean_inc(x_942);
x_944 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_943, x_908, x_942);
lean_ctor_set(x_940, 1, x_944);
return x_938;
}
else
{
lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; 
x_945 = lean_ctor_get(x_938, 0);
x_946 = lean_ctor_get(x_940, 0);
x_947 = lean_ctor_get(x_940, 1);
lean_inc(x_947);
lean_inc(x_946);
lean_dec(x_940);
lean_inc(x_945);
x_948 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_947, x_908, x_945);
x_949 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_949, 0, x_946);
lean_ctor_set(x_949, 1, x_948);
lean_ctor_set(x_938, 1, x_949);
return x_938;
}
}
else
{
lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; 
x_950 = lean_ctor_get(x_938, 1);
x_951 = lean_ctor_get(x_938, 0);
lean_inc(x_950);
lean_inc(x_951);
lean_dec(x_938);
x_952 = lean_ctor_get(x_950, 0);
lean_inc(x_952);
x_953 = lean_ctor_get(x_950, 1);
lean_inc(x_953);
if (lean_is_exclusive(x_950)) {
 lean_ctor_release(x_950, 0);
 lean_ctor_release(x_950, 1);
 x_954 = x_950;
} else {
 lean_dec_ref(x_950);
 x_954 = lean_box(0);
}
lean_inc(x_951);
x_955 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_953, x_908, x_951);
if (lean_is_scalar(x_954)) {
 x_956 = lean_alloc_ctor(0, 2, 0);
} else {
 x_956 = x_954;
}
lean_ctor_set(x_956, 0, x_952);
lean_ctor_set(x_956, 1, x_955);
x_957 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_957, 0, x_951);
lean_ctor_set(x_957, 1, x_956);
return x_957;
}
}
else
{
lean_object* x_958; lean_object* x_959; 
lean_dec(x_908);
lean_dec(x_1);
x_958 = lean_ctor_get(x_937, 0);
lean_inc(x_958);
lean_dec(x_937);
x_959 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_959, 0, x_958);
lean_ctor_set(x_959, 1, x_893);
return x_959;
}
}
}
}
block_904:
{
lean_object* x_895; lean_object* x_896; uint8_t x_897; 
lean_dec(x_894);
x_895 = lean_unsigned_to_nat(0u);
x_896 = l_Array_ummapAux___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__4___rarg(x_1, x_895, x_3, x_893);
x_897 = !lean_is_exclusive(x_896);
if (x_897 == 0)
{
lean_object* x_898; lean_object* x_899; 
x_898 = lean_ctor_get(x_896, 0);
x_899 = l_Lean_mkAppRev(x_892, x_898);
lean_dec(x_898);
lean_ctor_set(x_896, 0, x_899);
return x_896;
}
else
{
lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; 
x_900 = lean_ctor_get(x_896, 0);
x_901 = lean_ctor_get(x_896, 1);
lean_inc(x_901);
lean_inc(x_900);
lean_dec(x_896);
x_902 = l_Lean_mkAppRev(x_892, x_900);
lean_dec(x_900);
x_903 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_903, 0, x_902);
lean_ctor_set(x_903, 1, x_901);
return x_903;
}
}
}
}
default: 
{
uint8_t x_989; lean_object* x_990; lean_object* x_991; uint8_t x_1059; 
x_989 = l_Lean_Expr_isMVar(x_2);
x_1059 = lean_expr_has_expr_mvar(x_2);
if (x_1059 == 0)
{
uint8_t x_1060; 
x_1060 = lean_expr_has_level_mvar(x_2);
if (x_1060 == 0)
{
x_990 = x_2;
x_991 = x_4;
goto block_1058;
}
else
{
lean_object* x_1061; lean_object* x_1062; 
x_1061 = lean_ctor_get(x_4, 1);
lean_inc(x_1061);
x_1062 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_1061, x_2);
lean_dec(x_1061);
if (lean_obj_tag(x_1062) == 0)
{
lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; uint8_t x_1066; 
lean_inc(x_2);
lean_inc(x_1);
x_1063 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_2, x_4);
x_1064 = lean_ctor_get(x_1063, 1);
lean_inc(x_1064);
x_1065 = lean_ctor_get(x_1063, 0);
lean_inc(x_1065);
lean_dec(x_1063);
x_1066 = !lean_is_exclusive(x_1064);
if (x_1066 == 0)
{
lean_object* x_1067; lean_object* x_1068; 
x_1067 = lean_ctor_get(x_1064, 1);
lean_inc(x_1065);
x_1068 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_1067, x_2, x_1065);
lean_ctor_set(x_1064, 1, x_1068);
x_990 = x_1065;
x_991 = x_1064;
goto block_1058;
}
else
{
lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; 
x_1069 = lean_ctor_get(x_1064, 0);
x_1070 = lean_ctor_get(x_1064, 1);
lean_inc(x_1070);
lean_inc(x_1069);
lean_dec(x_1064);
lean_inc(x_1065);
x_1071 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_1070, x_2, x_1065);
x_1072 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1072, 0, x_1069);
lean_ctor_set(x_1072, 1, x_1071);
x_990 = x_1065;
x_991 = x_1072;
goto block_1058;
}
}
else
{
lean_object* x_1073; 
lean_dec(x_2);
x_1073 = lean_ctor_get(x_1062, 0);
lean_inc(x_1073);
lean_dec(x_1062);
x_990 = x_1073;
x_991 = x_4;
goto block_1058;
}
}
}
else
{
lean_object* x_1074; lean_object* x_1075; 
x_1074 = lean_ctor_get(x_4, 1);
lean_inc(x_1074);
x_1075 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_1074, x_2);
lean_dec(x_1074);
if (lean_obj_tag(x_1075) == 0)
{
lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; uint8_t x_1079; 
lean_inc(x_2);
lean_inc(x_1);
x_1076 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_2, x_4);
x_1077 = lean_ctor_get(x_1076, 1);
lean_inc(x_1077);
x_1078 = lean_ctor_get(x_1076, 0);
lean_inc(x_1078);
lean_dec(x_1076);
x_1079 = !lean_is_exclusive(x_1077);
if (x_1079 == 0)
{
lean_object* x_1080; lean_object* x_1081; 
x_1080 = lean_ctor_get(x_1077, 1);
lean_inc(x_1078);
x_1081 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_1080, x_2, x_1078);
lean_ctor_set(x_1077, 1, x_1081);
x_990 = x_1078;
x_991 = x_1077;
goto block_1058;
}
else
{
lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; 
x_1082 = lean_ctor_get(x_1077, 0);
x_1083 = lean_ctor_get(x_1077, 1);
lean_inc(x_1083);
lean_inc(x_1082);
lean_dec(x_1077);
lean_inc(x_1078);
x_1084 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_1083, x_2, x_1078);
x_1085 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1085, 0, x_1082);
lean_ctor_set(x_1085, 1, x_1084);
x_990 = x_1078;
x_991 = x_1085;
goto block_1058;
}
}
else
{
lean_object* x_1086; 
lean_dec(x_2);
x_1086 = lean_ctor_get(x_1075, 0);
lean_inc(x_1086);
lean_dec(x_1075);
x_990 = x_1086;
x_991 = x_4;
goto block_1058;
}
}
block_1058:
{
lean_object* x_992; 
if (x_989 == 0)
{
lean_object* x_1003; 
x_1003 = lean_box(0);
x_992 = x_1003;
goto block_1002;
}
else
{
uint8_t x_1004; 
x_1004 = l_Lean_Expr_isLambda(x_990);
if (x_1004 == 0)
{
lean_object* x_1005; 
x_1005 = lean_box(0);
x_992 = x_1005;
goto block_1002;
}
else
{
lean_object* x_1006; uint8_t x_1007; 
x_1006 = l_Lean_Expr_betaRev(x_990, x_3);
lean_dec(x_990);
x_1007 = lean_expr_has_expr_mvar(x_1006);
if (x_1007 == 0)
{
uint8_t x_1008; 
x_1008 = lean_expr_has_level_mvar(x_1006);
if (x_1008 == 0)
{
lean_object* x_1009; 
lean_dec(x_1);
x_1009 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1009, 0, x_1006);
lean_ctor_set(x_1009, 1, x_991);
return x_1009;
}
else
{
lean_object* x_1010; lean_object* x_1011; 
x_1010 = lean_ctor_get(x_991, 1);
lean_inc(x_1010);
x_1011 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_1010, x_1006);
lean_dec(x_1010);
if (lean_obj_tag(x_1011) == 0)
{
lean_object* x_1012; uint8_t x_1013; 
lean_inc(x_1006);
x_1012 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_1006, x_991);
x_1013 = !lean_is_exclusive(x_1012);
if (x_1013 == 0)
{
lean_object* x_1014; uint8_t x_1015; 
x_1014 = lean_ctor_get(x_1012, 1);
x_1015 = !lean_is_exclusive(x_1014);
if (x_1015 == 0)
{
lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; 
x_1016 = lean_ctor_get(x_1012, 0);
x_1017 = lean_ctor_get(x_1014, 1);
lean_inc(x_1016);
x_1018 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_1017, x_1006, x_1016);
lean_ctor_set(x_1014, 1, x_1018);
return x_1012;
}
else
{
lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; 
x_1019 = lean_ctor_get(x_1012, 0);
x_1020 = lean_ctor_get(x_1014, 0);
x_1021 = lean_ctor_get(x_1014, 1);
lean_inc(x_1021);
lean_inc(x_1020);
lean_dec(x_1014);
lean_inc(x_1019);
x_1022 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_1021, x_1006, x_1019);
x_1023 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1023, 0, x_1020);
lean_ctor_set(x_1023, 1, x_1022);
lean_ctor_set(x_1012, 1, x_1023);
return x_1012;
}
}
else
{
lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; 
x_1024 = lean_ctor_get(x_1012, 1);
x_1025 = lean_ctor_get(x_1012, 0);
lean_inc(x_1024);
lean_inc(x_1025);
lean_dec(x_1012);
x_1026 = lean_ctor_get(x_1024, 0);
lean_inc(x_1026);
x_1027 = lean_ctor_get(x_1024, 1);
lean_inc(x_1027);
if (lean_is_exclusive(x_1024)) {
 lean_ctor_release(x_1024, 0);
 lean_ctor_release(x_1024, 1);
 x_1028 = x_1024;
} else {
 lean_dec_ref(x_1024);
 x_1028 = lean_box(0);
}
lean_inc(x_1025);
x_1029 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_1027, x_1006, x_1025);
if (lean_is_scalar(x_1028)) {
 x_1030 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1030 = x_1028;
}
lean_ctor_set(x_1030, 0, x_1026);
lean_ctor_set(x_1030, 1, x_1029);
x_1031 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1031, 0, x_1025);
lean_ctor_set(x_1031, 1, x_1030);
return x_1031;
}
}
else
{
lean_object* x_1032; lean_object* x_1033; 
lean_dec(x_1006);
lean_dec(x_1);
x_1032 = lean_ctor_get(x_1011, 0);
lean_inc(x_1032);
lean_dec(x_1011);
x_1033 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1033, 0, x_1032);
lean_ctor_set(x_1033, 1, x_991);
return x_1033;
}
}
}
else
{
lean_object* x_1034; lean_object* x_1035; 
x_1034 = lean_ctor_get(x_991, 1);
lean_inc(x_1034);
x_1035 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_1034, x_1006);
lean_dec(x_1034);
if (lean_obj_tag(x_1035) == 0)
{
lean_object* x_1036; uint8_t x_1037; 
lean_inc(x_1006);
x_1036 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_1006, x_991);
x_1037 = !lean_is_exclusive(x_1036);
if (x_1037 == 0)
{
lean_object* x_1038; uint8_t x_1039; 
x_1038 = lean_ctor_get(x_1036, 1);
x_1039 = !lean_is_exclusive(x_1038);
if (x_1039 == 0)
{
lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; 
x_1040 = lean_ctor_get(x_1036, 0);
x_1041 = lean_ctor_get(x_1038, 1);
lean_inc(x_1040);
x_1042 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_1041, x_1006, x_1040);
lean_ctor_set(x_1038, 1, x_1042);
return x_1036;
}
else
{
lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; 
x_1043 = lean_ctor_get(x_1036, 0);
x_1044 = lean_ctor_get(x_1038, 0);
x_1045 = lean_ctor_get(x_1038, 1);
lean_inc(x_1045);
lean_inc(x_1044);
lean_dec(x_1038);
lean_inc(x_1043);
x_1046 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_1045, x_1006, x_1043);
x_1047 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1047, 0, x_1044);
lean_ctor_set(x_1047, 1, x_1046);
lean_ctor_set(x_1036, 1, x_1047);
return x_1036;
}
}
else
{
lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; 
x_1048 = lean_ctor_get(x_1036, 1);
x_1049 = lean_ctor_get(x_1036, 0);
lean_inc(x_1048);
lean_inc(x_1049);
lean_dec(x_1036);
x_1050 = lean_ctor_get(x_1048, 0);
lean_inc(x_1050);
x_1051 = lean_ctor_get(x_1048, 1);
lean_inc(x_1051);
if (lean_is_exclusive(x_1048)) {
 lean_ctor_release(x_1048, 0);
 lean_ctor_release(x_1048, 1);
 x_1052 = x_1048;
} else {
 lean_dec_ref(x_1048);
 x_1052 = lean_box(0);
}
lean_inc(x_1049);
x_1053 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_1051, x_1006, x_1049);
if (lean_is_scalar(x_1052)) {
 x_1054 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1054 = x_1052;
}
lean_ctor_set(x_1054, 0, x_1050);
lean_ctor_set(x_1054, 1, x_1053);
x_1055 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1055, 0, x_1049);
lean_ctor_set(x_1055, 1, x_1054);
return x_1055;
}
}
else
{
lean_object* x_1056; lean_object* x_1057; 
lean_dec(x_1006);
lean_dec(x_1);
x_1056 = lean_ctor_get(x_1035, 0);
lean_inc(x_1056);
lean_dec(x_1035);
x_1057 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1057, 0, x_1056);
lean_ctor_set(x_1057, 1, x_991);
return x_1057;
}
}
}
}
block_1002:
{
lean_object* x_993; lean_object* x_994; uint8_t x_995; 
lean_dec(x_992);
x_993 = lean_unsigned_to_nat(0u);
x_994 = l_Array_ummapAux___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__4___rarg(x_1, x_993, x_3, x_991);
x_995 = !lean_is_exclusive(x_994);
if (x_995 == 0)
{
lean_object* x_996; lean_object* x_997; 
x_996 = lean_ctor_get(x_994, 0);
x_997 = l_Lean_mkAppRev(x_990, x_996);
lean_dec(x_996);
lean_ctor_set(x_994, 0, x_997);
return x_994;
}
else
{
lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; 
x_998 = lean_ctor_get(x_994, 0);
x_999 = lean_ctor_get(x_994, 1);
lean_inc(x_999);
lean_inc(x_998);
lean_dec(x_994);
x_1000 = l_Lean_mkAppRev(x_990, x_998);
lean_dec(x_998);
x_1001 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1001, 0, x_1000);
lean_ctor_set(x_1001, 1, x_999);
return x_1001;
}
}
}
}
}
}
}
lean_object* l___private_Init_Lean_Expr_3__withAppRevAux___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Expr_3__withAppRevAux___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__5___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_16; lean_object* x_17; lean_object* x_27; lean_object* x_28; 
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_50; lean_object* x_51; 
x_38 = lean_ctor_get(x_2, 0);
lean_inc(x_38);
x_50 = lean_ctor_get(x_3, 1);
lean_inc(x_50);
x_51 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_50, x_2);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_3, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_1, 5);
lean_inc(x_53);
lean_inc(x_38);
lean_inc(x_52);
x_54 = lean_apply_2(x_53, x_52, x_38);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_1, 10);
lean_inc(x_55);
lean_inc(x_38);
x_56 = lean_apply_2(x_55, x_52, x_38);
if (lean_obj_tag(x_56) == 0)
{
lean_dec(x_50);
lean_dec(x_38);
lean_dec(x_1);
lean_inc(x_2);
x_4 = x_2;
x_5 = x_3;
goto block_15;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_108; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 2);
lean_inc(x_60);
lean_dec(x_57);
x_108 = lean_expr_has_expr_mvar(x_60);
if (x_108 == 0)
{
uint8_t x_109; 
x_109 = lean_expr_has_level_mvar(x_60);
if (x_109 == 0)
{
lean_dec(x_50);
x_61 = x_60;
x_62 = x_3;
goto block_107;
}
else
{
lean_object* x_110; 
x_110 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_50, x_60);
lean_dec(x_50);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
lean_inc(x_60);
lean_inc(x_1);
x_111 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_60, x_3);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 0);
lean_inc(x_113);
lean_dec(x_111);
x_114 = !lean_is_exclusive(x_112);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
x_116 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_115, x_60, x_113);
lean_ctor_set(x_112, 1, x_116);
x_61 = x_113;
x_62 = x_112;
goto block_107;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_112, 0);
x_118 = lean_ctor_get(x_112, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_112);
lean_inc(x_113);
x_119 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_118, x_60, x_113);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_119);
x_61 = x_113;
x_62 = x_120;
goto block_107;
}
}
else
{
lean_object* x_121; 
lean_dec(x_60);
x_121 = lean_ctor_get(x_110, 0);
lean_inc(x_121);
lean_dec(x_110);
x_61 = x_121;
x_62 = x_3;
goto block_107;
}
}
}
else
{
lean_object* x_122; 
x_122 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_50, x_60);
lean_dec(x_50);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
lean_inc(x_60);
lean_inc(x_1);
x_123 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_60, x_3);
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 0);
lean_inc(x_125);
lean_dec(x_123);
x_126 = !lean_is_exclusive(x_124);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
x_128 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_127, x_60, x_125);
lean_ctor_set(x_124, 1, x_128);
x_61 = x_125;
x_62 = x_124;
goto block_107;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_129 = lean_ctor_get(x_124, 0);
x_130 = lean_ctor_get(x_124, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_124);
lean_inc(x_125);
x_131 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_130, x_60, x_125);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_131);
x_61 = x_125;
x_62 = x_132;
goto block_107;
}
}
else
{
lean_object* x_133; 
lean_dec(x_60);
x_133 = lean_ctor_get(x_122, 0);
lean_inc(x_133);
lean_dec(x_122);
x_61 = x_133;
x_62 = x_3;
goto block_107;
}
}
block_107:
{
uint8_t x_63; 
x_63 = lean_expr_has_expr_mvar(x_61);
if (x_63 == 0)
{
uint8_t x_64; 
x_64 = lean_expr_has_level_mvar(x_61);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_array_get_size(x_59);
x_66 = lean_expr_abstract(x_61, x_59);
lean_inc(x_58);
lean_inc(x_1);
x_67 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__1___rarg(x_1, x_58, x_59, x_65, x_66, x_62);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_ctor_get(x_1, 9);
lean_inc(x_70);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_69, 0);
x_73 = lean_apply_5(x_70, x_72, x_38, x_58, x_59, x_61);
lean_ctor_set(x_69, 0, x_73);
lean_inc(x_2);
x_4 = x_2;
x_5 = x_69;
goto block_15;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_69, 0);
x_75 = lean_ctor_get(x_69, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_69);
x_76 = lean_apply_5(x_70, x_74, x_38, x_58, x_59, x_61);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
lean_inc(x_2);
x_4 = x_2;
x_5 = x_77;
goto block_15;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_58);
x_78 = lean_ctor_get(x_67, 1);
lean_inc(x_78);
lean_dec(x_67);
x_79 = lean_ctor_get(x_68, 0);
lean_inc(x_79);
lean_dec(x_68);
x_80 = lean_ctor_get(x_1, 6);
lean_inc(x_80);
x_81 = lean_ctor_get(x_1, 11);
lean_inc(x_81);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_78);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_78, 0);
lean_inc(x_38);
x_84 = lean_apply_2(x_81, x_83, x_38);
lean_inc(x_79);
x_85 = lean_apply_3(x_80, x_84, x_38, x_79);
lean_ctor_set(x_78, 0, x_85);
x_4 = x_79;
x_5 = x_78;
goto block_15;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_78, 0);
x_87 = lean_ctor_get(x_78, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_78);
lean_inc(x_38);
x_88 = lean_apply_2(x_81, x_86, x_38);
lean_inc(x_79);
x_89 = lean_apply_3(x_80, x_88, x_38, x_79);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_87);
x_4 = x_79;
x_5 = x_90;
goto block_15;
}
}
}
else
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_1, 9);
lean_inc(x_91);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_62);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_62, 0);
x_94 = lean_apply_5(x_91, x_93, x_38, x_58, x_59, x_61);
lean_ctor_set(x_62, 0, x_94);
lean_inc(x_2);
x_4 = x_2;
x_5 = x_62;
goto block_15;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_62, 0);
x_96 = lean_ctor_get(x_62, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_62);
x_97 = lean_apply_5(x_91, x_95, x_38, x_58, x_59, x_61);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
lean_inc(x_2);
x_4 = x_2;
x_5 = x_98;
goto block_15;
}
}
}
else
{
lean_object* x_99; uint8_t x_100; 
x_99 = lean_ctor_get(x_1, 9);
lean_inc(x_99);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_62);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_62, 0);
x_102 = lean_apply_5(x_99, x_101, x_38, x_58, x_59, x_61);
lean_ctor_set(x_62, 0, x_102);
lean_inc(x_2);
x_4 = x_2;
x_5 = x_62;
goto block_15;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_62, 0);
x_104 = lean_ctor_get(x_62, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_62);
x_105 = lean_apply_5(x_99, x_103, x_38, x_58, x_59, x_61);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
lean_inc(x_2);
x_4 = x_2;
x_5 = x_106;
goto block_15;
}
}
}
}
}
else
{
lean_object* x_134; uint8_t x_135; 
lean_dec(x_52);
x_134 = lean_ctor_get(x_54, 0);
lean_inc(x_134);
lean_dec(x_54);
x_135 = lean_expr_has_expr_mvar(x_134);
if (x_135 == 0)
{
uint8_t x_136; 
x_136 = lean_expr_has_level_mvar(x_134);
if (x_136 == 0)
{
lean_dec(x_50);
x_39 = x_134;
x_40 = x_3;
goto block_49;
}
else
{
lean_object* x_137; 
x_137 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_50, x_134);
lean_dec(x_50);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
lean_inc(x_134);
lean_inc(x_1);
x_138 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_134, x_3);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 0);
lean_inc(x_140);
lean_dec(x_138);
x_141 = !lean_is_exclusive(x_139);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
x_143 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_142, x_134, x_140);
lean_ctor_set(x_139, 1, x_143);
x_39 = x_140;
x_40 = x_139;
goto block_49;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_144 = lean_ctor_get(x_139, 0);
x_145 = lean_ctor_get(x_139, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_139);
lean_inc(x_140);
x_146 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_145, x_134, x_140);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_146);
x_39 = x_140;
x_40 = x_147;
goto block_49;
}
}
else
{
lean_object* x_148; 
lean_dec(x_134);
x_148 = lean_ctor_get(x_137, 0);
lean_inc(x_148);
lean_dec(x_137);
x_39 = x_148;
x_40 = x_3;
goto block_49;
}
}
}
else
{
lean_object* x_149; 
x_149 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_50, x_134);
lean_dec(x_50);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
lean_inc(x_134);
lean_inc(x_1);
x_150 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_134, x_3);
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 0);
lean_inc(x_152);
lean_dec(x_150);
x_153 = !lean_is_exclusive(x_151);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
x_155 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_154, x_134, x_152);
lean_ctor_set(x_151, 1, x_155);
x_39 = x_152;
x_40 = x_151;
goto block_49;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_156 = lean_ctor_get(x_151, 0);
x_157 = lean_ctor_get(x_151, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_151);
lean_inc(x_152);
x_158 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_157, x_134, x_152);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_158);
x_39 = x_152;
x_40 = x_159;
goto block_49;
}
}
else
{
lean_object* x_160; 
lean_dec(x_134);
x_160 = lean_ctor_get(x_149, 0);
lean_inc(x_160);
lean_dec(x_149);
x_39 = x_160;
x_40 = x_3;
goto block_49;
}
}
}
}
else
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_50);
lean_dec(x_38);
lean_dec(x_2);
lean_dec(x_1);
x_161 = lean_ctor_get(x_51, 0);
lean_inc(x_161);
lean_dec(x_51);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_3);
return x_162;
}
block_49:
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_1, 6);
lean_inc(x_41);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_39);
x_44 = lean_apply_3(x_41, x_43, x_38, x_39);
lean_ctor_set(x_40, 0, x_44);
x_4 = x_39;
x_5 = x_40;
goto block_15;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_40, 0);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_40);
lean_inc(x_39);
x_47 = lean_apply_3(x_41, x_45, x_38, x_39);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_4 = x_39;
x_5 = x_48;
goto block_15;
}
}
}
case 3:
{
lean_object* x_163; uint8_t x_164; 
x_163 = lean_ctor_get(x_2, 0);
lean_inc(x_163);
x_164 = !lean_is_exclusive(x_3);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_165 = lean_ctor_get(x_3, 0);
x_166 = l_Lean_AbstractMetavarContext_instantiateLevelMVars___main___rarg(x_1, x_163, x_165);
x_167 = !lean_is_exclusive(x_166);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_166, 0);
x_169 = lean_ctor_get(x_166, 1);
lean_ctor_set(x_3, 0, x_169);
x_170 = lean_expr_update_sort(x_2, x_168);
lean_ctor_set(x_166, 1, x_3);
lean_ctor_set(x_166, 0, x_170);
return x_166;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_171 = lean_ctor_get(x_166, 0);
x_172 = lean_ctor_get(x_166, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_166);
lean_ctor_set(x_3, 0, x_172);
x_173 = lean_expr_update_sort(x_2, x_171);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_3);
return x_174;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_175 = lean_ctor_get(x_3, 0);
x_176 = lean_ctor_get(x_3, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_3);
x_177 = l_Lean_AbstractMetavarContext_instantiateLevelMVars___main___rarg(x_1, x_163, x_175);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_180 = x_177;
} else {
 lean_dec_ref(x_177);
 x_180 = lean_box(0);
}
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_176);
x_182 = lean_expr_update_sort(x_2, x_178);
if (lean_is_scalar(x_180)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_180;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_181);
return x_183;
}
}
case 4:
{
lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_184 = lean_ctor_get(x_2, 1);
lean_inc(x_184);
x_185 = l_List_mmap___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__3___rarg(x_1, x_184, x_3);
x_186 = !lean_is_exclusive(x_185);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_ctor_get(x_185, 0);
x_188 = lean_expr_update_const(x_2, x_187);
lean_ctor_set(x_185, 0, x_188);
return x_185;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_189 = lean_ctor_get(x_185, 0);
x_190 = lean_ctor_get(x_185, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_185);
x_191 = lean_expr_update_const(x_2, x_189);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_190);
return x_192;
}
}
case 5:
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_193 = lean_unsigned_to_nat(0u);
x_194 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_193);
x_195 = lean_mk_empty_array_with_capacity(x_194);
lean_dec(x_194);
x_196 = l___private_Init_Lean_Expr_3__withAppRevAux___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__5___rarg(x_1, x_2, x_195, x_3);
return x_196;
}
case 6:
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_242; 
x_197 = lean_ctor_get(x_2, 1);
lean_inc(x_197);
x_198 = lean_ctor_get(x_2, 2);
lean_inc(x_198);
x_242 = lean_expr_has_expr_mvar(x_197);
if (x_242 == 0)
{
uint8_t x_243; 
x_243 = lean_expr_has_level_mvar(x_197);
if (x_243 == 0)
{
x_199 = x_197;
x_200 = x_3;
goto block_241;
}
else
{
lean_object* x_244; lean_object* x_245; 
x_244 = lean_ctor_get(x_3, 1);
lean_inc(x_244);
x_245 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_244, x_197);
lean_dec(x_244);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
lean_inc(x_197);
lean_inc(x_1);
x_246 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_197, x_3);
x_247 = lean_ctor_get(x_246, 1);
lean_inc(x_247);
x_248 = lean_ctor_get(x_246, 0);
lean_inc(x_248);
lean_dec(x_246);
x_249 = !lean_is_exclusive(x_247);
if (x_249 == 0)
{
lean_object* x_250; lean_object* x_251; 
x_250 = lean_ctor_get(x_247, 1);
lean_inc(x_248);
x_251 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_250, x_197, x_248);
lean_ctor_set(x_247, 1, x_251);
x_199 = x_248;
x_200 = x_247;
goto block_241;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_252 = lean_ctor_get(x_247, 0);
x_253 = lean_ctor_get(x_247, 1);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_247);
lean_inc(x_248);
x_254 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_253, x_197, x_248);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_252);
lean_ctor_set(x_255, 1, x_254);
x_199 = x_248;
x_200 = x_255;
goto block_241;
}
}
else
{
lean_object* x_256; 
lean_dec(x_197);
x_256 = lean_ctor_get(x_245, 0);
lean_inc(x_256);
lean_dec(x_245);
x_199 = x_256;
x_200 = x_3;
goto block_241;
}
}
}
else
{
lean_object* x_257; lean_object* x_258; 
x_257 = lean_ctor_get(x_3, 1);
lean_inc(x_257);
x_258 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_257, x_197);
lean_dec(x_257);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; uint8_t x_262; 
lean_inc(x_197);
lean_inc(x_1);
x_259 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_197, x_3);
x_260 = lean_ctor_get(x_259, 1);
lean_inc(x_260);
x_261 = lean_ctor_get(x_259, 0);
lean_inc(x_261);
lean_dec(x_259);
x_262 = !lean_is_exclusive(x_260);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; 
x_263 = lean_ctor_get(x_260, 1);
lean_inc(x_261);
x_264 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_263, x_197, x_261);
lean_ctor_set(x_260, 1, x_264);
x_199 = x_261;
x_200 = x_260;
goto block_241;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_265 = lean_ctor_get(x_260, 0);
x_266 = lean_ctor_get(x_260, 1);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_260);
lean_inc(x_261);
x_267 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_266, x_197, x_261);
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_265);
lean_ctor_set(x_268, 1, x_267);
x_199 = x_261;
x_200 = x_268;
goto block_241;
}
}
else
{
lean_object* x_269; 
lean_dec(x_197);
x_269 = lean_ctor_get(x_258, 0);
lean_inc(x_269);
lean_dec(x_258);
x_199 = x_269;
x_200 = x_3;
goto block_241;
}
}
block_241:
{
lean_object* x_201; lean_object* x_202; uint8_t x_213; 
x_213 = lean_expr_has_expr_mvar(x_198);
if (x_213 == 0)
{
uint8_t x_214; 
x_214 = lean_expr_has_level_mvar(x_198);
if (x_214 == 0)
{
lean_dec(x_1);
x_201 = x_198;
x_202 = x_200;
goto block_212;
}
else
{
lean_object* x_215; lean_object* x_216; 
x_215 = lean_ctor_get(x_200, 1);
lean_inc(x_215);
x_216 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_215, x_198);
lean_dec(x_215);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; 
lean_inc(x_198);
x_217 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_198, x_200);
x_218 = lean_ctor_get(x_217, 1);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 0);
lean_inc(x_219);
lean_dec(x_217);
x_220 = !lean_is_exclusive(x_218);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; 
x_221 = lean_ctor_get(x_218, 1);
lean_inc(x_219);
x_222 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_221, x_198, x_219);
lean_ctor_set(x_218, 1, x_222);
x_201 = x_219;
x_202 = x_218;
goto block_212;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_223 = lean_ctor_get(x_218, 0);
x_224 = lean_ctor_get(x_218, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_218);
lean_inc(x_219);
x_225 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_224, x_198, x_219);
x_226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_226, 0, x_223);
lean_ctor_set(x_226, 1, x_225);
x_201 = x_219;
x_202 = x_226;
goto block_212;
}
}
else
{
lean_object* x_227; 
lean_dec(x_198);
lean_dec(x_1);
x_227 = lean_ctor_get(x_216, 0);
lean_inc(x_227);
lean_dec(x_216);
x_201 = x_227;
x_202 = x_200;
goto block_212;
}
}
}
else
{
lean_object* x_228; lean_object* x_229; 
x_228 = lean_ctor_get(x_200, 1);
lean_inc(x_228);
x_229 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_228, x_198);
lean_dec(x_228);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
lean_inc(x_198);
x_230 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_198, x_200);
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 0);
lean_inc(x_232);
lean_dec(x_230);
x_233 = !lean_is_exclusive(x_231);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; 
x_234 = lean_ctor_get(x_231, 1);
lean_inc(x_232);
x_235 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_234, x_198, x_232);
lean_ctor_set(x_231, 1, x_235);
x_201 = x_232;
x_202 = x_231;
goto block_212;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_236 = lean_ctor_get(x_231, 0);
x_237 = lean_ctor_get(x_231, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_231);
lean_inc(x_232);
x_238 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_237, x_198, x_232);
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_236);
lean_ctor_set(x_239, 1, x_238);
x_201 = x_232;
x_202 = x_239;
goto block_212;
}
}
else
{
lean_object* x_240; 
lean_dec(x_198);
lean_dec(x_1);
x_240 = lean_ctor_get(x_229, 0);
lean_inc(x_240);
lean_dec(x_229);
x_201 = x_240;
x_202 = x_200;
goto block_212;
}
}
block_212:
{
if (lean_obj_tag(x_2) == 6)
{
uint8_t x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_204 = lean_expr_update_lambda(x_2, x_203, x_199, x_201);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_202);
return x_205;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_201);
lean_dec(x_199);
lean_dec(x_2);
x_206 = l_Lean_Expr_constName___closed__1;
x_207 = lean_unsigned_to_nat(471u);
x_208 = lean_unsigned_to_nat(18u);
x_209 = l_Lean_Expr_updateLambda_x21___closed__1;
x_210 = l_panicWithPos___at_Lean_Expr_bindingDomain___spec__1(x_206, x_207, x_208, x_209);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_202);
return x_211;
}
}
}
}
case 7:
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_315; 
x_270 = lean_ctor_get(x_2, 1);
lean_inc(x_270);
x_271 = lean_ctor_get(x_2, 2);
lean_inc(x_271);
x_315 = lean_expr_has_expr_mvar(x_270);
if (x_315 == 0)
{
uint8_t x_316; 
x_316 = lean_expr_has_level_mvar(x_270);
if (x_316 == 0)
{
x_272 = x_270;
x_273 = x_3;
goto block_314;
}
else
{
lean_object* x_317; lean_object* x_318; 
x_317 = lean_ctor_get(x_3, 1);
lean_inc(x_317);
x_318 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_317, x_270);
lean_dec(x_317);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; 
lean_inc(x_270);
lean_inc(x_1);
x_319 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_270, x_3);
x_320 = lean_ctor_get(x_319, 1);
lean_inc(x_320);
x_321 = lean_ctor_get(x_319, 0);
lean_inc(x_321);
lean_dec(x_319);
x_322 = !lean_is_exclusive(x_320);
if (x_322 == 0)
{
lean_object* x_323; lean_object* x_324; 
x_323 = lean_ctor_get(x_320, 1);
lean_inc(x_321);
x_324 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_323, x_270, x_321);
lean_ctor_set(x_320, 1, x_324);
x_272 = x_321;
x_273 = x_320;
goto block_314;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_325 = lean_ctor_get(x_320, 0);
x_326 = lean_ctor_get(x_320, 1);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_320);
lean_inc(x_321);
x_327 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_326, x_270, x_321);
x_328 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_328, 0, x_325);
lean_ctor_set(x_328, 1, x_327);
x_272 = x_321;
x_273 = x_328;
goto block_314;
}
}
else
{
lean_object* x_329; 
lean_dec(x_270);
x_329 = lean_ctor_get(x_318, 0);
lean_inc(x_329);
lean_dec(x_318);
x_272 = x_329;
x_273 = x_3;
goto block_314;
}
}
}
else
{
lean_object* x_330; lean_object* x_331; 
x_330 = lean_ctor_get(x_3, 1);
lean_inc(x_330);
x_331 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_330, x_270);
lean_dec(x_330);
if (lean_obj_tag(x_331) == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; 
lean_inc(x_270);
lean_inc(x_1);
x_332 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_270, x_3);
x_333 = lean_ctor_get(x_332, 1);
lean_inc(x_333);
x_334 = lean_ctor_get(x_332, 0);
lean_inc(x_334);
lean_dec(x_332);
x_335 = !lean_is_exclusive(x_333);
if (x_335 == 0)
{
lean_object* x_336; lean_object* x_337; 
x_336 = lean_ctor_get(x_333, 1);
lean_inc(x_334);
x_337 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_336, x_270, x_334);
lean_ctor_set(x_333, 1, x_337);
x_272 = x_334;
x_273 = x_333;
goto block_314;
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_338 = lean_ctor_get(x_333, 0);
x_339 = lean_ctor_get(x_333, 1);
lean_inc(x_339);
lean_inc(x_338);
lean_dec(x_333);
lean_inc(x_334);
x_340 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_339, x_270, x_334);
x_341 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_341, 0, x_338);
lean_ctor_set(x_341, 1, x_340);
x_272 = x_334;
x_273 = x_341;
goto block_314;
}
}
else
{
lean_object* x_342; 
lean_dec(x_270);
x_342 = lean_ctor_get(x_331, 0);
lean_inc(x_342);
lean_dec(x_331);
x_272 = x_342;
x_273 = x_3;
goto block_314;
}
}
block_314:
{
lean_object* x_274; lean_object* x_275; uint8_t x_286; 
x_286 = lean_expr_has_expr_mvar(x_271);
if (x_286 == 0)
{
uint8_t x_287; 
x_287 = lean_expr_has_level_mvar(x_271);
if (x_287 == 0)
{
lean_dec(x_1);
x_274 = x_271;
x_275 = x_273;
goto block_285;
}
else
{
lean_object* x_288; lean_object* x_289; 
x_288 = lean_ctor_get(x_273, 1);
lean_inc(x_288);
x_289 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_288, x_271);
lean_dec(x_288);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; 
lean_inc(x_271);
x_290 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_271, x_273);
x_291 = lean_ctor_get(x_290, 1);
lean_inc(x_291);
x_292 = lean_ctor_get(x_290, 0);
lean_inc(x_292);
lean_dec(x_290);
x_293 = !lean_is_exclusive(x_291);
if (x_293 == 0)
{
lean_object* x_294; lean_object* x_295; 
x_294 = lean_ctor_get(x_291, 1);
lean_inc(x_292);
x_295 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_294, x_271, x_292);
lean_ctor_set(x_291, 1, x_295);
x_274 = x_292;
x_275 = x_291;
goto block_285;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_296 = lean_ctor_get(x_291, 0);
x_297 = lean_ctor_get(x_291, 1);
lean_inc(x_297);
lean_inc(x_296);
lean_dec(x_291);
lean_inc(x_292);
x_298 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_297, x_271, x_292);
x_299 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_299, 0, x_296);
lean_ctor_set(x_299, 1, x_298);
x_274 = x_292;
x_275 = x_299;
goto block_285;
}
}
else
{
lean_object* x_300; 
lean_dec(x_271);
lean_dec(x_1);
x_300 = lean_ctor_get(x_289, 0);
lean_inc(x_300);
lean_dec(x_289);
x_274 = x_300;
x_275 = x_273;
goto block_285;
}
}
}
else
{
lean_object* x_301; lean_object* x_302; 
x_301 = lean_ctor_get(x_273, 1);
lean_inc(x_301);
x_302 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_301, x_271);
lean_dec(x_301);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; 
lean_inc(x_271);
x_303 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_271, x_273);
x_304 = lean_ctor_get(x_303, 1);
lean_inc(x_304);
x_305 = lean_ctor_get(x_303, 0);
lean_inc(x_305);
lean_dec(x_303);
x_306 = !lean_is_exclusive(x_304);
if (x_306 == 0)
{
lean_object* x_307; lean_object* x_308; 
x_307 = lean_ctor_get(x_304, 1);
lean_inc(x_305);
x_308 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_307, x_271, x_305);
lean_ctor_set(x_304, 1, x_308);
x_274 = x_305;
x_275 = x_304;
goto block_285;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_309 = lean_ctor_get(x_304, 0);
x_310 = lean_ctor_get(x_304, 1);
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_304);
lean_inc(x_305);
x_311 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_310, x_271, x_305);
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_309);
lean_ctor_set(x_312, 1, x_311);
x_274 = x_305;
x_275 = x_312;
goto block_285;
}
}
else
{
lean_object* x_313; 
lean_dec(x_271);
lean_dec(x_1);
x_313 = lean_ctor_get(x_302, 0);
lean_inc(x_313);
lean_dec(x_302);
x_274 = x_313;
x_275 = x_273;
goto block_285;
}
}
block_285:
{
if (lean_obj_tag(x_2) == 7)
{
uint8_t x_276; lean_object* x_277; lean_object* x_278; 
x_276 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_277 = lean_expr_update_forall(x_2, x_276, x_272, x_274);
x_278 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_275);
return x_278;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec(x_274);
lean_dec(x_272);
lean_dec(x_2);
x_279 = l_Lean_Expr_constName___closed__1;
x_280 = lean_unsigned_to_nat(457u);
x_281 = lean_unsigned_to_nat(22u);
x_282 = l_Lean_Expr_updateForall_x21___closed__1;
x_283 = l_panicWithPos___at_Lean_Expr_bindingDomain___spec__1(x_279, x_280, x_281, x_282);
x_284 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_275);
return x_284;
}
}
}
}
case 8:
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_419; 
x_343 = lean_ctor_get(x_2, 1);
lean_inc(x_343);
x_344 = lean_ctor_get(x_2, 2);
lean_inc(x_344);
x_345 = lean_ctor_get(x_2, 3);
lean_inc(x_345);
x_419 = lean_expr_has_expr_mvar(x_343);
if (x_419 == 0)
{
uint8_t x_420; 
x_420 = lean_expr_has_level_mvar(x_343);
if (x_420 == 0)
{
x_346 = x_343;
x_347 = x_3;
goto block_418;
}
else
{
lean_object* x_421; lean_object* x_422; 
x_421 = lean_ctor_get(x_3, 1);
lean_inc(x_421);
x_422 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_421, x_343);
lean_dec(x_421);
if (lean_obj_tag(x_422) == 0)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; uint8_t x_426; 
lean_inc(x_343);
lean_inc(x_1);
x_423 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_343, x_3);
x_424 = lean_ctor_get(x_423, 1);
lean_inc(x_424);
x_425 = lean_ctor_get(x_423, 0);
lean_inc(x_425);
lean_dec(x_423);
x_426 = !lean_is_exclusive(x_424);
if (x_426 == 0)
{
lean_object* x_427; lean_object* x_428; 
x_427 = lean_ctor_get(x_424, 1);
lean_inc(x_425);
x_428 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_427, x_343, x_425);
lean_ctor_set(x_424, 1, x_428);
x_346 = x_425;
x_347 = x_424;
goto block_418;
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_429 = lean_ctor_get(x_424, 0);
x_430 = lean_ctor_get(x_424, 1);
lean_inc(x_430);
lean_inc(x_429);
lean_dec(x_424);
lean_inc(x_425);
x_431 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_430, x_343, x_425);
x_432 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_432, 0, x_429);
lean_ctor_set(x_432, 1, x_431);
x_346 = x_425;
x_347 = x_432;
goto block_418;
}
}
else
{
lean_object* x_433; 
lean_dec(x_343);
x_433 = lean_ctor_get(x_422, 0);
lean_inc(x_433);
lean_dec(x_422);
x_346 = x_433;
x_347 = x_3;
goto block_418;
}
}
}
else
{
lean_object* x_434; lean_object* x_435; 
x_434 = lean_ctor_get(x_3, 1);
lean_inc(x_434);
x_435 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_434, x_343);
lean_dec(x_434);
if (lean_obj_tag(x_435) == 0)
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; uint8_t x_439; 
lean_inc(x_343);
lean_inc(x_1);
x_436 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_343, x_3);
x_437 = lean_ctor_get(x_436, 1);
lean_inc(x_437);
x_438 = lean_ctor_get(x_436, 0);
lean_inc(x_438);
lean_dec(x_436);
x_439 = !lean_is_exclusive(x_437);
if (x_439 == 0)
{
lean_object* x_440; lean_object* x_441; 
x_440 = lean_ctor_get(x_437, 1);
lean_inc(x_438);
x_441 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_440, x_343, x_438);
lean_ctor_set(x_437, 1, x_441);
x_346 = x_438;
x_347 = x_437;
goto block_418;
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_442 = lean_ctor_get(x_437, 0);
x_443 = lean_ctor_get(x_437, 1);
lean_inc(x_443);
lean_inc(x_442);
lean_dec(x_437);
lean_inc(x_438);
x_444 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_443, x_343, x_438);
x_445 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_445, 0, x_442);
lean_ctor_set(x_445, 1, x_444);
x_346 = x_438;
x_347 = x_445;
goto block_418;
}
}
else
{
lean_object* x_446; 
lean_dec(x_343);
x_446 = lean_ctor_get(x_435, 0);
lean_inc(x_446);
lean_dec(x_435);
x_346 = x_446;
x_347 = x_3;
goto block_418;
}
}
block_418:
{
lean_object* x_348; lean_object* x_349; uint8_t x_390; 
x_390 = lean_expr_has_expr_mvar(x_344);
if (x_390 == 0)
{
uint8_t x_391; 
x_391 = lean_expr_has_level_mvar(x_344);
if (x_391 == 0)
{
x_348 = x_344;
x_349 = x_347;
goto block_389;
}
else
{
lean_object* x_392; lean_object* x_393; 
x_392 = lean_ctor_get(x_347, 1);
lean_inc(x_392);
x_393 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_392, x_344);
lean_dec(x_392);
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; 
lean_inc(x_344);
lean_inc(x_1);
x_394 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_344, x_347);
x_395 = lean_ctor_get(x_394, 1);
lean_inc(x_395);
x_396 = lean_ctor_get(x_394, 0);
lean_inc(x_396);
lean_dec(x_394);
x_397 = !lean_is_exclusive(x_395);
if (x_397 == 0)
{
lean_object* x_398; lean_object* x_399; 
x_398 = lean_ctor_get(x_395, 1);
lean_inc(x_396);
x_399 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_398, x_344, x_396);
lean_ctor_set(x_395, 1, x_399);
x_348 = x_396;
x_349 = x_395;
goto block_389;
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_400 = lean_ctor_get(x_395, 0);
x_401 = lean_ctor_get(x_395, 1);
lean_inc(x_401);
lean_inc(x_400);
lean_dec(x_395);
lean_inc(x_396);
x_402 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_401, x_344, x_396);
x_403 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_403, 0, x_400);
lean_ctor_set(x_403, 1, x_402);
x_348 = x_396;
x_349 = x_403;
goto block_389;
}
}
else
{
lean_object* x_404; 
lean_dec(x_344);
x_404 = lean_ctor_get(x_393, 0);
lean_inc(x_404);
lean_dec(x_393);
x_348 = x_404;
x_349 = x_347;
goto block_389;
}
}
}
else
{
lean_object* x_405; lean_object* x_406; 
x_405 = lean_ctor_get(x_347, 1);
lean_inc(x_405);
x_406 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_405, x_344);
lean_dec(x_405);
if (lean_obj_tag(x_406) == 0)
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; uint8_t x_410; 
lean_inc(x_344);
lean_inc(x_1);
x_407 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_344, x_347);
x_408 = lean_ctor_get(x_407, 1);
lean_inc(x_408);
x_409 = lean_ctor_get(x_407, 0);
lean_inc(x_409);
lean_dec(x_407);
x_410 = !lean_is_exclusive(x_408);
if (x_410 == 0)
{
lean_object* x_411; lean_object* x_412; 
x_411 = lean_ctor_get(x_408, 1);
lean_inc(x_409);
x_412 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_411, x_344, x_409);
lean_ctor_set(x_408, 1, x_412);
x_348 = x_409;
x_349 = x_408;
goto block_389;
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_413 = lean_ctor_get(x_408, 0);
x_414 = lean_ctor_get(x_408, 1);
lean_inc(x_414);
lean_inc(x_413);
lean_dec(x_408);
lean_inc(x_409);
x_415 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_414, x_344, x_409);
x_416 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_416, 0, x_413);
lean_ctor_set(x_416, 1, x_415);
x_348 = x_409;
x_349 = x_416;
goto block_389;
}
}
else
{
lean_object* x_417; 
lean_dec(x_344);
x_417 = lean_ctor_get(x_406, 0);
lean_inc(x_417);
lean_dec(x_406);
x_348 = x_417;
x_349 = x_347;
goto block_389;
}
}
block_389:
{
lean_object* x_350; lean_object* x_351; uint8_t x_361; 
x_361 = lean_expr_has_expr_mvar(x_345);
if (x_361 == 0)
{
uint8_t x_362; 
x_362 = lean_expr_has_level_mvar(x_345);
if (x_362 == 0)
{
lean_dec(x_1);
x_350 = x_345;
x_351 = x_349;
goto block_360;
}
else
{
lean_object* x_363; lean_object* x_364; 
x_363 = lean_ctor_get(x_349, 1);
lean_inc(x_363);
x_364 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_363, x_345);
lean_dec(x_363);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; 
lean_inc(x_345);
x_365 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_345, x_349);
x_366 = lean_ctor_get(x_365, 1);
lean_inc(x_366);
x_367 = lean_ctor_get(x_365, 0);
lean_inc(x_367);
lean_dec(x_365);
x_368 = !lean_is_exclusive(x_366);
if (x_368 == 0)
{
lean_object* x_369; lean_object* x_370; 
x_369 = lean_ctor_get(x_366, 1);
lean_inc(x_367);
x_370 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_369, x_345, x_367);
lean_ctor_set(x_366, 1, x_370);
x_350 = x_367;
x_351 = x_366;
goto block_360;
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_371 = lean_ctor_get(x_366, 0);
x_372 = lean_ctor_get(x_366, 1);
lean_inc(x_372);
lean_inc(x_371);
lean_dec(x_366);
lean_inc(x_367);
x_373 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_372, x_345, x_367);
x_374 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_374, 0, x_371);
lean_ctor_set(x_374, 1, x_373);
x_350 = x_367;
x_351 = x_374;
goto block_360;
}
}
else
{
lean_object* x_375; 
lean_dec(x_345);
lean_dec(x_1);
x_375 = lean_ctor_get(x_364, 0);
lean_inc(x_375);
lean_dec(x_364);
x_350 = x_375;
x_351 = x_349;
goto block_360;
}
}
}
else
{
lean_object* x_376; lean_object* x_377; 
x_376 = lean_ctor_get(x_349, 1);
lean_inc(x_376);
x_377 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_376, x_345);
lean_dec(x_376);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; uint8_t x_381; 
lean_inc(x_345);
x_378 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_345, x_349);
x_379 = lean_ctor_get(x_378, 1);
lean_inc(x_379);
x_380 = lean_ctor_get(x_378, 0);
lean_inc(x_380);
lean_dec(x_378);
x_381 = !lean_is_exclusive(x_379);
if (x_381 == 0)
{
lean_object* x_382; lean_object* x_383; 
x_382 = lean_ctor_get(x_379, 1);
lean_inc(x_380);
x_383 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_382, x_345, x_380);
lean_ctor_set(x_379, 1, x_383);
x_350 = x_380;
x_351 = x_379;
goto block_360;
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_384 = lean_ctor_get(x_379, 0);
x_385 = lean_ctor_get(x_379, 1);
lean_inc(x_385);
lean_inc(x_384);
lean_dec(x_379);
lean_inc(x_380);
x_386 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_385, x_345, x_380);
x_387 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_387, 0, x_384);
lean_ctor_set(x_387, 1, x_386);
x_350 = x_380;
x_351 = x_387;
goto block_360;
}
}
else
{
lean_object* x_388; 
lean_dec(x_345);
lean_dec(x_1);
x_388 = lean_ctor_get(x_377, 0);
lean_inc(x_388);
lean_dec(x_377);
x_350 = x_388;
x_351 = x_349;
goto block_360;
}
}
block_360:
{
if (lean_obj_tag(x_2) == 8)
{
lean_object* x_352; lean_object* x_353; 
x_352 = lean_expr_update_let(x_2, x_346, x_348, x_350);
x_353 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_351);
return x_353;
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
lean_dec(x_350);
lean_dec(x_348);
lean_dec(x_346);
lean_dec(x_2);
x_354 = l_Lean_Expr_constName___closed__1;
x_355 = lean_unsigned_to_nat(480u);
x_356 = lean_unsigned_to_nat(18u);
x_357 = l_Lean_Expr_letName___closed__1;
x_358 = l_panicWithPos___at_Lean_Expr_bindingDomain___spec__1(x_354, x_355, x_356, x_357);
x_359 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_359, 0, x_358);
lean_ctor_set(x_359, 1, x_351);
return x_359;
}
}
}
}
}
case 10:
{
lean_object* x_447; uint8_t x_448; 
x_447 = lean_ctor_get(x_2, 1);
lean_inc(x_447);
x_448 = lean_expr_has_expr_mvar(x_447);
if (x_448 == 0)
{
uint8_t x_449; 
x_449 = lean_expr_has_level_mvar(x_447);
if (x_449 == 0)
{
lean_dec(x_1);
x_16 = x_447;
x_17 = x_3;
goto block_26;
}
else
{
lean_object* x_450; lean_object* x_451; 
x_450 = lean_ctor_get(x_3, 1);
lean_inc(x_450);
x_451 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_450, x_447);
lean_dec(x_450);
if (lean_obj_tag(x_451) == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; uint8_t x_455; 
lean_inc(x_447);
x_452 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_447, x_3);
x_453 = lean_ctor_get(x_452, 1);
lean_inc(x_453);
x_454 = lean_ctor_get(x_452, 0);
lean_inc(x_454);
lean_dec(x_452);
x_455 = !lean_is_exclusive(x_453);
if (x_455 == 0)
{
lean_object* x_456; lean_object* x_457; 
x_456 = lean_ctor_get(x_453, 1);
lean_inc(x_454);
x_457 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_456, x_447, x_454);
lean_ctor_set(x_453, 1, x_457);
x_16 = x_454;
x_17 = x_453;
goto block_26;
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_458 = lean_ctor_get(x_453, 0);
x_459 = lean_ctor_get(x_453, 1);
lean_inc(x_459);
lean_inc(x_458);
lean_dec(x_453);
lean_inc(x_454);
x_460 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_459, x_447, x_454);
x_461 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_461, 0, x_458);
lean_ctor_set(x_461, 1, x_460);
x_16 = x_454;
x_17 = x_461;
goto block_26;
}
}
else
{
lean_object* x_462; 
lean_dec(x_447);
lean_dec(x_1);
x_462 = lean_ctor_get(x_451, 0);
lean_inc(x_462);
lean_dec(x_451);
x_16 = x_462;
x_17 = x_3;
goto block_26;
}
}
}
else
{
lean_object* x_463; lean_object* x_464; 
x_463 = lean_ctor_get(x_3, 1);
lean_inc(x_463);
x_464 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_463, x_447);
lean_dec(x_463);
if (lean_obj_tag(x_464) == 0)
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; uint8_t x_468; 
lean_inc(x_447);
x_465 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_447, x_3);
x_466 = lean_ctor_get(x_465, 1);
lean_inc(x_466);
x_467 = lean_ctor_get(x_465, 0);
lean_inc(x_467);
lean_dec(x_465);
x_468 = !lean_is_exclusive(x_466);
if (x_468 == 0)
{
lean_object* x_469; lean_object* x_470; 
x_469 = lean_ctor_get(x_466, 1);
lean_inc(x_467);
x_470 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_469, x_447, x_467);
lean_ctor_set(x_466, 1, x_470);
x_16 = x_467;
x_17 = x_466;
goto block_26;
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_471 = lean_ctor_get(x_466, 0);
x_472 = lean_ctor_get(x_466, 1);
lean_inc(x_472);
lean_inc(x_471);
lean_dec(x_466);
lean_inc(x_467);
x_473 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_472, x_447, x_467);
x_474 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_474, 0, x_471);
lean_ctor_set(x_474, 1, x_473);
x_16 = x_467;
x_17 = x_474;
goto block_26;
}
}
else
{
lean_object* x_475; 
lean_dec(x_447);
lean_dec(x_1);
x_475 = lean_ctor_get(x_464, 0);
lean_inc(x_475);
lean_dec(x_464);
x_16 = x_475;
x_17 = x_3;
goto block_26;
}
}
}
case 11:
{
lean_object* x_476; uint8_t x_477; 
x_476 = lean_ctor_get(x_2, 2);
lean_inc(x_476);
x_477 = lean_expr_has_expr_mvar(x_476);
if (x_477 == 0)
{
uint8_t x_478; 
x_478 = lean_expr_has_level_mvar(x_476);
if (x_478 == 0)
{
lean_dec(x_1);
x_27 = x_476;
x_28 = x_3;
goto block_37;
}
else
{
lean_object* x_479; lean_object* x_480; 
x_479 = lean_ctor_get(x_3, 1);
lean_inc(x_479);
x_480 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_479, x_476);
lean_dec(x_479);
if (lean_obj_tag(x_480) == 0)
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; uint8_t x_484; 
lean_inc(x_476);
x_481 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_476, x_3);
x_482 = lean_ctor_get(x_481, 1);
lean_inc(x_482);
x_483 = lean_ctor_get(x_481, 0);
lean_inc(x_483);
lean_dec(x_481);
x_484 = !lean_is_exclusive(x_482);
if (x_484 == 0)
{
lean_object* x_485; lean_object* x_486; 
x_485 = lean_ctor_get(x_482, 1);
lean_inc(x_483);
x_486 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_485, x_476, x_483);
lean_ctor_set(x_482, 1, x_486);
x_27 = x_483;
x_28 = x_482;
goto block_37;
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_487 = lean_ctor_get(x_482, 0);
x_488 = lean_ctor_get(x_482, 1);
lean_inc(x_488);
lean_inc(x_487);
lean_dec(x_482);
lean_inc(x_483);
x_489 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_488, x_476, x_483);
x_490 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_490, 0, x_487);
lean_ctor_set(x_490, 1, x_489);
x_27 = x_483;
x_28 = x_490;
goto block_37;
}
}
else
{
lean_object* x_491; 
lean_dec(x_476);
lean_dec(x_1);
x_491 = lean_ctor_get(x_480, 0);
lean_inc(x_491);
lean_dec(x_480);
x_27 = x_491;
x_28 = x_3;
goto block_37;
}
}
}
else
{
lean_object* x_492; lean_object* x_493; 
x_492 = lean_ctor_get(x_3, 1);
lean_inc(x_492);
x_493 = l_HashMapImp_find___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__1(x_492, x_476);
lean_dec(x_492);
if (lean_obj_tag(x_493) == 0)
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; uint8_t x_497; 
lean_inc(x_476);
x_494 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_476, x_3);
x_495 = lean_ctor_get(x_494, 1);
lean_inc(x_495);
x_496 = lean_ctor_get(x_494, 0);
lean_inc(x_496);
lean_dec(x_494);
x_497 = !lean_is_exclusive(x_495);
if (x_497 == 0)
{
lean_object* x_498; lean_object* x_499; 
x_498 = lean_ctor_get(x_495, 1);
lean_inc(x_496);
x_499 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_498, x_476, x_496);
lean_ctor_set(x_495, 1, x_499);
x_27 = x_496;
x_28 = x_495;
goto block_37;
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; 
x_500 = lean_ctor_get(x_495, 0);
x_501 = lean_ctor_get(x_495, 1);
lean_inc(x_501);
lean_inc(x_500);
lean_dec(x_495);
lean_inc(x_496);
x_502 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_501, x_476, x_496);
x_503 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_503, 0, x_500);
lean_ctor_set(x_503, 1, x_502);
x_27 = x_496;
x_28 = x_503;
goto block_37;
}
}
else
{
lean_object* x_504; 
lean_dec(x_476);
lean_dec(x_1);
x_504 = lean_ctor_get(x_493, 0);
lean_inc(x_504);
lean_dec(x_493);
x_27 = x_504;
x_28 = x_3;
goto block_37;
}
}
}
default: 
{
lean_object* x_505; 
lean_dec(x_1);
x_505 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_505, 0, x_2);
lean_ctor_set(x_505, 1, x_3);
return x_505;
}
}
block_15:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_4);
x_8 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_7, x_2, x_4);
lean_ctor_set(x_5, 1, x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
lean_inc(x_4);
x_12 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_InstantiateExprMVars_checkCache___spec__3(x_11, x_2, x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
block_26:
{
if (lean_obj_tag(x_2) == 10)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_expr_update_mdata(x_2, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_16);
lean_dec(x_2);
x_20 = l_Lean_Expr_constName___closed__1;
x_21 = lean_unsigned_to_nat(438u);
x_22 = lean_unsigned_to_nat(15u);
x_23 = l_Lean_Expr_updateMData_x21___closed__1;
x_24 = l_panicWithPos___at_Lean_Expr_bindingDomain___spec__1(x_20, x_21, x_22, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_17);
return x_25;
}
}
block_37:
{
if (lean_obj_tag(x_2) == 11)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_expr_update_proj(x_2, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_27);
lean_dec(x_2);
x_31 = l_Lean_Expr_constName___closed__1;
x_32 = lean_unsigned_to_nat(443u);
x_33 = lean_unsigned_to_nat(16u);
x_34 = l_Lean_Expr_updateProj_x21___closed__1;
x_35 = l_panicWithPos___at_Lean_Expr_bindingDomain___spec__1(x_31, x_32, x_33, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_28);
return x_36;
}
}
}
}
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg), 3, 0);
return x_2;
}
}
lean_object* l_panicWithPos___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_panicWithPos___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__2___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___at_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_AbstractMetavarContext_InstantiateExprMVars_main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___rarg), 3, 0);
return x_2;
}
}
lean_object* l_mkHashMap___at_Lean_AbstractMetavarContext_instantiateMVars___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_AbstractMetavarContext_instantiateMVars___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_Lean_AbstractMetavarContext_instantiateMVars___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_expr_has_expr_mvar(x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = lean_expr_has_level_mvar(x_2);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = l_Lean_AbstractMetavarContext_instantiateMVars___rarg___closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_2, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
lean_ctor_set(x_9, 1, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = l_Lean_AbstractMetavarContext_instantiateMVars___rarg___closed__1;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_main___main___rarg(x_1, x_2, x_18);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 1);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
lean_ctor_set(x_19, 1, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l_Lean_AbstractMetavarContext_instantiateMVars(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_AbstractMetavarContext_instantiateMVars___rarg), 3, 0);
return x_2;
}
}
uint8_t l_AssocList_contains___main___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_expr_eqv(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
uint8_t l_HashMapImp_contains___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_expr_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_contains___main___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_AssocList_mfoldl___main___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = lean_expr_hash(x_4);
x_8 = lean_usize_modn(x_7, x_6);
lean_dec(x_6);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = lean_expr_hash(x_12);
x_17 = lean_usize_modn(x_16, x_15);
lean_dec(x_15);
x_18 = lean_array_uget(x_1, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_uset(x_1, x_17, x_19);
x_1 = x_20;
x_2 = x_14;
goto _start;
}
}
}
}
lean_object* l_HashMapImp_moveEntries___main___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_AssocList_mfoldl___main___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__6(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
lean_object* l_HashMapImp_expand___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_HashMapImp_moveEntries___main___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__5(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_AssocList_replace___main___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__7(x_1, x_2, x_7);
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
x_14 = l_AssocList_replace___main___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__7(x_1, x_2, x_12);
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
lean_object* l_HashMapImp_insert___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_expr_hash(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_AssocList_contains___main___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__2(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_6, x_9, x_14);
x_16 = lean_nat_dec_le(x_13, x_7);
lean_dec(x_7);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_1);
x_17 = l_HashMapImp_expand___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__4(x_13, x_15);
return x_17;
}
else
{
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_18 = l_AssocList_replace___main___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__7(x_2, x_3, x_10);
x_19 = lean_array_uset(x_6, x_9, x_18);
lean_ctor_set(x_1, 1, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_22 = lean_array_get_size(x_21);
x_23 = lean_expr_hash(x_2);
x_24 = lean_usize_modn(x_23, x_22);
x_25 = lean_array_uget(x_21, x_24);
x_26 = l_AssocList_contains___main___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__2(x_2, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_20, x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 2, x_25);
x_30 = lean_array_uset(x_21, x_24, x_29);
x_31 = lean_nat_dec_le(x_28, x_22);
lean_dec(x_22);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_HashMapImp_expand___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__4(x_28, x_30);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_22);
x_34 = l_AssocList_replace___main___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__7(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_Lean_AbstractMetavarContext_DependsOn_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_13; 
x_13 = lean_expr_has_expr_mvar(x_2);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = lean_expr_has_level_mvar(x_2);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = lean_expr_has_fvar(x_2);
if (x_15 == 0)
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_16 = 0;
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = lean_box(0);
x_4 = x_19;
goto block_12;
}
}
else
{
lean_object* x_20; 
x_20 = lean_box(0);
x_4 = x_20;
goto block_12;
}
}
else
{
lean_object* x_21; 
x_21 = lean_box(0);
x_4 = x_21;
goto block_12;
}
block_12:
{
uint8_t x_5; 
lean_dec(x_4);
x_5 = l_HashMapImp_contains___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__1(x_3, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_box(0);
lean_inc(x_2);
x_7 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__3(x_3, x_2, x_6);
x_8 = lean_apply_2(x_1, x_2, x_7);
return x_8;
}
else
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
}
}
lean_object* l_AssocList_contains___main___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_HashMapImp_contains___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_HashMapImp_contains___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_panicWithPos___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__1___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_panicWithPos___at_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___spec__1___rarg___closed__1;
x_2 = l_Bool_Inhabited;
x_3 = lean_box(x_2);
x_4 = l_monadInhabited___rarg(x_1, x_3);
return x_4;
}
}
lean_object* l_panicWithPos___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = l_panicWithPos___rarg___closed__1;
x_7 = lean_string_append(x_6, x_1);
x_8 = l_panicWithPos___rarg___closed__2;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_Nat_repr(x_2);
x_11 = lean_string_append(x_9, x_10);
lean_dec(x_10);
x_12 = l_panicWithPos___rarg___closed__2;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_Nat_repr(x_3);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = l_panicWithPos___rarg___closed__3;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_string_append(x_17, x_4);
x_19 = l_panicWithPos___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__1___closed__1;
x_20 = lean_panic_fn(x_18);
x_21 = lean_apply_1(x_20, x_5);
return x_21;
}
}
uint8_t l_Array_anyMAux___main___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_2, x_3);
lean_inc(x_1);
x_8 = l_PersistentArray_anyMAux___main___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__3(x_1, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
}
}
uint8_t l_Array_anyMAux___main___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_array_fget(x_2, x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_3, x_8);
lean_dec(x_3);
x_3 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lean_LocalDecl_name(x_11);
lean_dec(x_11);
lean_inc(x_1);
x_13 = lean_apply_1(x_1, x_12);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_3, x_15);
lean_dec(x_3);
x_3 = x_16;
goto _start;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
}
}
}
uint8_t l_PersistentArray_anyMAux___main___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_anyMAux___main___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__4(x_1, x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyMAux___main___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__5(x_1, x_6, x_7);
return x_8;
}
}
}
uint8_t l_Array_anyMAux___main___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_array_fget(x_2, x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_3, x_8);
lean_dec(x_3);
x_3 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lean_LocalDecl_name(x_11);
lean_dec(x_11);
lean_inc(x_1);
x_13 = lean_apply_1(x_1, x_12);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_3, x_15);
lean_dec(x_3);
x_3 = x_16;
goto _start;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
}
}
}
uint8_t l_PersistentArray_anyM___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_1);
x_4 = l_PersistentArray_anyMAux___main___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__3(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_anyMAux___main___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__6(x_1, x_5, x_6);
return x_7;
}
else
{
lean_dec(x_1);
return x_4;
}
}
}
lean_object* _init_l_Lean_AbstractMetavarContext_DependsOn_dep___main___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown metavariable");
return x_1;
}
}
lean_object* l_Lean_AbstractMetavarContext_DependsOn_dep___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 1:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_1(x_3, x_6);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_ctor_get(x_1, 5);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_2);
x_13 = lean_apply_2(x_12, x_2, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_1, 7);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_apply_2(x_14, x_2, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
x_16 = l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___rarg___closed__1;
x_17 = lean_unsigned_to_nat(304u);
x_18 = lean_unsigned_to_nat(19u);
x_19 = l_Lean_AbstractMetavarContext_DependsOn_dep___main___rarg___closed__1;
x_20 = l_panicWithPos___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__1(x_16, x_17, x_18, x_19, x_5);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_15, 0);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_PersistentArray_anyM___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__2(x_3, x_22);
lean_dec(x_22);
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_5);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_36; 
lean_dec(x_11);
x_26 = lean_ctor_get(x_13, 0);
lean_inc(x_26);
lean_dec(x_13);
x_36 = lean_expr_has_expr_mvar(x_26);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = lean_expr_has_level_mvar(x_26);
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = lean_expr_has_fvar(x_26);
if (x_38 == 0)
{
uint8_t x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_26);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = 0;
x_40 = lean_box(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_5);
return x_41;
}
else
{
lean_object* x_42; 
x_42 = lean_box(0);
x_27 = x_42;
goto block_35;
}
}
else
{
lean_object* x_43; 
x_43 = lean_box(0);
x_27 = x_43;
goto block_35;
}
}
else
{
lean_object* x_44; 
x_44 = lean_box(0);
x_27 = x_44;
goto block_35;
}
block_35:
{
uint8_t x_28; 
lean_dec(x_27);
x_28 = l_HashMapImp_contains___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__1(x_5, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_box(0);
lean_inc(x_26);
x_30 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__3(x_5, x_26, x_29);
x_4 = x_26;
x_5 = x_30;
goto _start;
}
else
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_26);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = 0;
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_5);
return x_34;
}
}
}
}
case 5:
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_72; uint8_t x_82; 
x_45 = lean_ctor_get(x_4, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_4, 1);
lean_inc(x_46);
lean_dec(x_4);
x_82 = lean_expr_has_expr_mvar(x_46);
if (x_82 == 0)
{
uint8_t x_83; 
x_83 = lean_expr_has_level_mvar(x_46);
if (x_83 == 0)
{
uint8_t x_84; 
x_84 = lean_expr_has_fvar(x_46);
if (x_84 == 0)
{
uint8_t x_85; 
lean_dec(x_46);
x_85 = 0;
x_47 = x_85;
x_48 = x_5;
goto block_71;
}
else
{
lean_object* x_86; 
x_86 = lean_box(0);
x_72 = x_86;
goto block_81;
}
}
else
{
lean_object* x_87; 
x_87 = lean_box(0);
x_72 = x_87;
goto block_81;
}
}
else
{
lean_object* x_88; 
x_88 = lean_box(0);
x_72 = x_88;
goto block_81;
}
block_71:
{
if (x_47 == 0)
{
uint8_t x_49; 
x_49 = l_Lean_Expr_isApp(x_45);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_59; 
x_59 = lean_expr_has_expr_mvar(x_45);
if (x_59 == 0)
{
uint8_t x_60; 
x_60 = lean_expr_has_level_mvar(x_45);
if (x_60 == 0)
{
uint8_t x_61; 
x_61 = lean_expr_has_fvar(x_45);
if (x_61 == 0)
{
uint8_t x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_45);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_62 = 0;
x_63 = lean_box(x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_48);
return x_64;
}
else
{
lean_object* x_65; 
x_65 = lean_box(0);
x_50 = x_65;
goto block_58;
}
}
else
{
lean_object* x_66; 
x_66 = lean_box(0);
x_50 = x_66;
goto block_58;
}
}
else
{
lean_object* x_67; 
x_67 = lean_box(0);
x_50 = x_67;
goto block_58;
}
block_58:
{
uint8_t x_51; 
lean_dec(x_50);
x_51 = l_HashMapImp_contains___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__1(x_48, x_45);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_box(0);
lean_inc(x_45);
x_53 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__3(x_48, x_45, x_52);
x_4 = x_45;
x_5 = x_53;
goto _start;
}
else
{
uint8_t x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_45);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = 0;
x_56 = lean_box(x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_48);
return x_57;
}
}
}
else
{
x_4 = x_45;
x_5 = x_48;
goto _start;
}
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_45);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = lean_box(x_47);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_48);
return x_70;
}
}
block_81:
{
uint8_t x_73; 
lean_dec(x_72);
x_73 = l_HashMapImp_contains___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__1(x_5, x_46);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_74 = lean_box(0);
lean_inc(x_46);
x_75 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__3(x_5, x_46, x_74);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_76 = l_Lean_AbstractMetavarContext_DependsOn_dep___main___rarg(x_1, x_2, x_3, x_46, x_75);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_unbox(x_77);
lean_dec(x_77);
x_47 = x_79;
x_48 = x_78;
goto block_71;
}
else
{
uint8_t x_80; 
lean_dec(x_46);
x_80 = 0;
x_47 = x_80;
x_48 = x_5;
goto block_71;
}
}
}
case 6:
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_114; uint8_t x_124; 
x_89 = lean_ctor_get(x_4, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_4, 2);
lean_inc(x_90);
lean_dec(x_4);
x_124 = lean_expr_has_expr_mvar(x_89);
if (x_124 == 0)
{
uint8_t x_125; 
x_125 = lean_expr_has_level_mvar(x_89);
if (x_125 == 0)
{
uint8_t x_126; 
x_126 = lean_expr_has_fvar(x_89);
if (x_126 == 0)
{
uint8_t x_127; 
lean_dec(x_89);
x_127 = 0;
x_91 = x_127;
x_92 = x_5;
goto block_113;
}
else
{
lean_object* x_128; 
x_128 = lean_box(0);
x_114 = x_128;
goto block_123;
}
}
else
{
lean_object* x_129; 
x_129 = lean_box(0);
x_114 = x_129;
goto block_123;
}
}
else
{
lean_object* x_130; 
x_130 = lean_box(0);
x_114 = x_130;
goto block_123;
}
block_113:
{
if (x_91 == 0)
{
lean_object* x_93; uint8_t x_102; 
x_102 = lean_expr_has_expr_mvar(x_90);
if (x_102 == 0)
{
uint8_t x_103; 
x_103 = lean_expr_has_level_mvar(x_90);
if (x_103 == 0)
{
uint8_t x_104; 
x_104 = lean_expr_has_fvar(x_90);
if (x_104 == 0)
{
uint8_t x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_90);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_105 = 0;
x_106 = lean_box(x_105);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_92);
return x_107;
}
else
{
lean_object* x_108; 
x_108 = lean_box(0);
x_93 = x_108;
goto block_101;
}
}
else
{
lean_object* x_109; 
x_109 = lean_box(0);
x_93 = x_109;
goto block_101;
}
}
else
{
lean_object* x_110; 
x_110 = lean_box(0);
x_93 = x_110;
goto block_101;
}
block_101:
{
uint8_t x_94; 
lean_dec(x_93);
x_94 = l_HashMapImp_contains___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__1(x_92, x_90);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_box(0);
lean_inc(x_90);
x_96 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__3(x_92, x_90, x_95);
x_4 = x_90;
x_5 = x_96;
goto _start;
}
else
{
uint8_t x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_90);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_98 = 0;
x_99 = lean_box(x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_92);
return x_100;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_90);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_111 = lean_box(x_91);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_92);
return x_112;
}
}
block_123:
{
uint8_t x_115; 
lean_dec(x_114);
x_115 = l_HashMapImp_contains___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__1(x_5, x_89);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_116 = lean_box(0);
lean_inc(x_89);
x_117 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__3(x_5, x_89, x_116);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_118 = l_Lean_AbstractMetavarContext_DependsOn_dep___main___rarg(x_1, x_2, x_3, x_89, x_117);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_unbox(x_119);
lean_dec(x_119);
x_91 = x_121;
x_92 = x_120;
goto block_113;
}
else
{
uint8_t x_122; 
lean_dec(x_89);
x_122 = 0;
x_91 = x_122;
x_92 = x_5;
goto block_113;
}
}
}
case 7:
{
lean_object* x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; lean_object* x_156; uint8_t x_166; 
x_131 = lean_ctor_get(x_4, 1);
lean_inc(x_131);
x_132 = lean_ctor_get(x_4, 2);
lean_inc(x_132);
lean_dec(x_4);
x_166 = lean_expr_has_expr_mvar(x_131);
if (x_166 == 0)
{
uint8_t x_167; 
x_167 = lean_expr_has_level_mvar(x_131);
if (x_167 == 0)
{
uint8_t x_168; 
x_168 = lean_expr_has_fvar(x_131);
if (x_168 == 0)
{
uint8_t x_169; 
lean_dec(x_131);
x_169 = 0;
x_133 = x_169;
x_134 = x_5;
goto block_155;
}
else
{
lean_object* x_170; 
x_170 = lean_box(0);
x_156 = x_170;
goto block_165;
}
}
else
{
lean_object* x_171; 
x_171 = lean_box(0);
x_156 = x_171;
goto block_165;
}
}
else
{
lean_object* x_172; 
x_172 = lean_box(0);
x_156 = x_172;
goto block_165;
}
block_155:
{
if (x_133 == 0)
{
lean_object* x_135; uint8_t x_144; 
x_144 = lean_expr_has_expr_mvar(x_132);
if (x_144 == 0)
{
uint8_t x_145; 
x_145 = lean_expr_has_level_mvar(x_132);
if (x_145 == 0)
{
uint8_t x_146; 
x_146 = lean_expr_has_fvar(x_132);
if (x_146 == 0)
{
uint8_t x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_132);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_147 = 0;
x_148 = lean_box(x_147);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_134);
return x_149;
}
else
{
lean_object* x_150; 
x_150 = lean_box(0);
x_135 = x_150;
goto block_143;
}
}
else
{
lean_object* x_151; 
x_151 = lean_box(0);
x_135 = x_151;
goto block_143;
}
}
else
{
lean_object* x_152; 
x_152 = lean_box(0);
x_135 = x_152;
goto block_143;
}
block_143:
{
uint8_t x_136; 
lean_dec(x_135);
x_136 = l_HashMapImp_contains___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__1(x_134, x_132);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_box(0);
lean_inc(x_132);
x_138 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__3(x_134, x_132, x_137);
x_4 = x_132;
x_5 = x_138;
goto _start;
}
else
{
uint8_t x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_132);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_140 = 0;
x_141 = lean_box(x_140);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_134);
return x_142;
}
}
}
else
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_132);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_153 = lean_box(x_133);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_134);
return x_154;
}
}
block_165:
{
uint8_t x_157; 
lean_dec(x_156);
x_157 = l_HashMapImp_contains___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__1(x_5, x_131);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_158 = lean_box(0);
lean_inc(x_131);
x_159 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__3(x_5, x_131, x_158);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_160 = l_Lean_AbstractMetavarContext_DependsOn_dep___main___rarg(x_1, x_2, x_3, x_131, x_159);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_163 = lean_unbox(x_161);
lean_dec(x_161);
x_133 = x_163;
x_134 = x_162;
goto block_155;
}
else
{
uint8_t x_164; 
lean_dec(x_131);
x_164 = 0;
x_133 = x_164;
x_134 = x_5;
goto block_155;
}
}
}
case 8:
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; uint8_t x_199; lean_object* x_200; lean_object* x_219; uint8_t x_229; 
x_173 = lean_ctor_get(x_4, 1);
lean_inc(x_173);
x_174 = lean_ctor_get(x_4, 2);
lean_inc(x_174);
x_175 = lean_ctor_get(x_4, 3);
lean_inc(x_175);
lean_dec(x_4);
x_229 = lean_expr_has_expr_mvar(x_173);
if (x_229 == 0)
{
uint8_t x_230; 
x_230 = lean_expr_has_level_mvar(x_173);
if (x_230 == 0)
{
uint8_t x_231; 
x_231 = lean_expr_has_fvar(x_173);
if (x_231 == 0)
{
uint8_t x_232; 
lean_dec(x_173);
x_232 = 0;
x_199 = x_232;
x_200 = x_5;
goto block_218;
}
else
{
lean_object* x_233; 
x_233 = lean_box(0);
x_219 = x_233;
goto block_228;
}
}
else
{
lean_object* x_234; 
x_234 = lean_box(0);
x_219 = x_234;
goto block_228;
}
}
else
{
lean_object* x_235; 
x_235 = lean_box(0);
x_219 = x_235;
goto block_228;
}
block_198:
{
if (x_176 == 0)
{
lean_object* x_178; uint8_t x_187; 
x_187 = lean_expr_has_expr_mvar(x_175);
if (x_187 == 0)
{
uint8_t x_188; 
x_188 = lean_expr_has_level_mvar(x_175);
if (x_188 == 0)
{
uint8_t x_189; 
x_189 = lean_expr_has_fvar(x_175);
if (x_189 == 0)
{
uint8_t x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_175);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_190 = 0;
x_191 = lean_box(x_190);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_177);
return x_192;
}
else
{
lean_object* x_193; 
x_193 = lean_box(0);
x_178 = x_193;
goto block_186;
}
}
else
{
lean_object* x_194; 
x_194 = lean_box(0);
x_178 = x_194;
goto block_186;
}
}
else
{
lean_object* x_195; 
x_195 = lean_box(0);
x_178 = x_195;
goto block_186;
}
block_186:
{
uint8_t x_179; 
lean_dec(x_178);
x_179 = l_HashMapImp_contains___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__1(x_177, x_175);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; 
x_180 = lean_box(0);
lean_inc(x_175);
x_181 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__3(x_177, x_175, x_180);
x_4 = x_175;
x_5 = x_181;
goto _start;
}
else
{
uint8_t x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_175);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_183 = 0;
x_184 = lean_box(x_183);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_177);
return x_185;
}
}
}
else
{
lean_object* x_196; lean_object* x_197; 
lean_dec(x_175);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_196 = lean_box(x_176);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_177);
return x_197;
}
}
block_218:
{
lean_object* x_201; 
if (x_199 == 0)
{
uint8_t x_211; 
x_211 = lean_expr_has_expr_mvar(x_174);
if (x_211 == 0)
{
uint8_t x_212; 
x_212 = lean_expr_has_level_mvar(x_174);
if (x_212 == 0)
{
uint8_t x_213; 
x_213 = lean_expr_has_fvar(x_174);
if (x_213 == 0)
{
uint8_t x_214; 
lean_dec(x_174);
x_214 = 0;
x_176 = x_214;
x_177 = x_200;
goto block_198;
}
else
{
lean_object* x_215; 
x_215 = lean_box(0);
x_201 = x_215;
goto block_210;
}
}
else
{
lean_object* x_216; 
x_216 = lean_box(0);
x_201 = x_216;
goto block_210;
}
}
else
{
lean_object* x_217; 
x_217 = lean_box(0);
x_201 = x_217;
goto block_210;
}
}
else
{
lean_dec(x_174);
x_176 = x_199;
x_177 = x_200;
goto block_198;
}
block_210:
{
uint8_t x_202; 
lean_dec(x_201);
x_202 = l_HashMapImp_contains___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__1(x_200, x_174);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; 
x_203 = lean_box(0);
lean_inc(x_174);
x_204 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__3(x_200, x_174, x_203);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_205 = l_Lean_AbstractMetavarContext_DependsOn_dep___main___rarg(x_1, x_2, x_3, x_174, x_204);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_dec(x_205);
x_208 = lean_unbox(x_206);
lean_dec(x_206);
x_176 = x_208;
x_177 = x_207;
goto block_198;
}
else
{
uint8_t x_209; 
lean_dec(x_174);
x_209 = 0;
x_176 = x_209;
x_177 = x_200;
goto block_198;
}
}
}
block_228:
{
uint8_t x_220; 
lean_dec(x_219);
x_220 = l_HashMapImp_contains___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__1(x_5, x_173);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; 
x_221 = lean_box(0);
lean_inc(x_173);
x_222 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__3(x_5, x_173, x_221);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_223 = l_Lean_AbstractMetavarContext_DependsOn_dep___main___rarg(x_1, x_2, x_3, x_173, x_222);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec(x_223);
x_226 = lean_unbox(x_224);
lean_dec(x_224);
x_199 = x_226;
x_200 = x_225;
goto block_218;
}
else
{
uint8_t x_227; 
lean_dec(x_173);
x_227 = 0;
x_199 = x_227;
x_200 = x_5;
goto block_218;
}
}
}
case 10:
{
lean_object* x_236; lean_object* x_237; uint8_t x_246; 
x_236 = lean_ctor_get(x_4, 1);
lean_inc(x_236);
lean_dec(x_4);
x_246 = lean_expr_has_expr_mvar(x_236);
if (x_246 == 0)
{
uint8_t x_247; 
x_247 = lean_expr_has_level_mvar(x_236);
if (x_247 == 0)
{
uint8_t x_248; 
x_248 = lean_expr_has_fvar(x_236);
if (x_248 == 0)
{
uint8_t x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_236);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_249 = 0;
x_250 = lean_box(x_249);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_5);
return x_251;
}
else
{
lean_object* x_252; 
x_252 = lean_box(0);
x_237 = x_252;
goto block_245;
}
}
else
{
lean_object* x_253; 
x_253 = lean_box(0);
x_237 = x_253;
goto block_245;
}
}
else
{
lean_object* x_254; 
x_254 = lean_box(0);
x_237 = x_254;
goto block_245;
}
block_245:
{
uint8_t x_238; 
lean_dec(x_237);
x_238 = l_HashMapImp_contains___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__1(x_5, x_236);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; 
x_239 = lean_box(0);
lean_inc(x_236);
x_240 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__3(x_5, x_236, x_239);
x_4 = x_236;
x_5 = x_240;
goto _start;
}
else
{
uint8_t x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_236);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_242 = 0;
x_243 = lean_box(x_242);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_5);
return x_244;
}
}
}
case 11:
{
lean_object* x_255; lean_object* x_256; uint8_t x_265; 
x_255 = lean_ctor_get(x_4, 2);
lean_inc(x_255);
lean_dec(x_4);
x_265 = lean_expr_has_expr_mvar(x_255);
if (x_265 == 0)
{
uint8_t x_266; 
x_266 = lean_expr_has_level_mvar(x_255);
if (x_266 == 0)
{
uint8_t x_267; 
x_267 = lean_expr_has_fvar(x_255);
if (x_267 == 0)
{
uint8_t x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_255);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_268 = 0;
x_269 = lean_box(x_268);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_5);
return x_270;
}
else
{
lean_object* x_271; 
x_271 = lean_box(0);
x_256 = x_271;
goto block_264;
}
}
else
{
lean_object* x_272; 
x_272 = lean_box(0);
x_256 = x_272;
goto block_264;
}
}
else
{
lean_object* x_273; 
x_273 = lean_box(0);
x_256 = x_273;
goto block_264;
}
block_264:
{
uint8_t x_257; 
lean_dec(x_256);
x_257 = l_HashMapImp_contains___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__1(x_5, x_255);
if (x_257 == 0)
{
lean_object* x_258; lean_object* x_259; 
x_258 = lean_box(0);
lean_inc(x_255);
x_259 = l_HashMapImp_insert___at_Lean_AbstractMetavarContext_DependsOn_visit___spec__3(x_5, x_255, x_258);
x_4 = x_255;
x_5 = x_259;
goto _start;
}
else
{
uint8_t x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_255);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_261 = 0;
x_262 = lean_box(x_261);
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_5);
return x_263;
}
}
}
default: 
{
uint8_t x_274; lean_object* x_275; lean_object* x_276; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_274 = 0;
x_275 = lean_box(x_274);
x_276 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_5);
return x_276;
}
}
}
}
lean_object* l_Lean_AbstractMetavarContext_DependsOn_dep___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_AbstractMetavarContext_DependsOn_dep___main___rarg), 5, 0);
return x_2;
}
}
lean_object* l_panicWithPos___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_panicWithPos___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_anyMAux___main___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_anyMAux___main___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__4(x_1, x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Array_anyMAux___main___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_anyMAux___main___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__5(x_1, x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_PersistentArray_anyMAux___main___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_PersistentArray_anyMAux___main___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__3(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_anyMAux___main___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_anyMAux___main___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__6(x_1, x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_PersistentArray_anyM___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_PersistentArray_anyM___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__2(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_AbstractMetavarContext_DependsOn_dep___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_AbstractMetavarContext_DependsOn_dep___main___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_AbstractMetavarContext_DependsOn_dep(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_AbstractMetavarContext_DependsOn_dep___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_AbstractMetavarContext_DependsOn_main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_expr_has_fvar(x_4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = lean_expr_has_expr_mvar(x_4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_expr_has_level_mvar(x_4);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = l_Lean_AbstractMetavarContext_DependsOn_dep___main___rarg(x_1, x_2, x_3, x_4, x_5);
return x_12;
}
}
else
{
lean_object* x_13; 
x_13 = l_Lean_AbstractMetavarContext_DependsOn_dep___main___rarg(x_1, x_2, x_3, x_4, x_5);
return x_13;
}
}
else
{
lean_object* x_14; 
x_14 = l_Lean_AbstractMetavarContext_DependsOn_dep___main___rarg(x_1, x_2, x_3, x_4, x_5);
return x_14;
}
}
}
lean_object* l_Lean_AbstractMetavarContext_DependsOn_main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_AbstractMetavarContext_DependsOn_main___rarg), 5, 0);
return x_2;
}
}
lean_object* l_mkHashMap___at_Lean_AbstractMetavarContext_exprDependsOn___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_mkHashSet___at_Lean_AbstractMetavarContext_exprDependsOn___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_AbstractMetavarContext_exprDependsOn___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_Lean_AbstractMetavarContext_exprDependsOn___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_expr_has_fvar(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = lean_expr_has_expr_mvar(x_4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = lean_expr_has_level_mvar(x_4);
if (x_7 == 0)
{
uint8_t x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = 0;
x_9 = lean_box(x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_AbstractMetavarContext_exprDependsOn___rarg___closed__1;
x_11 = l_Lean_AbstractMetavarContext_DependsOn_dep___main___rarg(x_1, x_2, x_3, x_4, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Lean_AbstractMetavarContext_exprDependsOn___rarg___closed__1;
x_14 = l_Lean_AbstractMetavarContext_DependsOn_dep___main___rarg(x_1, x_2, x_3, x_4, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_Lean_AbstractMetavarContext_exprDependsOn___rarg___closed__1;
x_17 = l_Lean_AbstractMetavarContext_DependsOn_dep___main___rarg(x_1, x_2, x_3, x_4, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
return x_18;
}
}
}
lean_object* l_Lean_AbstractMetavarContext_exprDependsOn(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_AbstractMetavarContext_exprDependsOn___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_AbstractMetavarContext_localDeclDependsOn___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_expr_has_fvar(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = lean_expr_has_expr_mvar(x_5);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_expr_has_level_mvar(x_5);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = 0;
x_10 = lean_box(x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_HashMap_Inhabited___closed__1;
x_12 = l_Lean_AbstractMetavarContext_DependsOn_dep___main___rarg(x_1, x_2, x_3, x_5, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_HashMap_Inhabited___closed__1;
x_15 = l_Lean_AbstractMetavarContext_DependsOn_dep___main___rarg(x_1, x_2, x_3, x_5, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = l_HashMap_Inhabited___closed__1;
x_18 = l_Lean_AbstractMetavarContext_DependsOn_dep___main___rarg(x_1, x_2, x_3, x_5, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_37; 
x_20 = lean_ctor_get(x_4, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_4, 4);
lean_inc(x_21);
lean_dec(x_4);
x_37 = lean_expr_has_fvar(x_20);
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = lean_expr_has_expr_mvar(x_20);
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = lean_expr_has_level_mvar(x_20);
if (x_39 == 0)
{
uint8_t x_40; lean_object* x_41; 
lean_dec(x_20);
x_40 = 0;
x_41 = l_HashMap_Inhabited___closed__1;
x_22 = x_40;
x_23 = x_41;
goto block_36;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_42 = l_HashMap_Inhabited___closed__1;
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_43 = l_Lean_AbstractMetavarContext_DependsOn_dep___main___rarg(x_1, x_2, x_3, x_20, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_unbox(x_44);
lean_dec(x_44);
x_22 = x_46;
x_23 = x_45;
goto block_36;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_47 = l_HashMap_Inhabited___closed__1;
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_48 = l_Lean_AbstractMetavarContext_DependsOn_dep___main___rarg(x_1, x_2, x_3, x_20, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_unbox(x_49);
lean_dec(x_49);
x_22 = x_51;
x_23 = x_50;
goto block_36;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = l_HashMap_Inhabited___closed__1;
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_53 = l_Lean_AbstractMetavarContext_DependsOn_dep___main___rarg(x_1, x_2, x_3, x_20, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_unbox(x_54);
lean_dec(x_54);
x_22 = x_56;
x_23 = x_55;
goto block_36;
}
block_36:
{
if (x_22 == 0)
{
uint8_t x_24; 
x_24 = lean_expr_has_fvar(x_21);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = lean_expr_has_expr_mvar(x_21);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = lean_expr_has_level_mvar(x_21);
if (x_26 == 0)
{
uint8_t x_27; lean_object* x_28; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = 0;
x_28 = lean_box(x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_AbstractMetavarContext_DependsOn_dep___main___rarg(x_1, x_2, x_3, x_21, x_23);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_AbstractMetavarContext_DependsOn_dep___main___rarg(x_1, x_2, x_3, x_21, x_23);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Lean_AbstractMetavarContext_DependsOn_dep___main___rarg(x_1, x_2, x_3, x_21, x_23);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
return x_34;
}
}
else
{
lean_object* x_35; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = lean_box(x_22);
return x_35;
}
}
}
}
}
lean_object* l_Lean_AbstractMetavarContext_localDeclDependsOn(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_AbstractMetavarContext_localDeclDependsOn___rarg), 4, 0);
return x_2;
}
}
lean_object* initialize_Init_Control_Reader(lean_object*);
lean_object* initialize_Init_Control_Conditional(lean_object*);
lean_object* initialize_Init_Data_Option_Default(lean_object*);
lean_object* initialize_Init_Lean_LocalContext(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_AbstractMetavarContext(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Reader(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Conditional(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Default(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_LocalContext(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_panicWithPos___at_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___spec__1___rarg___closed__1 = _init_l_panicWithPos___at_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___spec__1___rarg___closed__1();
lean_mark_persistent(l_panicWithPos___at_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___spec__1___rarg___closed__1);
l_panicWithPos___at_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___spec__1___rarg___closed__2 = _init_l_panicWithPos___at_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___spec__1___rarg___closed__2();
lean_mark_persistent(l_panicWithPos___at_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___spec__1___rarg___closed__2);
l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___rarg___closed__1 = _init_l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___rarg___closed__1();
lean_mark_persistent(l_Lean_AbstractMetavarContext_InstantiateExprMVars_instantiateDelayedAux___main___rarg___closed__1);
l_Lean_AbstractMetavarContext_instantiateMVars___rarg___closed__1 = _init_l_Lean_AbstractMetavarContext_instantiateMVars___rarg___closed__1();
lean_mark_persistent(l_Lean_AbstractMetavarContext_instantiateMVars___rarg___closed__1);
l_panicWithPos___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__1___closed__1 = _init_l_panicWithPos___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__1___closed__1();
lean_mark_persistent(l_panicWithPos___at_Lean_AbstractMetavarContext_DependsOn_dep___main___spec__1___closed__1);
l_Lean_AbstractMetavarContext_DependsOn_dep___main___rarg___closed__1 = _init_l_Lean_AbstractMetavarContext_DependsOn_dep___main___rarg___closed__1();
lean_mark_persistent(l_Lean_AbstractMetavarContext_DependsOn_dep___main___rarg___closed__1);
l_Lean_AbstractMetavarContext_exprDependsOn___rarg___closed__1 = _init_l_Lean_AbstractMetavarContext_exprDependsOn___rarg___closed__1();
lean_mark_persistent(l_Lean_AbstractMetavarContext_exprDependsOn___rarg___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
