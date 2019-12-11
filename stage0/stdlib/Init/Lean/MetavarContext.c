// Lean compiler output
// Module: Init.Lean.MetavarContext
// Imports: Init.Control.Reader Init.Data.Nat Init.Data.Option Init.Lean.Data.NameGenerator Init.Lean.Util.MonadCache Init.Lean.LocalContext
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
lean_object* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getDelayedAssignment___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldr___main___at_Lean_MetavarContext_hasAssignedMVar___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldRevMAux___main___at_Lean_MetavarContext_mkBinding___spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_InstantiateExprMVars_main(lean_object*, lean_object*);
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l___private_Init_Lean_MetavarContext_19__mkForallAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_Exception_toString___closed__6;
lean_object* l___private_Init_Lean_MetavarContext_5__instantiateDelayedAux___main___closed__1;
lean_object* l_Nat_foldRevMAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isLevelAssigned___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_MetavarContext_MkBinding_Exception_toString___spec__2(lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_20__mkMVarApp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter___closed__2;
lean_object* l_Lean_LocalContext_foldlFromM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__39___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_mkHashMap___at_Lean_MetavarContext_instantiateMVars___spec__1(lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getLevelAssignment___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldRevMAux___main___at___private_Init_Lean_MetavarContext_19__mkForallAux___spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_mkBinding___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_MetavarContext_assignDelayed___spec__4(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_17__getInScope___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_5__instantiateDelayedAux___main___closed__2;
lean_object* l___private_Init_Lean_MetavarContext_18__withFreshCache(lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter___closed__1;
lean_object* l_PersistentHashMap_insert___at_Lean_MetavarContext_assignExpr___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_5__withAppRevAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_mkBinding___at___private_Init_Lean_MetavarContext_19__mkForallAux___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filterAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlFromMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__41(lean_object*);
lean_object* l_Lean_MetavarContext_instantiateMVars(lean_object*, lean_object*);
lean_object* l_Nat_foldRevMAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_findDecl___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldRevMAux___main___at___private_Init_Lean_MetavarContext_19__mkForallAux___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter___lambda__2(lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__1;
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__48___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_exprDependsOn___closed__1;
lean_object* l_Lean_MetavarContext_addLevelMVarDecl(lean_object*, lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_20__mkMVarApp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isDelayedAssigned___spec__2(lean_object*, size_t, lean_object*);
uint8_t l_PersistentArray_anyM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__4(lean_object*, lean_object*);
extern lean_object* l_EIO_Monad___closed__1;
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern size_t l_PersistentHashMap_insertAux___main___rarg___closed__2;
extern lean_object* l_Option_get_x21___rarg___closed__3;
lean_object* l___private_Init_Lean_MetavarContext_14__reduceLocalContext(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateMData_x21___closed__2;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignDelayed___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_metavar_ctx(lean_object*);
lean_object* l_Nat_foldRevMAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_MetavarContext_addExprMVarDecl___spec__4(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_expand___at___private_Init_Lean_MetavarContext_2__visit___spec__5(lean_object*, lean_object*);
lean_object* lean_local_ctx_erase(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_contains___at_Lean_MetavarContext_isExprAssigned___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
size_t l_USize_sub(size_t, size_t);
uint8_t lean_metavar_ctx_is_delayed_assigned(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_MetavarContext_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_1__mkPanicMessage(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__43___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_8__visit_x3f___spec__3(lean_object*, lean_object*, lean_object*);
uint8_t l_PersistentHashMap_contains___at_Lean_MetavarContext_isDelayedAssigned___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
lean_object* l_Lean_MetavarContext_getDecl___closed__2;
uint8_t l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__35(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__45___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_mkBinding(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDecl___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_5__instantiateDelayedAux___main___closed__3;
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_MetavarContext_isDelayedAssigned___boxed(lean_object*, lean_object*);
lean_object* l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__17___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_5__instantiateDelayedAux___main___at_Lean_MetavarContext_InstantiateExprMVars_main___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_addExprMVarDecl___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findFVar(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_Exception_toString___closed__2;
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_12__getLocalDeclWithSmallestIdx___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_isUnaryNode___rarg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__23(lean_object*, lean_object*);
uint8_t l_PersistentHashMap_contains___at_Lean_MetavarContext_isLevelAssigned___spec__1(lean_object*, lean_object*);
lean_object* l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__23___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_5__instantiateDelayedAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Level_Inhabited;
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__45(lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l___private_Init_Lean_MetavarContext_21__mkAuxMVar(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_HashMapImp_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__29(lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__3;
lean_object* l_PersistentHashMap_find___at_Lean_MetavarContext_getExprAssignment___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter___closed__4;
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_PersistentHashMap_contains___at_Lean_MetavarContext_isLevelAssigned___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_AssocList_contains___main___at___private_Init_Lean_MetavarContext_8__visit_x3f___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_find___at_Lean_MetavarContext_findDecl___spec__1(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__44(lean_object*);
uint8_t l_PersistentHashMap_contains___at_Lean_MetavarContext_isExprAssigned___spec__1(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_4__modifyCtx(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_isLevelAssignable___boxed(lean_object*, lean_object*);
uint8_t l_Lean_LocalContext_contains(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_MetavarContext_addExprMVarDecl___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__47___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_Inhabited___closed__1;
lean_object* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getLevelAssignment___spec__2(lean_object*, size_t, lean_object*);
lean_object* l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__11___boxed(lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_eraseAux___main___at_Lean_MetavarContext_eraseDelayed___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__37___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_eraseAux___main___at_Lean_MetavarContext_eraseDelayed___spec__2(lean_object*, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_11__abstractRange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_5__instantiateDelayedAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_anyM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__10___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateLambdaE_x21___closed__1;
lean_object* lean_metavar_ctx_assign_delayed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_foldlFromM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__39___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_hasAssignableMVar___main(lean_object*, lean_object*);
lean_object* lean_metavar_ctx_find_decl(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_10__dep___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
uint8_t lean_metavar_ctx_is_expr_assigned(lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_Inhabited___closed__2;
extern lean_object* l_PersistentArray_getAux___main___rarg___closed__1;
lean_object* l___private_Init_Lean_MetavarContext_5__instantiateDelayedAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldRevMAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MetavarContext_hasAssignableLevelMVar___main(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignLevel___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_HasRepr___rarg___closed__1;
lean_object* l___private_Init_Lean_MetavarContext_3__getMCtx(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_List_foldr___main___at_Lean_MetavarContext_hasAssignableMVar___main___spec__1(lean_object*, uint8_t, lean_object*);
uint8_t l_PersistentArray_anyM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__22(lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_elimMVarDeps___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited___closed__1;
lean_object* l_Lean_MetavarDecl_Inhabited___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_List_mapM___main___at_Lean_MetavarContext_InstantiateExprMVars_main___main___spec__2(lean_object*, lean_object*);
lean_object* l_PersistentArray_anyM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__28___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_11__abstractRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_10__dep___main___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateMVars___closed__1;
lean_object* l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter___lambda__1(lean_object*, lean_object*);
lean_object* l_EStateM_bind___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__36(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_MetavarContext_assignDelayed___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_12__getLocalDeclWithSmallestIdx___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___main(lean_object*, lean_object*);
lean_object* l_HashMapImp_contains___at___private_Init_Lean_MetavarContext_8__visit_x3f___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_12__getLocalDeclWithSmallestIdx___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldRevMAux___main___at_Lean_MetavarContext_mkBinding___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Expr_5__withAppRevAux___main___at_Lean_MetavarContext_InstantiateExprMVars_main___main___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_Exception_toString___closed__5;
lean_object* l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l_AssocList_contains___main___at___private_Init_Lean_MetavarContext_2__visit___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getExprAssignment___spec__2___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MetavarContext_hasAssignedLevelMVar(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_16__getMCtx(lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getLevelAssignment___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_isExprAssignable___boxed(lean_object*, lean_object*);
lean_object* l_Nat_foldRevMAux___main___at_Lean_MetavarContext_mkBinding___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_level_update_max(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldRevMAux___main___at___private_Init_Lean_MetavarContext_19__mkForallAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_erase___at_Lean_MetavarContext_eraseDelayed___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_MetavarContext_InstantiateExprMVars_main___main___spec__3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_mkBinding___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Nat_foldRevAux___main___at_Lean_LocalContext_mkBinding___spec__1___closed__1;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_21__mkAuxMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_17__getInScope(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insert___at_Lean_MetavarContext_addLevelMVarDecl___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_foldlM___main___at___private_Init_Lean_MetavarContext_2__visit___spec__7(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_elimMVarDeps(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignExpr___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_isWellFormed(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_find___at_Lean_MetavarContext_findLevelDepth___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__43___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_isLevelAssigned___boxed(lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_Exception_toString(lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__37(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_PersistentHashMap_insert___at_Lean_MetavarContext_assignLevel___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDecl___closed__3;
lean_object* l_Lean_MetavarContext_instantiateLevelMVars(lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__42___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l_PersistentHashMap_find___at_Lean_MetavarContext_findDecl___spec__1___boxed(lean_object*, lean_object*);
uint8_t l_PersistentArray_anyM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__28(lean_object*, lean_object*);
lean_object* l_PersistentArray_anyM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__16___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_mkBinding___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_PersistentHashMap_insertAux___main___rarg___closed__3;
lean_object* l_Lean_LocalContext_foldlFromM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__39(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_Inhabited;
size_t l_Lean_Expr_hash(lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_5__instantiateDelayedAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__2;
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_mkBinding___lambda__1___closed__1;
extern lean_object* l_List_reprAux___main___rarg___closed__1;
lean_object* l_Lean_MetavarContext_hasAssignableLevelMVar___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_MetavarContext_assignExpr___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlFromM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__40___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getLevelAssignment___spec__2___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__5(lean_object*, lean_object*);
size_t l_USize_shiftLeft(size_t, size_t);
extern lean_object* l_Lean_LocalDecl_Inhabited;
lean_object* lean_metavar_ctx_assign_expr(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__33(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_indexOfAux___main___at_Lean_MetavarContext_eraseDelayed___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_isWellFormed___main(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isExprAssigned___spec__2(lean_object*, size_t, lean_object*);
lean_object* l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__5___boxed(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_10__dep___main___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_localDeclDependsOn(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__44___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_HashMapImp_moveEntries___main___at___private_Init_Lean_MetavarContext_2__visit___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_findLevelDepth(lean_object*, lean_object*);
lean_object* l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__35___boxed(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_MetavarContext_addLevelMVarDecl___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isAuxDecl(uint8_t);
lean_object* l_Lean_MetavarContext_MkBinding_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_mul(size_t, size_t);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__43(lean_object*);
lean_object* l_mkHashMapImp___rarg(lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_mkBinding___at_Lean_MetavarContext_mkBinding___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldRevMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getDelayedAssignment___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_PersistentArray_anyM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__10(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__46___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_findLevelDepth___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter___closed__3;
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__36___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignExpr___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Id_Monad;
lean_object* l_Nat_foldRevMAux___main___at_Lean_MetavarContext_mkBinding___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
uint8_t l_PersistentHashMap_containsAtAux___main___at_Lean_MetavarContext_isLevelAssigned___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filterAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_HashMapImp_contains___at___private_Init_Lean_MetavarContext_8__visit_x3f___spec__1(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__47___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_mkForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getDelayedAssignment___spec__2(lean_object*, size_t, lean_object*);
lean_object* l_Lean_LocalContext_foldlFromM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__39___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__45___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateProj_x21___closed__2;
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__46(lean_object*);
uint8_t l_PersistentArray_anyM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__16(lean_object*, lean_object*);
lean_object* l_Lean_LocalInstance_beq___boxed(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_findDecl___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignLevel___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_Exception_toString___closed__3;
lean_object* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_findDecl___spec__2(lean_object*, size_t, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__48___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__42___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_containsAtAux___main___at_Lean_MetavarContext_isLevelAssigned___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_exprDependsOn(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignDelayed___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_metavar_ctx_get_delayed_assignment(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__46___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_Exception_hasToString;
lean_object* l___private_Init_Lean_MetavarContext_18__withFreshCache___rarg(lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_17__getInScope___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_hasAssignedLevelMVar___main___boxed(lean_object*, lean_object*);
lean_object* l_AssocList_replace___main___at___private_Init_Lean_MetavarContext_2__visit___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_hasAssignableLevelMVar___main___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__44___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter;
lean_object* l_Lean_LocalDecl_index(lean_object*);
lean_object* l_PersistentArray_anyM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__34___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_MetavarContext_assignLevel___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getExprAssignment___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__47(lean_object*);
lean_object* lean_metavar_ctx_get_level_assignment(lean_object*, lean_object*);
lean_object* l_Nat_foldRevMAux___main___at___private_Init_Lean_MetavarContext_19__mkForallAux___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_hasAssignableMVar___boxed(lean_object*, lean_object*);
uint8_t l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isLevelAssigned___spec__2(lean_object*, size_t, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_addLevelMVarDecl___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_MetavarContext_addExprMVarDecl___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_Exception_hasToString___closed__1;
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Init_Lean_MetavarContext_14__reduceLocalContext___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_sort(lean_object*, lean_object*);
lean_object* l_Lean_MetavarDecl_Inhabited;
lean_object* l___private_Init_Lean_Expr_5__withAppRevAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_addLevelMVarDecl___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_14__reduceLocalContext___boxed(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_USize_decLe(size_t, size_t);
lean_object* l_AssocList_foldlM___main___at___private_Init_Lean_MetavarContext_8__visit_x3f___spec__6(lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_17__getInScope___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getDelayedAssignment___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*);
lean_object* l_HashMapImp_find___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MetavarContext_hasAssignableLevelMVar(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_isExprAssigned___boxed(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_find___at_Lean_MetavarContext_getDelayedAssignment___spec__1___boxed(lean_object*, lean_object*);
uint8_t l_AssocList_contains___main___at___private_Init_Lean_MetavarContext_8__visit_x3f___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_mkAppRev(lean_object*, lean_object*);
lean_object* lean_metavar_ctx_mk_decl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
extern uint8_t l_Bool_Inhabited;
lean_object* l___private_Init_Lean_MetavarContext_13__collectDeps(lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_Monad___rarg(lean_object*);
lean_object* l_panic(lean_object*, lean_object*, lean_object*);
lean_object* lean_metavar_ctx_assign_level(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_MetavarContext_addLevelMVarDecl___spec__4(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_MetavarContext_assignLevel___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isExprAssigned___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_find___at_Lean_MetavarContext_getExprAssignment___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_incDepth(lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__21(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_anyM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_eraseIdx_x27___rarg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_isLevelAssignable___closed__2;
lean_object* l_Lean_LocalInstance_hasBeq___closed__1;
lean_object* l_Lean_LocalInstance_hasBeq;
uint8_t l_Lean_MetavarContext_isLevelAssignable(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_12__getLocalDeclWithSmallestIdx___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_erase___at_Lean_MetavarContext_eraseDelayed___spec__1(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_MetavarContext_assignDelayed___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_8__visit_x3f(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insert___at_Lean_MetavarContext_assignDelayed___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_replace___main___at___private_Init_Lean_MetavarContext_8__visit_x3f___spec__7(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_updateLet_x21___closed__1;
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_level_update_succ(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_findDecl___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_mkHashSet___at_Lean_MetavarContext_exprDependsOn___spec__1(lean_object*);
lean_object* l_Lean_MetavarContext_getDecl___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__27(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_MetavarContext_assignLevel___spec__4(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insert___at_Lean_MetavarContext_addExprMVarDecl___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isDelayedAssigned___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_mkBinding___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLet(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Expr_Hashable;
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__48(lean_object*);
lean_object* l_Lean_MetavarContext_getLevelDepth(lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
uint8_t l_PersistentArray_anyM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__34(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_mkBinding(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_MetavarContext_assignExpr___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* l_PersistentArray_foldlFromM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__40___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkHashMap___at_Lean_MetavarContext_exprDependsOn___spec__2(lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_20__mkMVarApp(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_Exception_toString___closed__1;
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__38(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_foldr___main___at_Lean_MetavarContext_hasAssignedMVar___main___spec__1(lean_object*, uint8_t, lean_object*);
lean_object* l_PersistentHashMap_contains___at_Lean_MetavarContext_isDelayedAssigned___spec__1___boxed(lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_anyM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__4___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_15__visit(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_20__mkMVarApp___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__29___boxed(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_9__visit(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_6__instantiateDelayed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_isLevelAssignable___closed__1;
lean_object* l_Array_indexOfAux___main___at_Lean_MetavarContext_eraseDelayed___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_addExprMVarDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MetavarContext_isExprAssignable(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_hasAssignedLevelMVar___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_5__instantiateDelayedAux___main___at_Lean_MetavarContext_InstantiateExprMVars_main___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_Inhabited___closed__1;
lean_object* l_Lean_MetavarContext_mkForall(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_metavar_ctx_get_expr_assignment(lean_object*, lean_object*);
uint8_t l_Lean_LocalInstance_beq(lean_object*, lean_object*);
lean_object* l_AssocList_find___main___at___private_Init_Lean_MetavarContext_2__visit___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_MetavarContext_MkBinding_Exception_toString___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_metavar_ctx_erase_delayed(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
lean_object* l_HashMapImp_moveEntries___main___at___private_Init_Lean_MetavarContext_8__visit_x3f___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getLevelDepth___closed__1;
extern lean_object* l_Nat_Inhabited;
lean_object* l_PersistentArray_foldlFromM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__40(lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_mkBinding___at___private_Init_Lean_MetavarContext_19__mkForallAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_List_foldr___main___at_Lean_MetavarContext_hasAssignableMVar___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MetavarContext_hasAssignedLevelMVar___main(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getLevelDepth___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_12__getLocalDeclWithSmallestIdx___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_InstantiateExprMVars_instantiateLevelMVars(lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_MetavarContext_hasAssignableMVar___main___boxed(lean_object*, lean_object*);
lean_object* l_AssocList_find___main___at___private_Init_Lean_MetavarContext_2__visit___spec__2(lean_object*, lean_object*);
lean_object* l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1___boxed(lean_object*, lean_object*);
extern lean_object* l_HashMap_Inhabited___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_MetavarContext_addLevelMVarDecl___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__11(lean_object*, lean_object*);
uint8_t l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__17(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getExprAssignment___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_HasBeq;
lean_object* l_Lean_MetavarContext_DependsOn_main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_mkBinding___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_PersistentHashMap_find___at_Lean_MetavarContext_getLevelAssignment___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_PersistentArray_anyM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__22___boxed(lean_object*, lean_object*);
uint8_t lean_metavar_ctx_is_level_assigned(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_2__visit(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_findLevelDepth___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_12__getLocalDeclWithSmallestIdx(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_10__dep(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_mkBinding___at_Lean_MetavarContext_mkBinding___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_findLevelDepth___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_find___at_Lean_MetavarContext_getDelayedAssignment___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_InstantiateExprMVars_main___main(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_hasAssignedMVar___main(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_find___at_Lean_MetavarContext_getLevelAssignment___spec__1(lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__42(lean_object*);
extern lean_object* l_EStateM_MonadState___closed__2;
lean_object* l_List_toStringAux___main___at_Lean_MetavarContext_MkBinding_Exception_toString___spec__3(uint8_t, lean_object*);
extern lean_object* l_Lean_Expr_updateForallE_x21___closed__1;
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_MetavarContext_assignExpr___spec__4(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_const(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getExprAssignment___spec__2(lean_object*, size_t, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_findLevelDepth___spec__2(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_Level_updateIMax_x21___closed__2;
lean_object* l_HashMapImp_expand___at___private_Init_Lean_MetavarContext_8__visit_x3f___spec__4(lean_object*, lean_object*);
uint8_t l_Lean_LocalContext_isSubPrefixOf(lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlFromMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__41___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlFromMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__41___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Init_Lean_MetavarContext_14__reduceLocalContext___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_find___at_Lean_MetavarContext_findLevelDepth___spec__1(lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_MetavarContext_MkBinding_Exception_toString___spec__3___boxed(lean_object*, lean_object*);
uint8_t l_AssocList_contains___main___at___private_Init_Lean_MetavarContext_2__visit___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_mkBinding___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_findLevelDepth___spec__2___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isLet(lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_hasAssignableMVar(lean_object*, lean_object*);
lean_object* l_monadInhabited___rarg(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_Exception_toString___closed__4;
lean_object* l_Lean_MetavarContext_hasAssignedMVar(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_addExprMVarDecl___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalInstance_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_expr_eqv(x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_LocalInstance_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_LocalInstance_beq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_LocalInstance_hasBeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_LocalInstance_beq___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_LocalInstance_hasBeq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_LocalInstance_hasBeq___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_MetavarDecl_Inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_1 = lean_box(0);
x_2 = l_Lean_LocalContext_Inhabited___closed__2;
x_3 = l_Lean_Expr_Inhabited___closed__1;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_empty___closed__1;
x_6 = 0;
x_7 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*5, x_6);
return x_7;
}
}
lean_object* _init_l_Lean_MetavarDecl_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_MetavarDecl_Inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_MetavarContext_Inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_LocalContext_Inhabited___closed__1;
x_3 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_2);
lean_ctor_set(x_3, 5, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_MetavarContext_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_MetavarContext_Inhabited___closed__1;
return x_1;
}
}
lean_object* lean_mk_metavar_ctx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_dec(x_1);
x_2 = l_Lean_MetavarContext_Inhabited___closed__1;
return x_2;
}
}
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_MetavarContext_addExprMVarDecl___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_array_push(x_5, x_3);
x_13 = lean_array_push(x_6, x_4);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_array_push(x_5, x_3);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = lean_name_eq(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_array_fset(x_5, x_2, x_3);
x_26 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_27 = lean_array_fset(x_5, x_2, x_3);
x_28 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_MetavarContext_addExprMVarDecl___spec__4(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_array_fget(x_4, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_Name_hash(x_9);
x_12 = 1;
x_13 = x_1 - x_12;
x_14 = 5;
x_15 = x_14 * x_13;
x_16 = x_11 >> x_15;
x_17 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_addExprMVarDecl___spec__2(x_6, x_16, x_1, x_9, x_10);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_5 = x_19;
x_6 = x_17;
goto _start;
}
}
}
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_addExprMVarDecl___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_11 = x_2 & x_10;
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean_box(2);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_name_eq(x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_22 = l_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_array_fset(x_17, x_12, x_23);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_25 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_name_eq(x_4, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_array_fset(x_17, x_12, x_30);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_5);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = x_2 >> x_9;
x_37 = x_3 + x_8;
x_38 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_addExprMVarDecl___spec__2(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_39 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_39);
return x_1;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
x_41 = x_2 >> x_9;
x_42 = x_3 + x_8;
x_43 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_addExprMVarDecl___spec__2(x_40, x_41, x_42, x_4, x_5);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_array_fset(x_17, x_12, x_44);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_45);
return x_1;
}
}
default: 
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_5);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
}
}
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = 1;
x_50 = 5;
x_51 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_52 = x_2 & x_51;
x_53 = lean_usize_to_nat(x_52);
x_54 = lean_array_get_size(x_48);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_48);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_array_fget(x_48, x_53);
x_58 = lean_box(2);
x_59 = lean_array_fset(x_48, x_53, x_58);
switch (lean_obj_tag(x_57)) {
case 0:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_62 = x_57;
} else {
 lean_dec_ref(x_57);
 x_62 = lean_box(0);
}
x_63 = lean_name_eq(x_4, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_array_fset(x_59, x_53, x_65);
lean_dec(x_53);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_61);
lean_dec(x_60);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_5);
x_69 = lean_array_fset(x_59, x_53, x_68);
lean_dec(x_53);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
case 1:
{
lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_72 = x_57;
} else {
 lean_dec_ref(x_57);
 x_72 = lean_box(0);
}
x_73 = x_2 >> x_50;
x_74 = x_3 + x_49;
x_75 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_addExprMVarDecl___spec__2(x_71, x_73, x_74, x_4, x_5);
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_array_fset(x_59, x_53, x_76);
lean_dec(x_53);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
default: 
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_4);
lean_ctor_set(x_79, 1, x_5);
x_80 = lean_array_fset(x_59, x_53, x_79);
lean_dec(x_53);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; size_t x_84; uint8_t x_85; 
x_82 = lean_unsigned_to_nat(0u);
x_83 = l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_MetavarContext_addExprMVarDecl___spec__3(x_1, x_82, x_4, x_5);
x_84 = 7;
x_85 = x_84 <= x_3;
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = l_PersistentHashMap_getCollisionNodeSize___rarg(x_83);
x_87 = lean_unsigned_to_nat(4u);
x_88 = lean_nat_dec_lt(x_86, x_87);
lean_dec(x_86);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_83, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_83, 1);
lean_inc(x_90);
lean_dec(x_83);
x_91 = l_PersistentHashMap_insertAux___main___rarg___closed__3;
x_92 = l_Array_iterateMAux___main___at_Lean_MetavarContext_addExprMVarDecl___spec__4(x_3, x_89, x_90, x_89, x_82, x_91);
lean_dec(x_90);
lean_dec(x_89);
return x_92;
}
else
{
return x_83;
}
}
else
{
return x_83;
}
}
}
}
lean_object* l_PersistentHashMap_insert___at_Lean_MetavarContext_addExprMVarDecl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Name_hash(x_2);
x_8 = 1;
x_9 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_addExprMVarDecl___spec__2(x_5, x_7, x_8, x_2, x_3);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_6, x_10);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = l_Lean_Name_hash(x_2);
x_15 = 1;
x_16 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_addExprMVarDecl___spec__2(x_12, x_14, x_15, x_2, x_3);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_13, x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
lean_object* lean_metavar_ctx_mk_decl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_11 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_4);
lean_ctor_set(x_11, 2, x_6);
lean_ctor_set(x_11, 3, x_9);
lean_ctor_set(x_11, 4, x_5);
lean_ctor_set_uint8(x_11, sizeof(void*)*5, x_7);
x_12 = l_PersistentHashMap_insert___at_Lean_MetavarContext_addExprMVarDecl___spec__1(x_10, x_2, x_11);
lean_ctor_set(x_1, 2, x_12);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_ctor_get(x_1, 2);
x_16 = lean_ctor_get(x_1, 3);
x_17 = lean_ctor_get(x_1, 4);
x_18 = lean_ctor_get(x_1, 5);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
lean_inc(x_13);
x_19 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_19, 0, x_3);
lean_ctor_set(x_19, 1, x_4);
lean_ctor_set(x_19, 2, x_6);
lean_ctor_set(x_19, 3, x_13);
lean_ctor_set(x_19, 4, x_5);
lean_ctor_set_uint8(x_19, sizeof(void*)*5, x_7);
x_20 = l_PersistentHashMap_insert___at_Lean_MetavarContext_addExprMVarDecl___spec__1(x_15, x_2, x_19);
x_21 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 2, x_20);
lean_ctor_set(x_21, 3, x_16);
lean_ctor_set(x_21, 4, x_17);
lean_ctor_set(x_21, 5, x_18);
return x_21;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_MetavarContext_addExprMVarDecl___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Array_iterateMAux___main___at_Lean_MetavarContext_addExprMVarDecl___spec__4(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_addExprMVarDecl___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_addExprMVarDecl___spec__2(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l_Lean_MetavarContext_addExprMVarDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_7);
lean_dec(x_7);
x_9 = lean_metavar_ctx_mk_decl(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_MetavarContext_addLevelMVarDecl___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_array_push(x_5, x_3);
x_13 = lean_array_push(x_6, x_4);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_array_push(x_5, x_3);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = lean_name_eq(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_array_fset(x_5, x_2, x_3);
x_26 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_27 = lean_array_fset(x_5, x_2, x_3);
x_28 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_MetavarContext_addLevelMVarDecl___spec__4(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_array_fget(x_4, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_Name_hash(x_9);
x_12 = 1;
x_13 = x_1 - x_12;
x_14 = 5;
x_15 = x_14 * x_13;
x_16 = x_11 >> x_15;
x_17 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_addLevelMVarDecl___spec__2(x_6, x_16, x_1, x_9, x_10);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_5 = x_19;
x_6 = x_17;
goto _start;
}
}
}
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_addLevelMVarDecl___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_11 = x_2 & x_10;
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean_box(2);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_name_eq(x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_22 = l_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_array_fset(x_17, x_12, x_23);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_25 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_name_eq(x_4, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_array_fset(x_17, x_12, x_30);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_5);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = x_2 >> x_9;
x_37 = x_3 + x_8;
x_38 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_addLevelMVarDecl___spec__2(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_39 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_39);
return x_1;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
x_41 = x_2 >> x_9;
x_42 = x_3 + x_8;
x_43 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_addLevelMVarDecl___spec__2(x_40, x_41, x_42, x_4, x_5);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_array_fset(x_17, x_12, x_44);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_45);
return x_1;
}
}
default: 
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_5);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
}
}
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = 1;
x_50 = 5;
x_51 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_52 = x_2 & x_51;
x_53 = lean_usize_to_nat(x_52);
x_54 = lean_array_get_size(x_48);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_48);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_array_fget(x_48, x_53);
x_58 = lean_box(2);
x_59 = lean_array_fset(x_48, x_53, x_58);
switch (lean_obj_tag(x_57)) {
case 0:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_62 = x_57;
} else {
 lean_dec_ref(x_57);
 x_62 = lean_box(0);
}
x_63 = lean_name_eq(x_4, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_array_fset(x_59, x_53, x_65);
lean_dec(x_53);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_61);
lean_dec(x_60);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_5);
x_69 = lean_array_fset(x_59, x_53, x_68);
lean_dec(x_53);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
case 1:
{
lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_72 = x_57;
} else {
 lean_dec_ref(x_57);
 x_72 = lean_box(0);
}
x_73 = x_2 >> x_50;
x_74 = x_3 + x_49;
x_75 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_addLevelMVarDecl___spec__2(x_71, x_73, x_74, x_4, x_5);
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_array_fset(x_59, x_53, x_76);
lean_dec(x_53);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
default: 
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_4);
lean_ctor_set(x_79, 1, x_5);
x_80 = lean_array_fset(x_59, x_53, x_79);
lean_dec(x_53);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; size_t x_84; uint8_t x_85; 
x_82 = lean_unsigned_to_nat(0u);
x_83 = l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_MetavarContext_addLevelMVarDecl___spec__3(x_1, x_82, x_4, x_5);
x_84 = 7;
x_85 = x_84 <= x_3;
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = l_PersistentHashMap_getCollisionNodeSize___rarg(x_83);
x_87 = lean_unsigned_to_nat(4u);
x_88 = lean_nat_dec_lt(x_86, x_87);
lean_dec(x_86);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_83, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_83, 1);
lean_inc(x_90);
lean_dec(x_83);
x_91 = l_PersistentHashMap_insertAux___main___rarg___closed__3;
x_92 = l_Array_iterateMAux___main___at_Lean_MetavarContext_addLevelMVarDecl___spec__4(x_3, x_89, x_90, x_89, x_82, x_91);
lean_dec(x_90);
lean_dec(x_89);
return x_92;
}
else
{
return x_83;
}
}
else
{
return x_83;
}
}
}
}
lean_object* l_PersistentHashMap_insert___at_Lean_MetavarContext_addLevelMVarDecl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Name_hash(x_2);
x_8 = 1;
x_9 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_addLevelMVarDecl___spec__2(x_5, x_7, x_8, x_2, x_3);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_6, x_10);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = l_Lean_Name_hash(x_2);
x_15 = 1;
x_16 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_addLevelMVarDecl___spec__2(x_12, x_14, x_15, x_2, x_3);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_13, x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
lean_object* l_Lean_MetavarContext_addLevelMVarDecl(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_6 = l_PersistentHashMap_insert___at_Lean_MetavarContext_addLevelMVarDecl___spec__1(x_5, x_2, x_4);
lean_ctor_set(x_1, 1, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_ctor_get(x_1, 4);
x_12 = lean_ctor_get(x_1, 5);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
lean_inc(x_7);
x_13 = l_PersistentHashMap_insert___at_Lean_MetavarContext_addLevelMVarDecl___spec__1(x_8, x_2, x_7);
x_14 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 2, x_9);
lean_ctor_set(x_14, 3, x_10);
lean_ctor_set(x_14, 4, x_11);
lean_ctor_set(x_14, 5, x_12);
return x_14;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_MetavarContext_addLevelMVarDecl___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Array_iterateMAux___main___at_Lean_MetavarContext_addLevelMVarDecl___spec__4(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_addLevelMVarDecl___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_addLevelMVarDecl___spec__2(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_findDecl___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_name_eq(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
lean_object* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_findDecl___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
lean_object* x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = x_2 >> x_5;
x_18 = l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_findDecl___spec__2(x_16, x_17, x_3);
lean_dec(x_16);
return x_18;
}
default: 
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_findDecl___spec__3(x_20, x_21, lean_box(0), x_22, x_3);
return x_23;
}
}
}
lean_object* l_PersistentHashMap_find___at_Lean_MetavarContext_findDecl___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_findDecl___spec__2(x_3, x_4, x_2);
return x_5;
}
}
lean_object* lean_metavar_ctx_find_decl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_PersistentHashMap_find___at_Lean_MetavarContext_findDecl___spec__1(x_3, x_2);
lean_dec(x_2);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_findDecl___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_findDecl___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_findDecl___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_findDecl___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_PersistentHashMap_find___at_Lean_MetavarContext_findDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentHashMap_find___at_Lean_MetavarContext_findDecl___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l_Lean_MetavarContext_getDecl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Init.Lean.MetavarContext");
return x_1;
}
}
lean_object* _init_l_Lean_MetavarContext_getDecl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown metavariable");
return x_1;
}
}
lean_object* _init_l_Lean_MetavarContext_getDecl___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_MetavarContext_getDecl___closed__1;
x_2 = lean_unsigned_to_nat(277u);
x_3 = lean_unsigned_to_nat(15u);
x_4 = l_Lean_MetavarContext_getDecl___closed__2;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_MetavarContext_getDecl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = l_PersistentHashMap_find___at_Lean_MetavarContext_findDecl___spec__1(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_MetavarDecl_Inhabited;
x_6 = l_Lean_MetavarContext_getDecl___closed__3;
x_7 = lean_panic_fn(x_6);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
return x_8;
}
}
}
lean_object* l_Lean_MetavarContext_getDecl___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MetavarContext_getDecl(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_findLevelDepth___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_name_eq(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
lean_object* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_findLevelDepth___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
lean_object* x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = x_2 >> x_5;
x_18 = l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_findLevelDepth___spec__2(x_16, x_17, x_3);
lean_dec(x_16);
return x_18;
}
default: 
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_findLevelDepth___spec__3(x_20, x_21, lean_box(0), x_22, x_3);
return x_23;
}
}
}
lean_object* l_PersistentHashMap_find___at_Lean_MetavarContext_findLevelDepth___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_findLevelDepth___spec__2(x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_Lean_MetavarContext_findLevelDepth(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_PersistentHashMap_find___at_Lean_MetavarContext_findLevelDepth___spec__1(x_3, x_2);
return x_4;
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_findLevelDepth___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_findLevelDepth___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_findLevelDepth___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_findLevelDepth___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_PersistentHashMap_find___at_Lean_MetavarContext_findLevelDepth___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentHashMap_find___at_Lean_MetavarContext_findLevelDepth___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_MetavarContext_findLevelDepth___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MetavarContext_findLevelDepth(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l_Lean_MetavarContext_getLevelDepth___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_MetavarContext_getDecl___closed__1;
x_2 = lean_unsigned_to_nat(285u);
x_3 = lean_unsigned_to_nat(12u);
x_4 = l_Lean_MetavarContext_getDecl___closed__2;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_MetavarContext_getLevelDepth(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MetavarContext_findLevelDepth(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Nat_Inhabited;
x_5 = l_Lean_MetavarContext_getLevelDepth___closed__1;
x_6 = lean_panic_fn(x_5);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
return x_7;
}
}
}
lean_object* l_Lean_MetavarContext_getLevelDepth___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MetavarContext_getLevelDepth(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_MetavarContext_assignLevel___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_array_push(x_5, x_3);
x_13 = lean_array_push(x_6, x_4);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_array_push(x_5, x_3);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = lean_name_eq(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_array_fset(x_5, x_2, x_3);
x_26 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_27 = lean_array_fset(x_5, x_2, x_3);
x_28 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_MetavarContext_assignLevel___spec__4(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_array_fget(x_4, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_Name_hash(x_9);
x_12 = 1;
x_13 = x_1 - x_12;
x_14 = 5;
x_15 = x_14 * x_13;
x_16 = x_11 >> x_15;
x_17 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignLevel___spec__2(x_6, x_16, x_1, x_9, x_10);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_5 = x_19;
x_6 = x_17;
goto _start;
}
}
}
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignLevel___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_11 = x_2 & x_10;
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean_box(2);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_name_eq(x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_22 = l_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_array_fset(x_17, x_12, x_23);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_25 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_name_eq(x_4, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_array_fset(x_17, x_12, x_30);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_5);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = x_2 >> x_9;
x_37 = x_3 + x_8;
x_38 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignLevel___spec__2(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_39 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_39);
return x_1;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
x_41 = x_2 >> x_9;
x_42 = x_3 + x_8;
x_43 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignLevel___spec__2(x_40, x_41, x_42, x_4, x_5);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_array_fset(x_17, x_12, x_44);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_45);
return x_1;
}
}
default: 
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_5);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
}
}
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = 1;
x_50 = 5;
x_51 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_52 = x_2 & x_51;
x_53 = lean_usize_to_nat(x_52);
x_54 = lean_array_get_size(x_48);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_48);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_array_fget(x_48, x_53);
x_58 = lean_box(2);
x_59 = lean_array_fset(x_48, x_53, x_58);
switch (lean_obj_tag(x_57)) {
case 0:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_62 = x_57;
} else {
 lean_dec_ref(x_57);
 x_62 = lean_box(0);
}
x_63 = lean_name_eq(x_4, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_array_fset(x_59, x_53, x_65);
lean_dec(x_53);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_61);
lean_dec(x_60);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_5);
x_69 = lean_array_fset(x_59, x_53, x_68);
lean_dec(x_53);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
case 1:
{
lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_72 = x_57;
} else {
 lean_dec_ref(x_57);
 x_72 = lean_box(0);
}
x_73 = x_2 >> x_50;
x_74 = x_3 + x_49;
x_75 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignLevel___spec__2(x_71, x_73, x_74, x_4, x_5);
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_array_fset(x_59, x_53, x_76);
lean_dec(x_53);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
default: 
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_4);
lean_ctor_set(x_79, 1, x_5);
x_80 = lean_array_fset(x_59, x_53, x_79);
lean_dec(x_53);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; size_t x_84; uint8_t x_85; 
x_82 = lean_unsigned_to_nat(0u);
x_83 = l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_MetavarContext_assignLevel___spec__3(x_1, x_82, x_4, x_5);
x_84 = 7;
x_85 = x_84 <= x_3;
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = l_PersistentHashMap_getCollisionNodeSize___rarg(x_83);
x_87 = lean_unsigned_to_nat(4u);
x_88 = lean_nat_dec_lt(x_86, x_87);
lean_dec(x_86);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_83, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_83, 1);
lean_inc(x_90);
lean_dec(x_83);
x_91 = l_PersistentHashMap_insertAux___main___rarg___closed__3;
x_92 = l_Array_iterateMAux___main___at_Lean_MetavarContext_assignLevel___spec__4(x_3, x_89, x_90, x_89, x_82, x_91);
lean_dec(x_90);
lean_dec(x_89);
return x_92;
}
else
{
return x_83;
}
}
else
{
return x_83;
}
}
}
}
lean_object* l_PersistentHashMap_insert___at_Lean_MetavarContext_assignLevel___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Name_hash(x_2);
x_8 = 1;
x_9 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignLevel___spec__2(x_5, x_7, x_8, x_2, x_3);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_6, x_10);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = l_Lean_Name_hash(x_2);
x_15 = 1;
x_16 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignLevel___spec__2(x_12, x_14, x_15, x_2, x_3);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_13, x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
lean_object* lean_metavar_ctx_assign_level(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 3);
x_6 = l_PersistentHashMap_insert___at_Lean_MetavarContext_assignLevel___spec__1(x_5, x_2, x_3);
lean_ctor_set(x_1, 3, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_ctor_get(x_1, 4);
x_12 = lean_ctor_get(x_1, 5);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_13 = l_PersistentHashMap_insert___at_Lean_MetavarContext_assignLevel___spec__1(x_10, x_2, x_3);
x_14 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_14, 2, x_9);
lean_ctor_set(x_14, 3, x_13);
lean_ctor_set(x_14, 4, x_11);
lean_ctor_set(x_14, 5, x_12);
return x_14;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_MetavarContext_assignLevel___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Array_iterateMAux___main___at_Lean_MetavarContext_assignLevel___spec__4(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignLevel___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignLevel___spec__2(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_MetavarContext_assignExpr___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_array_push(x_5, x_3);
x_13 = lean_array_push(x_6, x_4);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_array_push(x_5, x_3);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = lean_name_eq(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_array_fset(x_5, x_2, x_3);
x_26 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_27 = lean_array_fset(x_5, x_2, x_3);
x_28 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_MetavarContext_assignExpr___spec__4(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_array_fget(x_4, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_Name_hash(x_9);
x_12 = 1;
x_13 = x_1 - x_12;
x_14 = 5;
x_15 = x_14 * x_13;
x_16 = x_11 >> x_15;
x_17 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignExpr___spec__2(x_6, x_16, x_1, x_9, x_10);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_5 = x_19;
x_6 = x_17;
goto _start;
}
}
}
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignExpr___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_11 = x_2 & x_10;
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean_box(2);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_name_eq(x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_22 = l_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_array_fset(x_17, x_12, x_23);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_25 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_name_eq(x_4, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_array_fset(x_17, x_12, x_30);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_5);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = x_2 >> x_9;
x_37 = x_3 + x_8;
x_38 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignExpr___spec__2(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_39 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_39);
return x_1;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
x_41 = x_2 >> x_9;
x_42 = x_3 + x_8;
x_43 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignExpr___spec__2(x_40, x_41, x_42, x_4, x_5);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_array_fset(x_17, x_12, x_44);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_45);
return x_1;
}
}
default: 
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_5);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
}
}
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = 1;
x_50 = 5;
x_51 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_52 = x_2 & x_51;
x_53 = lean_usize_to_nat(x_52);
x_54 = lean_array_get_size(x_48);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_48);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_array_fget(x_48, x_53);
x_58 = lean_box(2);
x_59 = lean_array_fset(x_48, x_53, x_58);
switch (lean_obj_tag(x_57)) {
case 0:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_62 = x_57;
} else {
 lean_dec_ref(x_57);
 x_62 = lean_box(0);
}
x_63 = lean_name_eq(x_4, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_array_fset(x_59, x_53, x_65);
lean_dec(x_53);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_61);
lean_dec(x_60);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_5);
x_69 = lean_array_fset(x_59, x_53, x_68);
lean_dec(x_53);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
case 1:
{
lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_72 = x_57;
} else {
 lean_dec_ref(x_57);
 x_72 = lean_box(0);
}
x_73 = x_2 >> x_50;
x_74 = x_3 + x_49;
x_75 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignExpr___spec__2(x_71, x_73, x_74, x_4, x_5);
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_array_fset(x_59, x_53, x_76);
lean_dec(x_53);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
default: 
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_4);
lean_ctor_set(x_79, 1, x_5);
x_80 = lean_array_fset(x_59, x_53, x_79);
lean_dec(x_53);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; size_t x_84; uint8_t x_85; 
x_82 = lean_unsigned_to_nat(0u);
x_83 = l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_MetavarContext_assignExpr___spec__3(x_1, x_82, x_4, x_5);
x_84 = 7;
x_85 = x_84 <= x_3;
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = l_PersistentHashMap_getCollisionNodeSize___rarg(x_83);
x_87 = lean_unsigned_to_nat(4u);
x_88 = lean_nat_dec_lt(x_86, x_87);
lean_dec(x_86);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_83, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_83, 1);
lean_inc(x_90);
lean_dec(x_83);
x_91 = l_PersistentHashMap_insertAux___main___rarg___closed__3;
x_92 = l_Array_iterateMAux___main___at_Lean_MetavarContext_assignExpr___spec__4(x_3, x_89, x_90, x_89, x_82, x_91);
lean_dec(x_90);
lean_dec(x_89);
return x_92;
}
else
{
return x_83;
}
}
else
{
return x_83;
}
}
}
}
lean_object* l_PersistentHashMap_insert___at_Lean_MetavarContext_assignExpr___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Name_hash(x_2);
x_8 = 1;
x_9 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignExpr___spec__2(x_5, x_7, x_8, x_2, x_3);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_6, x_10);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = l_Lean_Name_hash(x_2);
x_15 = 1;
x_16 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignExpr___spec__2(x_12, x_14, x_15, x_2, x_3);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_13, x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
lean_object* lean_metavar_ctx_assign_expr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 4);
x_6 = l_PersistentHashMap_insert___at_Lean_MetavarContext_assignExpr___spec__1(x_5, x_2, x_3);
lean_ctor_set(x_1, 4, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_ctor_get(x_1, 4);
x_12 = lean_ctor_get(x_1, 5);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_13 = l_PersistentHashMap_insert___at_Lean_MetavarContext_assignExpr___spec__1(x_11, x_2, x_3);
x_14 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_14, 2, x_9);
lean_ctor_set(x_14, 3, x_10);
lean_ctor_set(x_14, 4, x_13);
lean_ctor_set(x_14, 5, x_12);
return x_14;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_MetavarContext_assignExpr___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Array_iterateMAux___main___at_Lean_MetavarContext_assignExpr___spec__4(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignExpr___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignExpr___spec__2(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_MetavarContext_assignDelayed___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_array_push(x_5, x_3);
x_13 = lean_array_push(x_6, x_4);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_array_push(x_5, x_3);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = lean_name_eq(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_array_fset(x_5, x_2, x_3);
x_26 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_27 = lean_array_fset(x_5, x_2, x_3);
x_28 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_MetavarContext_assignDelayed___spec__4(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_array_fget(x_4, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_Name_hash(x_9);
x_12 = 1;
x_13 = x_1 - x_12;
x_14 = 5;
x_15 = x_14 * x_13;
x_16 = x_11 >> x_15;
x_17 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignDelayed___spec__2(x_6, x_16, x_1, x_9, x_10);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_5 = x_19;
x_6 = x_17;
goto _start;
}
}
}
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignDelayed___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_11 = x_2 & x_10;
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean_box(2);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_name_eq(x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_22 = l_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_array_fset(x_17, x_12, x_23);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_25 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_name_eq(x_4, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_array_fset(x_17, x_12, x_30);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_5);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = x_2 >> x_9;
x_37 = x_3 + x_8;
x_38 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignDelayed___spec__2(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_39 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_39);
return x_1;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
x_41 = x_2 >> x_9;
x_42 = x_3 + x_8;
x_43 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignDelayed___spec__2(x_40, x_41, x_42, x_4, x_5);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_array_fset(x_17, x_12, x_44);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_45);
return x_1;
}
}
default: 
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_5);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
}
}
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = 1;
x_50 = 5;
x_51 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_52 = x_2 & x_51;
x_53 = lean_usize_to_nat(x_52);
x_54 = lean_array_get_size(x_48);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_48);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_array_fget(x_48, x_53);
x_58 = lean_box(2);
x_59 = lean_array_fset(x_48, x_53, x_58);
switch (lean_obj_tag(x_57)) {
case 0:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_62 = x_57;
} else {
 lean_dec_ref(x_57);
 x_62 = lean_box(0);
}
x_63 = lean_name_eq(x_4, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_array_fset(x_59, x_53, x_65);
lean_dec(x_53);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_61);
lean_dec(x_60);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_5);
x_69 = lean_array_fset(x_59, x_53, x_68);
lean_dec(x_53);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
case 1:
{
lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_72 = x_57;
} else {
 lean_dec_ref(x_57);
 x_72 = lean_box(0);
}
x_73 = x_2 >> x_50;
x_74 = x_3 + x_49;
x_75 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignDelayed___spec__2(x_71, x_73, x_74, x_4, x_5);
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_array_fset(x_59, x_53, x_76);
lean_dec(x_53);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
default: 
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_4);
lean_ctor_set(x_79, 1, x_5);
x_80 = lean_array_fset(x_59, x_53, x_79);
lean_dec(x_53);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; size_t x_84; uint8_t x_85; 
x_82 = lean_unsigned_to_nat(0u);
x_83 = l_PersistentHashMap_insertAtCollisionNodeAux___main___at_Lean_MetavarContext_assignDelayed___spec__3(x_1, x_82, x_4, x_5);
x_84 = 7;
x_85 = x_84 <= x_3;
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = l_PersistentHashMap_getCollisionNodeSize___rarg(x_83);
x_87 = lean_unsigned_to_nat(4u);
x_88 = lean_nat_dec_lt(x_86, x_87);
lean_dec(x_86);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_83, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_83, 1);
lean_inc(x_90);
lean_dec(x_83);
x_91 = l_PersistentHashMap_insertAux___main___rarg___closed__3;
x_92 = l_Array_iterateMAux___main___at_Lean_MetavarContext_assignDelayed___spec__4(x_3, x_89, x_90, x_89, x_82, x_91);
lean_dec(x_90);
lean_dec(x_89);
return x_92;
}
else
{
return x_83;
}
}
else
{
return x_83;
}
}
}
}
lean_object* l_PersistentHashMap_insert___at_Lean_MetavarContext_assignDelayed___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Name_hash(x_2);
x_8 = 1;
x_9 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignDelayed___spec__2(x_5, x_7, x_8, x_2, x_3);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_6, x_10);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = l_Lean_Name_hash(x_2);
x_15 = 1;
x_16 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignDelayed___spec__2(x_12, x_14, x_15, x_2, x_3);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_13, x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
lean_object* lean_metavar_ctx_assign_delayed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 5);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_5);
x_9 = l_PersistentHashMap_insert___at_Lean_MetavarContext_assignDelayed___spec__1(x_7, x_2, x_8);
lean_ctor_set(x_1, 5, x_9);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_ctor_get(x_1, 3);
x_14 = lean_ctor_get(x_1, 4);
x_15 = lean_ctor_get(x_1, 5);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_4);
lean_ctor_set(x_16, 2, x_5);
x_17 = l_PersistentHashMap_insert___at_Lean_MetavarContext_assignDelayed___spec__1(x_15, x_2, x_16);
x_18 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_11);
lean_ctor_set(x_18, 2, x_12);
lean_ctor_set(x_18, 3, x_13);
lean_ctor_set(x_18, 4, x_14);
lean_ctor_set(x_18, 5, x_17);
return x_18;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_MetavarContext_assignDelayed___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Array_iterateMAux___main___at_Lean_MetavarContext_assignDelayed___spec__4(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignDelayed___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_PersistentHashMap_insertAux___main___at_Lean_MetavarContext_assignDelayed___spec__2(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getLevelAssignment___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_name_eq(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
lean_object* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getLevelAssignment___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
lean_object* x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = x_2 >> x_5;
x_18 = l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getLevelAssignment___spec__2(x_16, x_17, x_3);
lean_dec(x_16);
return x_18;
}
default: 
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getLevelAssignment___spec__3(x_20, x_21, lean_box(0), x_22, x_3);
return x_23;
}
}
}
lean_object* l_PersistentHashMap_find___at_Lean_MetavarContext_getLevelAssignment___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getLevelAssignment___spec__2(x_3, x_4, x_2);
return x_5;
}
}
lean_object* lean_metavar_ctx_get_level_assignment(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_PersistentHashMap_find___at_Lean_MetavarContext_getLevelAssignment___spec__1(x_3, x_2);
lean_dec(x_2);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getLevelAssignment___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getLevelAssignment___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getLevelAssignment___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getLevelAssignment___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_PersistentHashMap_find___at_Lean_MetavarContext_getLevelAssignment___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentHashMap_find___at_Lean_MetavarContext_getLevelAssignment___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getExprAssignment___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_name_eq(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
lean_object* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getExprAssignment___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
lean_object* x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = x_2 >> x_5;
x_18 = l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getExprAssignment___spec__2(x_16, x_17, x_3);
lean_dec(x_16);
return x_18;
}
default: 
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getExprAssignment___spec__3(x_20, x_21, lean_box(0), x_22, x_3);
return x_23;
}
}
}
lean_object* l_PersistentHashMap_find___at_Lean_MetavarContext_getExprAssignment___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getExprAssignment___spec__2(x_3, x_4, x_2);
return x_5;
}
}
lean_object* lean_metavar_ctx_get_expr_assignment(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 4);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_PersistentHashMap_find___at_Lean_MetavarContext_getExprAssignment___spec__1(x_3, x_2);
lean_dec(x_2);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getExprAssignment___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getExprAssignment___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getExprAssignment___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getExprAssignment___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_PersistentHashMap_find___at_Lean_MetavarContext_getExprAssignment___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentHashMap_find___at_Lean_MetavarContext_getExprAssignment___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getDelayedAssignment___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_name_eq(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
lean_object* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getDelayedAssignment___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
lean_object* x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = x_2 >> x_5;
x_18 = l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getDelayedAssignment___spec__2(x_16, x_17, x_3);
lean_dec(x_16);
return x_18;
}
default: 
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getDelayedAssignment___spec__3(x_20, x_21, lean_box(0), x_22, x_3);
return x_23;
}
}
}
lean_object* l_PersistentHashMap_find___at_Lean_MetavarContext_getDelayedAssignment___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getDelayedAssignment___spec__2(x_3, x_4, x_2);
return x_5;
}
}
lean_object* lean_metavar_ctx_get_delayed_assignment(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 5);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_PersistentHashMap_find___at_Lean_MetavarContext_getDelayedAssignment___spec__1(x_3, x_2);
lean_dec(x_2);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getDelayedAssignment___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_findAtAux___main___at_Lean_MetavarContext_getDelayedAssignment___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getDelayedAssignment___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_findAux___main___at_Lean_MetavarContext_getDelayedAssignment___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_PersistentHashMap_find___at_Lean_MetavarContext_getDelayedAssignment___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentHashMap_find___at_Lean_MetavarContext_getDelayedAssignment___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
uint8_t l_PersistentHashMap_containsAtAux___main___at_Lean_MetavarContext_isLevelAssigned___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_2);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_1, x_2);
x_8 = lean_name_eq(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_2, x_9);
lean_dec(x_2);
x_2 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_2);
x_12 = 1;
return x_12;
}
}
}
}
uint8_t l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isLevelAssigned___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = x_2 >> x_5;
x_15 = l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isLevelAssigned___spec__2(x_13, x_14, x_3);
lean_dec(x_13);
return x_15;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_PersistentHashMap_containsAtAux___main___at_Lean_MetavarContext_isLevelAssigned___spec__3(x_17, x_18, x_3);
return x_19;
}
}
}
uint8_t l_PersistentHashMap_contains___at_Lean_MetavarContext_isLevelAssigned___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isLevelAssigned___spec__2(x_3, x_4, x_2);
return x_5;
}
}
uint8_t lean_metavar_ctx_is_level_assigned(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_PersistentHashMap_contains___at_Lean_MetavarContext_isLevelAssigned___spec__1(x_3, x_2);
lean_dec(x_2);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_PersistentHashMap_containsAtAux___main___at_Lean_MetavarContext_isLevelAssigned___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_PersistentHashMap_containsAtAux___main___at_Lean_MetavarContext_isLevelAssigned___spec__3(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isLevelAssigned___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isLevelAssigned___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_PersistentHashMap_contains___at_Lean_MetavarContext_isLevelAssigned___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_PersistentHashMap_contains___at_Lean_MetavarContext_isLevelAssigned___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_MetavarContext_isLevelAssigned___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_metavar_ctx_is_level_assigned(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isExprAssigned___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = x_2 >> x_5;
x_15 = l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isExprAssigned___spec__2(x_13, x_14, x_3);
lean_dec(x_13);
return x_15;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_PersistentHashMap_containsAtAux___main___at_Lean_MetavarContext_isLevelAssigned___spec__3(x_17, x_18, x_3);
return x_19;
}
}
}
uint8_t l_PersistentHashMap_contains___at_Lean_MetavarContext_isExprAssigned___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isExprAssigned___spec__2(x_3, x_4, x_2);
return x_5;
}
}
uint8_t lean_metavar_ctx_is_expr_assigned(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 4);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_PersistentHashMap_contains___at_Lean_MetavarContext_isExprAssigned___spec__1(x_3, x_2);
lean_dec(x_2);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isExprAssigned___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isExprAssigned___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_PersistentHashMap_contains___at_Lean_MetavarContext_isExprAssigned___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_PersistentHashMap_contains___at_Lean_MetavarContext_isExprAssigned___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_MetavarContext_isExprAssigned___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_metavar_ctx_is_expr_assigned(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isDelayedAssigned___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = x_2 >> x_5;
x_15 = l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isDelayedAssigned___spec__2(x_13, x_14, x_3);
lean_dec(x_13);
return x_15;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_PersistentHashMap_containsAtAux___main___at_Lean_MetavarContext_isLevelAssigned___spec__3(x_17, x_18, x_3);
return x_19;
}
}
}
uint8_t l_PersistentHashMap_contains___at_Lean_MetavarContext_isDelayedAssigned___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isDelayedAssigned___spec__2(x_3, x_4, x_2);
return x_5;
}
}
uint8_t lean_metavar_ctx_is_delayed_assigned(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 5);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_PersistentHashMap_contains___at_Lean_MetavarContext_isDelayedAssigned___spec__1(x_3, x_2);
lean_dec(x_2);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isDelayedAssigned___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_containsAux___main___at_Lean_MetavarContext_isDelayedAssigned___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_PersistentHashMap_contains___at_Lean_MetavarContext_isDelayedAssigned___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_PersistentHashMap_contains___at_Lean_MetavarContext_isDelayedAssigned___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_MetavarContext_isDelayedAssigned___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_metavar_ctx_is_delayed_assigned(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_indexOfAux___main___at_Lean_MetavarContext_eraseDelayed___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_1, x_3);
x_8 = lean_name_eq(x_7, x_2);
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
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_3);
return x_12;
}
}
}
}
lean_object* l_PersistentHashMap_eraseAux___main___at_Lean_MetavarContext_eraseDelayed___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = 5;
x_6 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_4);
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_1, 0);
lean_dec(x_17);
x_18 = lean_array_set(x_4, x_8, x_9);
lean_dec(x_8);
lean_ctor_set(x_1, 0, x_18);
x_19 = 1;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_1);
x_22 = lean_array_set(x_4, x_8, x_9);
lean_dec(x_8);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = 1;
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
case 1:
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_10);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; size_t x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_ctor_get(x_10, 0);
x_29 = lean_array_set(x_4, x_8, x_9);
x_30 = x_2 >> x_5;
x_31 = l_PersistentHashMap_eraseAux___main___at_Lean_MetavarContext_eraseDelayed___spec__2(x_28, x_30, x_3);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
uint8_t x_34; 
lean_dec(x_29);
lean_free_object(x_10);
lean_dec(x_8);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_31, 1);
lean_dec(x_35);
x_36 = lean_ctor_get(x_31, 0);
lean_dec(x_36);
x_37 = 0;
x_38 = lean_box(x_37);
lean_ctor_set(x_31, 1, x_38);
lean_ctor_set(x_31, 0, x_1);
return x_31;
}
else
{
uint8_t x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_31);
x_39 = 0;
x_40 = lean_box(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_1);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_1, 0);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_31);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_31, 0);
x_46 = lean_ctor_get(x_31, 1);
lean_dec(x_46);
x_47 = l_PersistentHashMap_isUnaryNode___rarg(x_45);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; uint8_t x_49; lean_object* x_50; 
lean_ctor_set(x_10, 0, x_45);
x_48 = lean_array_set(x_29, x_8, x_10);
lean_dec(x_8);
lean_ctor_set(x_1, 0, x_48);
x_49 = 1;
x_50 = lean_box(x_49);
lean_ctor_set(x_31, 1, x_50);
lean_ctor_set(x_31, 0, x_1);
return x_31;
}
else
{
lean_object* x_51; uint8_t x_52; 
lean_free_object(x_31);
lean_dec(x_45);
lean_free_object(x_10);
x_51 = lean_ctor_get(x_47, 0);
lean_inc(x_51);
lean_dec(x_47);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_51, 1);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_array_set(x_29, x_8, x_55);
lean_dec(x_8);
lean_ctor_set(x_1, 0, x_56);
x_57 = 1;
x_58 = lean_box(x_57);
lean_ctor_set(x_51, 1, x_58);
lean_ctor_set(x_51, 0, x_1);
return x_51;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; 
x_59 = lean_ctor_get(x_51, 0);
x_60 = lean_ctor_get(x_51, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_51);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_array_set(x_29, x_8, x_61);
lean_dec(x_8);
lean_ctor_set(x_1, 0, x_62);
x_63 = 1;
x_64 = lean_box(x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_1);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_31, 0);
lean_inc(x_66);
lean_dec(x_31);
x_67 = l_PersistentHashMap_isUnaryNode___rarg(x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; 
lean_ctor_set(x_10, 0, x_66);
x_68 = lean_array_set(x_29, x_8, x_10);
lean_dec(x_8);
lean_ctor_set(x_1, 0, x_68);
x_69 = 1;
x_70 = lean_box(x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_1);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_66);
lean_free_object(x_10);
x_72 = lean_ctor_get(x_67, 0);
lean_inc(x_72);
lean_dec(x_67);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_75 = x_72;
} else {
 lean_dec_ref(x_72);
 x_75 = lean_box(0);
}
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
x_77 = lean_array_set(x_29, x_8, x_76);
lean_dec(x_8);
lean_ctor_set(x_1, 0, x_77);
x_78 = 1;
x_79 = lean_box(x_78);
if (lean_is_scalar(x_75)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_75;
}
lean_ctor_set(x_80, 0, x_1);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_1);
x_81 = lean_ctor_get(x_31, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_82 = x_31;
} else {
 lean_dec_ref(x_31);
 x_82 = lean_box(0);
}
x_83 = l_PersistentHashMap_isUnaryNode___rarg(x_81);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; 
lean_ctor_set(x_10, 0, x_81);
x_84 = lean_array_set(x_29, x_8, x_10);
lean_dec(x_8);
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = 1;
x_87 = lean_box(x_86);
if (lean_is_scalar(x_82)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_82;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_82);
lean_dec(x_81);
lean_free_object(x_10);
x_89 = lean_ctor_get(x_83, 0);
lean_inc(x_89);
lean_dec(x_83);
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
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
x_94 = lean_array_set(x_29, x_8, x_93);
lean_dec(x_8);
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_96 = 1;
x_97 = lean_box(x_96);
if (lean_is_scalar(x_92)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_92;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
else
{
lean_object* x_99; lean_object* x_100; size_t x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_99 = lean_ctor_get(x_10, 0);
lean_inc(x_99);
lean_dec(x_10);
x_100 = lean_array_set(x_4, x_8, x_9);
x_101 = x_2 >> x_5;
x_102 = l_PersistentHashMap_eraseAux___main___at_Lean_MetavarContext_eraseDelayed___spec__2(x_99, x_101, x_3);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
x_104 = lean_unbox(x_103);
lean_dec(x_103);
if (x_104 == 0)
{
lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_100);
lean_dec(x_8);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_105 = x_102;
} else {
 lean_dec_ref(x_102);
 x_105 = lean_box(0);
}
x_106 = 0;
x_107 = lean_box(x_106);
if (lean_is_scalar(x_105)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_105;
}
lean_ctor_set(x_108, 0, x_1);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_109 = x_1;
} else {
 lean_dec_ref(x_1);
 x_109 = lean_box(0);
}
x_110 = lean_ctor_get(x_102, 0);
lean_inc(x_110);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_111 = x_102;
} else {
 lean_dec_ref(x_102);
 x_111 = lean_box(0);
}
x_112 = l_PersistentHashMap_isUnaryNode___rarg(x_110);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; 
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_110);
x_114 = lean_array_set(x_100, x_8, x_113);
lean_dec(x_8);
if (lean_is_scalar(x_109)) {
 x_115 = lean_alloc_ctor(0, 1, 0);
} else {
 x_115 = x_109;
}
lean_ctor_set(x_115, 0, x_114);
x_116 = 1;
x_117 = lean_box(x_116);
if (lean_is_scalar(x_111)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_111;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_111);
lean_dec(x_110);
x_119 = lean_ctor_get(x_112, 0);
lean_inc(x_119);
lean_dec(x_112);
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
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
x_124 = lean_array_set(x_100, x_8, x_123);
lean_dec(x_8);
if (lean_is_scalar(x_109)) {
 x_125 = lean_alloc_ctor(0, 1, 0);
} else {
 x_125 = x_109;
}
lean_ctor_set(x_125, 0, x_124);
x_126 = 1;
x_127 = lean_box(x_126);
if (lean_is_scalar(x_122)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_122;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
}
default: 
{
uint8_t x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_8);
lean_dec(x_4);
x_129 = 0;
x_130 = lean_box(x_129);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_1);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_132 = lean_ctor_get(x_1, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_1, 1);
lean_inc(x_133);
x_134 = lean_unsigned_to_nat(0u);
x_135 = l_Array_indexOfAux___main___at_Lean_MetavarContext_eraseDelayed___spec__3(x_132, x_3, x_134);
if (lean_obj_tag(x_135) == 0)
{
uint8_t x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_133);
lean_dec(x_132);
x_136 = 0;
x_137 = lean_box(x_136);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_1);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
else
{
uint8_t x_139; 
x_139 = !lean_is_exclusive(x_1);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; 
x_140 = lean_ctor_get(x_1, 1);
lean_dec(x_140);
x_141 = lean_ctor_get(x_1, 0);
lean_dec(x_141);
x_142 = lean_ctor_get(x_135, 0);
lean_inc(x_142);
lean_dec(x_135);
x_143 = l_Array_eraseIdx_x27___rarg(x_132, x_142);
x_144 = l_Array_eraseIdx_x27___rarg(x_133, x_142);
lean_dec(x_142);
lean_ctor_set(x_1, 1, x_144);
lean_ctor_set(x_1, 0, x_143);
x_145 = 1;
x_146 = lean_box(x_145);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_1);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_1);
x_148 = lean_ctor_get(x_135, 0);
lean_inc(x_148);
lean_dec(x_135);
x_149 = l_Array_eraseIdx_x27___rarg(x_132, x_148);
x_150 = l_Array_eraseIdx_x27___rarg(x_133, x_148);
lean_dec(x_148);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
x_152 = 1;
x_153 = lean_box(x_152);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_151);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
}
}
lean_object* l_PersistentHashMap_erase___at_Lean_MetavarContext_eraseDelayed___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_Name_hash(x_2);
x_7 = l_PersistentHashMap_eraseAux___main___at_Lean_MetavarContext_eraseDelayed___spec__2(x_4, x_6, x_2);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_5, x_12);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_11);
return x_1;
}
}
else
{
lean_object* x_14; lean_object* x_15; size_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_16 = l_Lean_Name_hash(x_2);
x_17 = l_PersistentHashMap_eraseAux___main___at_Lean_MetavarContext_eraseDelayed___spec__2(x_14, x_16, x_2);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_15);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_sub(x_15, x_23);
lean_dec(x_15);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
lean_object* lean_metavar_ctx_erase_delayed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 5);
x_5 = l_PersistentHashMap_erase___at_Lean_MetavarContext_eraseDelayed___spec__1(x_4, x_2);
lean_dec(x_2);
lean_ctor_set(x_1, 5, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
x_10 = lean_ctor_get(x_1, 4);
x_11 = lean_ctor_get(x_1, 5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_12 = l_PersistentHashMap_erase___at_Lean_MetavarContext_eraseDelayed___spec__1(x_11, x_2);
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_7);
lean_ctor_set(x_13, 2, x_8);
lean_ctor_set(x_13, 3, x_9);
lean_ctor_set(x_13, 4, x_10);
lean_ctor_set(x_13, 5, x_12);
return x_13;
}
}
}
lean_object* l_Array_indexOfAux___main___at_Lean_MetavarContext_eraseDelayed___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_indexOfAux___main___at_Lean_MetavarContext_eraseDelayed___spec__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_PersistentHashMap_eraseAux___main___at_Lean_MetavarContext_eraseDelayed___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_eraseAux___main___at_Lean_MetavarContext_eraseDelayed___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_PersistentHashMap_erase___at_Lean_MetavarContext_eraseDelayed___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentHashMap_erase___at_Lean_MetavarContext_eraseDelayed___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_MetavarContext_isLevelAssignable___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown universe metavariable");
return x_1;
}
}
lean_object* _init_l_Lean_MetavarContext_isLevelAssignable___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_MetavarContext_getDecl___closed__1;
x_2 = lean_unsigned_to_nat(330u);
x_3 = lean_unsigned_to_nat(12u);
x_4 = l_Lean_MetavarContext_isLevelAssignable___closed__1;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
uint8_t l_Lean_MetavarContext_isLevelAssignable(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_PersistentHashMap_find___at_Lean_MetavarContext_findLevelDepth___spec__1(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = l_Bool_Inhabited;
x_6 = l_Lean_MetavarContext_isLevelAssignable___closed__2;
x_7 = lean_box(x_5);
x_8 = lean_panic_fn(x_6);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_nat_dec_eq(x_10, x_11);
lean_dec(x_10);
return x_12;
}
}
}
lean_object* l_Lean_MetavarContext_isLevelAssignable___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_MetavarContext_isLevelAssignable(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_MetavarContext_isExprAssignable(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = l_Lean_MetavarContext_getDecl(x_1, x_2);
x_4 = lean_ctor_get(x_3, 3);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_nat_dec_eq(x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_MetavarContext_isExprAssignable___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_MetavarContext_isExprAssignable(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_MetavarContext_incDepth(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_3);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
x_10 = lean_ctor_get(x_1, 4);
x_11 = lean_ctor_get(x_1, 5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_6, x_12);
lean_dec(x_6);
x_14 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_7);
lean_ctor_set(x_14, 2, x_8);
lean_ctor_set(x_14, 3, x_9);
lean_ctor_set(x_14, 4, x_10);
lean_ctor_set(x_14, 5, x_11);
return x_14;
}
}
}
uint8_t l_Lean_MetavarContext_hasAssignedLevelMVar___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lean_Level_hasMVar(x_3);
if (x_4 == 0)
{
uint8_t x_5; 
lean_dec(x_3);
lean_dec(x_1);
x_5 = 0;
return x_5;
}
else
{
x_2 = x_3;
goto _start;
}
}
case 2:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lean_Level_hasMVar(x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
x_10 = l_Lean_Level_hasMVar(x_8);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_8);
lean_dec(x_1);
x_11 = 0;
return x_11;
}
else
{
x_2 = x_8;
goto _start;
}
}
else
{
uint8_t x_13; 
lean_inc(x_1);
x_13 = l_Lean_MetavarContext_hasAssignedLevelMVar___main(x_1, x_7);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Level_hasMVar(x_8);
if (x_14 == 0)
{
lean_dec(x_8);
lean_dec(x_1);
return x_13;
}
else
{
x_2 = x_8;
goto _start;
}
}
else
{
uint8_t x_16; 
lean_dec(x_8);
lean_dec(x_1);
x_16 = 1;
return x_16;
}
}
}
case 3:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_dec(x_2);
x_19 = l_Lean_Level_hasMVar(x_17);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_17);
x_20 = l_Lean_Level_hasMVar(x_18);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_18);
lean_dec(x_1);
x_21 = 0;
return x_21;
}
else
{
x_2 = x_18;
goto _start;
}
}
else
{
uint8_t x_23; 
lean_inc(x_1);
x_23 = l_Lean_MetavarContext_hasAssignedLevelMVar___main(x_1, x_17);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_Lean_Level_hasMVar(x_18);
if (x_24 == 0)
{
lean_dec(x_18);
lean_dec(x_1);
return x_23;
}
else
{
x_2 = x_18;
goto _start;
}
}
else
{
uint8_t x_26; 
lean_dec(x_18);
lean_dec(x_1);
x_26 = 1;
return x_26;
}
}
}
case 5:
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_2, 0);
lean_inc(x_27);
lean_dec(x_2);
x_28 = lean_metavar_ctx_is_level_assigned(x_1, x_27);
return x_28;
}
default: 
{
uint8_t x_29; 
lean_dec(x_2);
lean_dec(x_1);
x_29 = 0;
return x_29;
}
}
}
}
lean_object* l_Lean_MetavarContext_hasAssignedLevelMVar___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_MetavarContext_hasAssignedLevelMVar___main(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_MetavarContext_hasAssignedLevelMVar(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_MetavarContext_hasAssignedLevelMVar___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_MetavarContext_hasAssignedLevelMVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_MetavarContext_hasAssignedLevelMVar(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_List_foldr___main___at_Lean_MetavarContext_hasAssignedMVar___main___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_1);
x_6 = l_List_foldr___main___at_Lean_MetavarContext_hasAssignedMVar___main___spec__1(x_1, x_2, x_5);
x_7 = l_Lean_MetavarContext_hasAssignedLevelMVar___main(x_1, x_4);
if (x_7 == 0)
{
return x_6;
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
lean_object* l_Lean_MetavarContext_hasAssignedMVar___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_metavar_ctx_is_expr_assigned(x_1, x_3);
x_5 = lean_box(x_4);
return x_5;
}
case 3:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lean_MetavarContext_hasAssignedLevelMVar___main(x_1, x_6);
x_8 = lean_box(x_7);
return x_8;
}
case 4:
{
lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = 0;
x_11 = l_List_foldr___main___at_Lean_MetavarContext_hasAssignedMVar___main___spec__1(x_1, x_10, x_9);
x_12 = lean_box(x_11);
return x_12;
}
case 5:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_Lean_Expr_hasMVar(x_13);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_13);
x_16 = l_Lean_Expr_hasMVar(x_14);
if (x_16 == 0)
{
uint8_t x_17; lean_object* x_18; 
lean_dec(x_14);
lean_dec(x_1);
x_17 = 0;
x_18 = lean_box(x_17);
return x_18;
}
else
{
x_2 = x_14;
goto _start;
}
}
else
{
lean_object* x_20; uint8_t x_21; 
lean_inc(x_1);
x_20 = l_Lean_MetavarContext_hasAssignedMVar___main(x_1, x_13);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Expr_hasMVar(x_14);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_14);
lean_dec(x_1);
x_23 = lean_box(x_21);
return x_23;
}
else
{
x_2 = x_14;
goto _start;
}
}
else
{
uint8_t x_25; lean_object* x_26; 
lean_dec(x_14);
lean_dec(x_1);
x_25 = 1;
x_26 = lean_box(x_25);
return x_26;
}
}
}
case 6:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_2, 2);
lean_inc(x_28);
lean_dec(x_2);
x_29 = l_Lean_Expr_hasMVar(x_27);
if (x_29 == 0)
{
uint8_t x_30; 
lean_dec(x_27);
x_30 = l_Lean_Expr_hasMVar(x_28);
if (x_30 == 0)
{
uint8_t x_31; lean_object* x_32; 
lean_dec(x_28);
lean_dec(x_1);
x_31 = 0;
x_32 = lean_box(x_31);
return x_32;
}
else
{
x_2 = x_28;
goto _start;
}
}
else
{
lean_object* x_34; uint8_t x_35; 
lean_inc(x_1);
x_34 = l_Lean_MetavarContext_hasAssignedMVar___main(x_1, x_27);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = l_Lean_Expr_hasMVar(x_28);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_28);
lean_dec(x_1);
x_37 = lean_box(x_35);
return x_37;
}
else
{
x_2 = x_28;
goto _start;
}
}
else
{
uint8_t x_39; lean_object* x_40; 
lean_dec(x_28);
lean_dec(x_1);
x_39 = 1;
x_40 = lean_box(x_39);
return x_40;
}
}
}
case 7:
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_2, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_2, 2);
lean_inc(x_42);
lean_dec(x_2);
x_43 = l_Lean_Expr_hasMVar(x_41);
if (x_43 == 0)
{
uint8_t x_44; 
lean_dec(x_41);
x_44 = l_Lean_Expr_hasMVar(x_42);
if (x_44 == 0)
{
uint8_t x_45; lean_object* x_46; 
lean_dec(x_42);
lean_dec(x_1);
x_45 = 0;
x_46 = lean_box(x_45);
return x_46;
}
else
{
x_2 = x_42;
goto _start;
}
}
else
{
lean_object* x_48; uint8_t x_49; 
lean_inc(x_1);
x_48 = l_Lean_MetavarContext_hasAssignedMVar___main(x_1, x_41);
x_49 = lean_unbox(x_48);
lean_dec(x_48);
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = l_Lean_Expr_hasMVar(x_42);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_42);
lean_dec(x_1);
x_51 = lean_box(x_49);
return x_51;
}
else
{
x_2 = x_42;
goto _start;
}
}
else
{
uint8_t x_53; lean_object* x_54; 
lean_dec(x_42);
lean_dec(x_1);
x_53 = 1;
x_54 = lean_box(x_53);
return x_54;
}
}
}
case 8:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_2, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_2, 2);
lean_inc(x_56);
x_57 = lean_ctor_get(x_2, 3);
lean_inc(x_57);
lean_dec(x_2);
x_58 = l_Lean_Expr_hasMVar(x_55);
if (x_58 == 0)
{
uint8_t x_59; 
lean_dec(x_55);
x_59 = l_Lean_Expr_hasMVar(x_56);
if (x_59 == 0)
{
uint8_t x_60; 
lean_dec(x_56);
x_60 = l_Lean_Expr_hasMVar(x_57);
if (x_60 == 0)
{
uint8_t x_61; lean_object* x_62; 
lean_dec(x_57);
lean_dec(x_1);
x_61 = 0;
x_62 = lean_box(x_61);
return x_62;
}
else
{
x_2 = x_57;
goto _start;
}
}
else
{
lean_object* x_64; uint8_t x_65; 
lean_inc(x_1);
x_64 = l_Lean_MetavarContext_hasAssignedMVar___main(x_1, x_56);
x_65 = lean_unbox(x_64);
lean_dec(x_64);
if (x_65 == 0)
{
uint8_t x_66; 
x_66 = l_Lean_Expr_hasMVar(x_57);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec(x_57);
lean_dec(x_1);
x_67 = lean_box(x_65);
return x_67;
}
else
{
x_2 = x_57;
goto _start;
}
}
else
{
uint8_t x_69; lean_object* x_70; 
lean_dec(x_57);
lean_dec(x_1);
x_69 = 1;
x_70 = lean_box(x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; uint8_t x_72; 
lean_inc(x_1);
x_71 = l_Lean_MetavarContext_hasAssignedMVar___main(x_1, x_55);
x_72 = lean_unbox(x_71);
lean_dec(x_71);
if (x_72 == 0)
{
uint8_t x_73; 
x_73 = l_Lean_Expr_hasMVar(x_56);
if (x_73 == 0)
{
uint8_t x_74; 
lean_dec(x_56);
x_74 = l_Lean_Expr_hasMVar(x_57);
if (x_74 == 0)
{
lean_object* x_75; 
lean_dec(x_57);
lean_dec(x_1);
x_75 = lean_box(x_72);
return x_75;
}
else
{
x_2 = x_57;
goto _start;
}
}
else
{
lean_object* x_77; uint8_t x_78; 
lean_inc(x_1);
x_77 = l_Lean_MetavarContext_hasAssignedMVar___main(x_1, x_56);
x_78 = lean_unbox(x_77);
lean_dec(x_77);
if (x_78 == 0)
{
uint8_t x_79; 
x_79 = l_Lean_Expr_hasMVar(x_57);
if (x_79 == 0)
{
lean_object* x_80; 
lean_dec(x_57);
lean_dec(x_1);
x_80 = lean_box(x_78);
return x_80;
}
else
{
x_2 = x_57;
goto _start;
}
}
else
{
uint8_t x_82; lean_object* x_83; 
lean_dec(x_57);
lean_dec(x_1);
x_82 = 1;
x_83 = lean_box(x_82);
return x_83;
}
}
}
else
{
uint8_t x_84; lean_object* x_85; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_1);
x_84 = 1;
x_85 = lean_box(x_84);
return x_85;
}
}
}
case 10:
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_ctor_get(x_2, 1);
lean_inc(x_86);
lean_dec(x_2);
x_87 = l_Lean_Expr_hasMVar(x_86);
if (x_87 == 0)
{
uint8_t x_88; lean_object* x_89; 
lean_dec(x_86);
lean_dec(x_1);
x_88 = 0;
x_89 = lean_box(x_88);
return x_89;
}
else
{
x_2 = x_86;
goto _start;
}
}
case 11:
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_2, 2);
lean_inc(x_91);
lean_dec(x_2);
x_92 = l_Lean_Expr_hasMVar(x_91);
if (x_92 == 0)
{
uint8_t x_93; lean_object* x_94; 
lean_dec(x_91);
lean_dec(x_1);
x_93 = 0;
x_94 = lean_box(x_93);
return x_94;
}
else
{
x_2 = x_91;
goto _start;
}
}
case 12:
{
uint8_t x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_2);
lean_dec(x_1);
x_96 = l_Bool_Inhabited;
x_97 = lean_box(x_96);
x_98 = l_unreachable_x21___rarg(x_97);
return x_98;
}
default: 
{
uint8_t x_99; lean_object* x_100; 
lean_dec(x_2);
lean_dec(x_1);
x_99 = 0;
x_100 = lean_box(x_99);
return x_100;
}
}
}
}
lean_object* l_List_foldr___main___at_Lean_MetavarContext_hasAssignedMVar___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_List_foldr___main___at_Lean_MetavarContext_hasAssignedMVar___main___spec__1(x_1, x_4, x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Lean_MetavarContext_hasAssignedMVar(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MetavarContext_hasAssignedMVar___main(x_1, x_2);
return x_3;
}
}
uint8_t l_Lean_MetavarContext_hasAssignableLevelMVar___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Lean_Level_hasMVar(x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
x_2 = x_3;
goto _start;
}
}
case 2:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = l_Lean_Level_hasMVar(x_7);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Lean_Level_hasMVar(x_8);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
else
{
x_2 = x_8;
goto _start;
}
}
else
{
uint8_t x_13; 
x_13 = l_Lean_MetavarContext_hasAssignableLevelMVar___main(x_1, x_7);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Level_hasMVar(x_8);
if (x_14 == 0)
{
return x_13;
}
else
{
x_2 = x_8;
goto _start;
}
}
else
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
}
}
case 3:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
x_19 = l_Lean_Level_hasMVar(x_17);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = l_Lean_Level_hasMVar(x_18);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = 0;
return x_21;
}
else
{
x_2 = x_18;
goto _start;
}
}
else
{
uint8_t x_23; 
x_23 = l_Lean_MetavarContext_hasAssignableLevelMVar___main(x_1, x_17);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_Lean_Level_hasMVar(x_18);
if (x_24 == 0)
{
return x_23;
}
else
{
x_2 = x_18;
goto _start;
}
}
else
{
uint8_t x_26; 
x_26 = 1;
return x_26;
}
}
}
case 5:
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_2, 0);
x_28 = l_Lean_MetavarContext_isLevelAssignable(x_1, x_27);
return x_28;
}
default: 
{
uint8_t x_29; 
x_29 = 0;
return x_29;
}
}
}
}
lean_object* l_Lean_MetavarContext_hasAssignableLevelMVar___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_MetavarContext_hasAssignableLevelMVar___main(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_MetavarContext_hasAssignableLevelMVar(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_MetavarContext_hasAssignableLevelMVar___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_MetavarContext_hasAssignableLevelMVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_MetavarContext_hasAssignableLevelMVar(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_List_foldr___main___at_Lean_MetavarContext_hasAssignableMVar___main___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_List_foldr___main___at_Lean_MetavarContext_hasAssignableMVar___main___spec__1(x_1, x_2, x_5);
x_7 = l_Lean_MetavarContext_hasAssignableLevelMVar___main(x_1, x_4);
if (x_7 == 0)
{
return x_6;
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
lean_object* l_Lean_MetavarContext_hasAssignableMVar___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Lean_MetavarContext_isExprAssignable(x_1, x_3);
x_5 = lean_box(x_4);
return x_5;
}
case 3:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = l_Lean_MetavarContext_hasAssignableLevelMVar___main(x_1, x_6);
x_8 = lean_box(x_7);
return x_8;
}
case 4:
{
lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_2, 1);
x_10 = 0;
x_11 = l_List_foldr___main___at_Lean_MetavarContext_hasAssignableMVar___main___spec__1(x_1, x_10, x_9);
x_12 = lean_box(x_11);
return x_12;
}
case 5:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = l_Lean_Expr_hasMVar(x_13);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = l_Lean_Expr_hasMVar(x_14);
if (x_16 == 0)
{
uint8_t x_17; lean_object* x_18; 
x_17 = 0;
x_18 = lean_box(x_17);
return x_18;
}
else
{
x_2 = x_14;
goto _start;
}
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_MetavarContext_hasAssignableMVar___main(x_1, x_13);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Expr_hasMVar(x_14);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_box(x_21);
return x_23;
}
else
{
x_2 = x_14;
goto _start;
}
}
else
{
uint8_t x_25; lean_object* x_26; 
x_25 = 1;
x_26 = lean_box(x_25);
return x_26;
}
}
}
case 6:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_2, 1);
x_28 = lean_ctor_get(x_2, 2);
x_29 = l_Lean_Expr_hasMVar(x_27);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = l_Lean_Expr_hasMVar(x_28);
if (x_30 == 0)
{
uint8_t x_31; lean_object* x_32; 
x_31 = 0;
x_32 = lean_box(x_31);
return x_32;
}
else
{
x_2 = x_28;
goto _start;
}
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = l_Lean_MetavarContext_hasAssignableMVar___main(x_1, x_27);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = l_Lean_Expr_hasMVar(x_28);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_box(x_35);
return x_37;
}
else
{
x_2 = x_28;
goto _start;
}
}
else
{
uint8_t x_39; lean_object* x_40; 
x_39 = 1;
x_40 = lean_box(x_39);
return x_40;
}
}
}
case 7:
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_2, 1);
x_42 = lean_ctor_get(x_2, 2);
x_43 = l_Lean_Expr_hasMVar(x_41);
if (x_43 == 0)
{
uint8_t x_44; 
x_44 = l_Lean_Expr_hasMVar(x_42);
if (x_44 == 0)
{
uint8_t x_45; lean_object* x_46; 
x_45 = 0;
x_46 = lean_box(x_45);
return x_46;
}
else
{
x_2 = x_42;
goto _start;
}
}
else
{
lean_object* x_48; uint8_t x_49; 
x_48 = l_Lean_MetavarContext_hasAssignableMVar___main(x_1, x_41);
x_49 = lean_unbox(x_48);
lean_dec(x_48);
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = l_Lean_Expr_hasMVar(x_42);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_box(x_49);
return x_51;
}
else
{
x_2 = x_42;
goto _start;
}
}
else
{
uint8_t x_53; lean_object* x_54; 
x_53 = 1;
x_54 = lean_box(x_53);
return x_54;
}
}
}
case 8:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_2, 1);
x_56 = lean_ctor_get(x_2, 2);
x_57 = lean_ctor_get(x_2, 3);
x_58 = l_Lean_Expr_hasMVar(x_55);
if (x_58 == 0)
{
uint8_t x_59; 
x_59 = l_Lean_Expr_hasMVar(x_56);
if (x_59 == 0)
{
uint8_t x_60; 
x_60 = l_Lean_Expr_hasMVar(x_57);
if (x_60 == 0)
{
uint8_t x_61; lean_object* x_62; 
x_61 = 0;
x_62 = lean_box(x_61);
return x_62;
}
else
{
x_2 = x_57;
goto _start;
}
}
else
{
lean_object* x_64; uint8_t x_65; 
x_64 = l_Lean_MetavarContext_hasAssignableMVar___main(x_1, x_56);
x_65 = lean_unbox(x_64);
lean_dec(x_64);
if (x_65 == 0)
{
uint8_t x_66; 
x_66 = l_Lean_Expr_hasMVar(x_57);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_box(x_65);
return x_67;
}
else
{
x_2 = x_57;
goto _start;
}
}
else
{
uint8_t x_69; lean_object* x_70; 
x_69 = 1;
x_70 = lean_box(x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; uint8_t x_72; 
x_71 = l_Lean_MetavarContext_hasAssignableMVar___main(x_1, x_55);
x_72 = lean_unbox(x_71);
lean_dec(x_71);
if (x_72 == 0)
{
uint8_t x_73; 
x_73 = l_Lean_Expr_hasMVar(x_56);
if (x_73 == 0)
{
uint8_t x_74; 
x_74 = l_Lean_Expr_hasMVar(x_57);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_box(x_72);
return x_75;
}
else
{
x_2 = x_57;
goto _start;
}
}
else
{
lean_object* x_77; uint8_t x_78; 
x_77 = l_Lean_MetavarContext_hasAssignableMVar___main(x_1, x_56);
x_78 = lean_unbox(x_77);
lean_dec(x_77);
if (x_78 == 0)
{
uint8_t x_79; 
x_79 = l_Lean_Expr_hasMVar(x_57);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = lean_box(x_78);
return x_80;
}
else
{
x_2 = x_57;
goto _start;
}
}
else
{
uint8_t x_82; lean_object* x_83; 
x_82 = 1;
x_83 = lean_box(x_82);
return x_83;
}
}
}
else
{
uint8_t x_84; lean_object* x_85; 
x_84 = 1;
x_85 = lean_box(x_84);
return x_85;
}
}
}
case 10:
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_ctor_get(x_2, 1);
x_87 = l_Lean_Expr_hasMVar(x_86);
if (x_87 == 0)
{
uint8_t x_88; lean_object* x_89; 
x_88 = 0;
x_89 = lean_box(x_88);
return x_89;
}
else
{
x_2 = x_86;
goto _start;
}
}
case 11:
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_2, 2);
x_92 = l_Lean_Expr_hasMVar(x_91);
if (x_92 == 0)
{
uint8_t x_93; lean_object* x_94; 
x_93 = 0;
x_94 = lean_box(x_93);
return x_94;
}
else
{
x_2 = x_91;
goto _start;
}
}
case 12:
{
uint8_t x_96; lean_object* x_97; lean_object* x_98; 
x_96 = l_Bool_Inhabited;
x_97 = lean_box(x_96);
x_98 = l_unreachable_x21___rarg(x_97);
return x_98;
}
default: 
{
uint8_t x_99; lean_object* x_100; 
x_99 = 0;
x_100 = lean_box(x_99);
return x_100;
}
}
}
}
lean_object* l_List_foldr___main___at_Lean_MetavarContext_hasAssignableMVar___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_List_foldr___main___at_Lean_MetavarContext_hasAssignableMVar___main___spec__1(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Lean_MetavarContext_hasAssignableMVar___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MetavarContext_hasAssignableMVar___main(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_MetavarContext_hasAssignableMVar(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MetavarContext_hasAssignableMVar___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_MetavarContext_hasAssignableMVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MetavarContext_hasAssignableMVar(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = l_Lean_MetavarContext_instantiateLevelMVars___main(x_3, x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_level_update_succ(x_1, x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = lean_level_update_succ(x_1, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
case 2:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = l_Lean_MetavarContext_instantiateLevelMVars___main(x_12, x_2);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_MetavarContext_instantiateLevelMVars___main(x_13, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_level_update_max(x_1, x_15, x_19);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_level_update_max(x_1, x_15, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
case 3:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_dec(x_1);
x_27 = l_Lean_MetavarContext_instantiateLevelMVars___main(x_25, x_2);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_Lean_MetavarContext_instantiateLevelMVars___main(x_26, x_28);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
x_32 = l_Lean_Level_Inhabited;
x_33 = l_Lean_Level_updateIMax_x21___closed__2;
x_34 = lean_panic_fn(x_33);
lean_ctor_set(x_29, 0, x_34);
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = l_Lean_Level_Inhabited;
x_37 = l_Lean_Level_updateIMax_x21___closed__2;
x_38 = lean_panic_fn(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
}
case 5:
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
lean_inc(x_40);
lean_inc(x_2);
x_41 = lean_metavar_ctx_get_level_assignment(x_2, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
lean_dec(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_2);
return x_42;
}
else
{
lean_object* x_43; uint8_t x_44; 
lean_dec(x_1);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Level_hasMVar(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_40);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_2);
return x_45;
}
else
{
lean_object* x_46; uint8_t x_47; 
x_46 = l_Lean_MetavarContext_instantiateLevelMVars___main(x_43, x_2);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
x_50 = lean_metavar_ctx_assign_level(x_49, x_40, x_48);
lean_ctor_set(x_46, 1, x_50);
return x_46;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_46, 0);
x_52 = lean_ctor_get(x_46, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_46);
lean_inc(x_51);
x_53 = lean_metavar_ctx_assign_level(x_52, x_40, x_51);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
default: 
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_2);
return x_55;
}
}
}
}
lean_object* l_Lean_MetavarContext_instantiateLevelMVars(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MetavarContext_instantiateLevelMVars___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_MetavarContext_InstantiateExprMVars_instantiateLevelMVars(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_MetavarContext_instantiateLevelMVars___main(x_1, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 1);
lean_ctor_set(x_2, 0, x_7);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_5);
lean_ctor_set(x_2, 0, x_9);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_2);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
x_13 = l_Lean_MetavarContext_instantiateLevelMVars___main(x_1, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_16 = x_13;
} else {
 lean_dec_ref(x_13);
 x_16 = lean_box(0);
}
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_12);
if (lean_is_scalar(x_16)) {
 x_18 = lean_alloc_ctor(0, 2, 0);
} else {
 x_18 = x_16;
}
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
lean_object* l_AssocList_find___main___at___private_Init_Lean_MetavarContext_2__visit___spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_find___main___at___private_Init_Lean_MetavarContext_2__visit___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
uint8_t l_AssocList_contains___main___at___private_Init_Lean_MetavarContext_2__visit___spec__4(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_AssocList_foldlM___main___at___private_Init_Lean_MetavarContext_2__visit___spec__7(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_Expr_hash(x_4);
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
x_16 = l_Lean_Expr_hash(x_12);
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
lean_object* l_HashMapImp_moveEntries___main___at___private_Init_Lean_MetavarContext_2__visit___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_AssocList_foldlM___main___at___private_Init_Lean_MetavarContext_2__visit___spec__7(x_3, x_6);
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
lean_object* l_HashMapImp_expand___at___private_Init_Lean_MetavarContext_2__visit___spec__5(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_HashMapImp_moveEntries___main___at___private_Init_Lean_MetavarContext_2__visit___spec__6(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at___private_Init_Lean_MetavarContext_2__visit___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_AssocList_replace___main___at___private_Init_Lean_MetavarContext_2__visit___spec__8(x_1, x_2, x_7);
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
x_14 = l_AssocList_replace___main___at___private_Init_Lean_MetavarContext_2__visit___spec__8(x_1, x_2, x_12);
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
lean_object* l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l_Lean_Expr_hash(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_AssocList_contains___main___at___private_Init_Lean_MetavarContext_2__visit___spec__4(x_2, x_10);
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
x_17 = l_HashMapImp_expand___at___private_Init_Lean_MetavarContext_2__visit___spec__5(x_13, x_15);
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
x_18 = l_AssocList_replace___main___at___private_Init_Lean_MetavarContext_2__visit___spec__8(x_2, x_3, x_10);
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
x_23 = l_Lean_Expr_hash(x_2);
x_24 = lean_usize_modn(x_23, x_22);
x_25 = lean_array_uget(x_21, x_24);
x_26 = l_AssocList_contains___main___at___private_Init_Lean_MetavarContext_2__visit___spec__4(x_2, x_25);
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
x_32 = l_HashMapImp_expand___at___private_Init_Lean_MetavarContext_2__visit___spec__5(x_28, x_30);
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
x_34 = l_AssocList_replace___main___at___private_Init_Lean_MetavarContext_2__visit___spec__8(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l___private_Init_Lean_MetavarContext_2__visit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_2);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_6, x_2);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
lean_inc(x_2);
x_8 = lean_apply_2(x_1, x_2, x_3);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 1);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_14 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_13, x_2, x_12);
lean_ctor_set(x_10, 1, x_14);
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
lean_inc(x_15);
x_18 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_17, x_2, x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_8, 1, x_19);
return x_8;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_8, 1);
x_21 = lean_ctor_get(x_8, 0);
lean_inc(x_20);
lean_inc(x_21);
lean_dec(x_8);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_24 = x_20;
} else {
 lean_dec_ref(x_20);
 x_24 = lean_box(0);
}
lean_inc(x_21);
x_25 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_23, x_2, x_21);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_ctor_get(x_7, 0);
lean_inc(x_28);
lean_dec(x_7);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_3);
return x_29;
}
}
}
}
lean_object* l_AssocList_find___main___at___private_Init_Lean_MetavarContext_2__visit___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_AssocList_find___main___at___private_Init_Lean_MetavarContext_2__visit___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_AssocList_contains___main___at___private_Init_Lean_MetavarContext_2__visit___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AssocList_contains___main___at___private_Init_Lean_MetavarContext_2__visit___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_MetavarContext_3__getMCtx(lean_object* x_1) {
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
lean_object* l___private_Init_Lean_MetavarContext_4__modifyCtx(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 0, x_5);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_10 = lean_apply_1(x_1, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
lean_object* _init_l___private_Init_Lean_MetavarContext_5__instantiateDelayedAux___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Id_Monad;
x_2 = l_StateT_Monad___rarg(x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_MetavarContext_5__instantiateDelayedAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_MetavarContext_5__instantiateDelayedAux___main___closed__1;
x_3 = l_monadInhabited___rarg(x_2, x_1);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_MetavarContext_5__instantiateDelayedAux___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_MetavarContext_getDecl___closed__1;
x_2 = lean_unsigned_to_nat(431u);
x_3 = lean_unsigned_to_nat(12u);
x_4 = l_Nat_foldRevAux___main___at_Lean_LocalContext_mkBinding___spec__1___closed__1;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Init_Lean_MetavarContext_5__instantiateDelayedAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = l_Lean_Expr_Inhabited;
x_12 = lean_array_get(x_11, x_3, x_10);
lean_inc(x_2);
x_13 = l_Lean_LocalContext_findFVar(x_2, x_12);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_14 = l___private_Init_Lean_MetavarContext_5__instantiateDelayedAux___main___closed__2;
x_15 = l___private_Init_Lean_MetavarContext_5__instantiateDelayedAux___main___closed__3;
x_16 = lean_panic_fn(x_15);
x_17 = lean_apply_1(x_16, x_6);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_18, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 3);
lean_inc(x_20);
x_21 = lean_ctor_get_uint8(x_18, sizeof(void*)*4);
lean_dec(x_18);
x_22 = l_Lean_Expr_hasMVar(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_expr_abstract_range(x_20, x_10, x_3);
lean_dec(x_20);
x_24 = l_Lean_mkLambda(x_19, x_21, x_23, x_5);
x_4 = x_10;
x_5 = x_24;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_6, 1);
lean_inc(x_26);
x_27 = l_Lean_Expr_HasBeq;
x_28 = l_Lean_Expr_Hashable;
lean_inc(x_20);
x_29 = l_HashMapImp_find___rarg(x_27, x_28, x_26, x_20);
lean_dec(x_26);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; 
lean_inc(x_1);
lean_inc(x_20);
x_30 = lean_apply_2(x_1, x_20, x_6);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_30, 1);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_30, 0);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
x_36 = l_HashMapImp_insert___rarg(x_27, x_28, x_35, x_20, x_34);
lean_ctor_set(x_32, 1, x_36);
x_37 = l_Lean_Expr_hasMVar(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_free_object(x_30);
x_38 = lean_expr_abstract_range(x_34, x_10, x_3);
lean_dec(x_34);
x_39 = l_Lean_mkLambda(x_19, x_21, x_38, x_5);
x_4 = x_10;
x_5 = x_39;
x_6 = x_32;
goto _start;
}
else
{
lean_object* x_41; 
lean_dec(x_34);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_41 = lean_box(0);
lean_ctor_set(x_30, 0, x_41);
return x_30;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_42 = lean_ctor_get(x_30, 0);
x_43 = lean_ctor_get(x_32, 0);
x_44 = lean_ctor_get(x_32, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_32);
lean_inc(x_42);
x_45 = l_HashMapImp_insert___rarg(x_27, x_28, x_44, x_20, x_42);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_Expr_hasMVar(x_42);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_free_object(x_30);
x_48 = lean_expr_abstract_range(x_42, x_10, x_3);
lean_dec(x_42);
x_49 = l_Lean_mkLambda(x_19, x_21, x_48, x_5);
x_4 = x_10;
x_5 = x_49;
x_6 = x_46;
goto _start;
}
else
{
lean_object* x_51; 
lean_dec(x_42);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_51 = lean_box(0);
lean_ctor_set(x_30, 1, x_46);
lean_ctor_set(x_30, 0, x_51);
return x_30;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_52 = lean_ctor_get(x_30, 1);
x_53 = lean_ctor_get(x_30, 0);
lean_inc(x_52);
lean_inc(x_53);
lean_dec(x_30);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_56 = x_52;
} else {
 lean_dec_ref(x_52);
 x_56 = lean_box(0);
}
lean_inc(x_53);
x_57 = l_HashMapImp_insert___rarg(x_27, x_28, x_55, x_20, x_53);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_54);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_Expr_hasMVar(x_53);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_expr_abstract_range(x_53, x_10, x_3);
lean_dec(x_53);
x_61 = l_Lean_mkLambda(x_19, x_21, x_60, x_5);
x_4 = x_10;
x_5 = x_61;
x_6 = x_58;
goto _start;
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_53);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_58);
return x_64;
}
}
}
else
{
lean_object* x_65; uint8_t x_66; 
lean_dec(x_20);
x_65 = lean_ctor_get(x_29, 0);
lean_inc(x_65);
lean_dec(x_29);
x_66 = l_Lean_Expr_hasMVar(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_expr_abstract_range(x_65, x_10, x_3);
lean_dec(x_65);
x_68 = l_Lean_mkLambda(x_19, x_21, x_67, x_5);
x_4 = x_10;
x_5 = x_68;
goto _start;
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_65);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_6);
return x_71;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_141; 
x_72 = lean_ctor_get(x_18, 2);
lean_inc(x_72);
x_73 = lean_ctor_get(x_18, 3);
lean_inc(x_73);
x_74 = lean_ctor_get(x_18, 4);
lean_inc(x_74);
lean_dec(x_18);
x_141 = l_Lean_Expr_hasMVar(x_73);
if (x_141 == 0)
{
x_75 = x_73;
x_76 = x_6;
goto block_140;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_142 = lean_ctor_get(x_6, 1);
lean_inc(x_142);
x_143 = l_Lean_Expr_HasBeq;
x_144 = l_Lean_Expr_Hashable;
lean_inc(x_73);
x_145 = l_HashMapImp_find___rarg(x_143, x_144, x_142, x_73);
lean_dec(x_142);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
lean_inc(x_1);
lean_inc(x_73);
x_146 = lean_apply_2(x_1, x_73, x_6);
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 0);
lean_inc(x_148);
lean_dec(x_146);
x_149 = !lean_is_exclusive(x_147);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
x_151 = l_HashMapImp_insert___rarg(x_143, x_144, x_150, x_73, x_148);
lean_ctor_set(x_147, 1, x_151);
x_75 = x_148;
x_76 = x_147;
goto block_140;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_152 = lean_ctor_get(x_147, 0);
x_153 = lean_ctor_get(x_147, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_147);
lean_inc(x_148);
x_154 = l_HashMapImp_insert___rarg(x_143, x_144, x_153, x_73, x_148);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_154);
x_75 = x_148;
x_76 = x_155;
goto block_140;
}
}
else
{
lean_object* x_156; 
lean_dec(x_73);
x_156 = lean_ctor_get(x_145, 0);
lean_inc(x_156);
lean_dec(x_145);
x_75 = x_156;
x_76 = x_6;
goto block_140;
}
}
block_140:
{
uint8_t x_77; 
x_77 = l_Lean_Expr_hasMVar(x_75);
if (x_77 == 0)
{
uint8_t x_78; 
x_78 = l_Lean_Expr_hasMVar(x_74);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; 
x_79 = lean_expr_abstract_range(x_75, x_10, x_3);
lean_dec(x_75);
x_80 = lean_expr_abstract_range(x_74, x_10, x_3);
lean_dec(x_74);
x_81 = 0;
x_82 = l_Lean_mkLet(x_72, x_79, x_80, x_5, x_81);
x_4 = x_10;
x_5 = x_82;
x_6 = x_76;
goto _start;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_76, 1);
lean_inc(x_84);
x_85 = l_Lean_Expr_HasBeq;
x_86 = l_Lean_Expr_Hashable;
lean_inc(x_74);
x_87 = l_HashMapImp_find___rarg(x_85, x_86, x_84, x_74);
lean_dec(x_84);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; uint8_t x_89; 
lean_inc(x_1);
lean_inc(x_74);
x_88 = lean_apply_2(x_1, x_74, x_76);
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_ctor_get(x_88, 1);
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_92 = lean_ctor_get(x_88, 0);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
x_94 = l_HashMapImp_insert___rarg(x_85, x_86, x_93, x_74, x_92);
lean_ctor_set(x_90, 1, x_94);
x_95 = l_Lean_Expr_hasMVar(x_92);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; 
lean_free_object(x_88);
x_96 = lean_expr_abstract_range(x_75, x_10, x_3);
lean_dec(x_75);
x_97 = lean_expr_abstract_range(x_92, x_10, x_3);
lean_dec(x_92);
x_98 = 0;
x_99 = l_Lean_mkLet(x_72, x_96, x_97, x_5, x_98);
x_4 = x_10;
x_5 = x_99;
x_6 = x_90;
goto _start;
}
else
{
lean_object* x_101; 
lean_dec(x_92);
lean_dec(x_75);
lean_dec(x_72);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_101 = lean_box(0);
lean_ctor_set(x_88, 0, x_101);
return x_88;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_102 = lean_ctor_get(x_88, 0);
x_103 = lean_ctor_get(x_90, 0);
x_104 = lean_ctor_get(x_90, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_90);
lean_inc(x_102);
x_105 = l_HashMapImp_insert___rarg(x_85, x_86, x_104, x_74, x_102);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_Expr_hasMVar(x_102);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; 
lean_free_object(x_88);
x_108 = lean_expr_abstract_range(x_75, x_10, x_3);
lean_dec(x_75);
x_109 = lean_expr_abstract_range(x_102, x_10, x_3);
lean_dec(x_102);
x_110 = 0;
x_111 = l_Lean_mkLet(x_72, x_108, x_109, x_5, x_110);
x_4 = x_10;
x_5 = x_111;
x_6 = x_106;
goto _start;
}
else
{
lean_object* x_113; 
lean_dec(x_102);
lean_dec(x_75);
lean_dec(x_72);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_113 = lean_box(0);
lean_ctor_set(x_88, 1, x_106);
lean_ctor_set(x_88, 0, x_113);
return x_88;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_114 = lean_ctor_get(x_88, 1);
x_115 = lean_ctor_get(x_88, 0);
lean_inc(x_114);
lean_inc(x_115);
lean_dec(x_88);
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_118 = x_114;
} else {
 lean_dec_ref(x_114);
 x_118 = lean_box(0);
}
lean_inc(x_115);
x_119 = l_HashMapImp_insert___rarg(x_85, x_86, x_117, x_74, x_115);
if (lean_is_scalar(x_118)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_118;
}
lean_ctor_set(x_120, 0, x_116);
lean_ctor_set(x_120, 1, x_119);
x_121 = l_Lean_Expr_hasMVar(x_115);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; 
x_122 = lean_expr_abstract_range(x_75, x_10, x_3);
lean_dec(x_75);
x_123 = lean_expr_abstract_range(x_115, x_10, x_3);
lean_dec(x_115);
x_124 = 0;
x_125 = l_Lean_mkLet(x_72, x_122, x_123, x_5, x_124);
x_4 = x_10;
x_5 = x_125;
x_6 = x_120;
goto _start;
}
else
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_115);
lean_dec(x_75);
lean_dec(x_72);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_127 = lean_box(0);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_120);
return x_128;
}
}
}
else
{
lean_object* x_129; uint8_t x_130; 
lean_dec(x_74);
x_129 = lean_ctor_get(x_87, 0);
lean_inc(x_129);
lean_dec(x_87);
x_130 = l_Lean_Expr_hasMVar(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; 
x_131 = lean_expr_abstract_range(x_75, x_10, x_3);
lean_dec(x_75);
x_132 = lean_expr_abstract_range(x_129, x_10, x_3);
lean_dec(x_129);
x_133 = 0;
x_134 = l_Lean_mkLet(x_72, x_131, x_132, x_5, x_133);
x_4 = x_10;
x_5 = x_134;
x_6 = x_76;
goto _start;
}
else
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_129);
lean_dec(x_75);
lean_dec(x_72);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_136 = lean_box(0);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_76);
return x_137;
}
}
}
}
else
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_138 = lean_box(0);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_76);
return x_139;
}
}
}
}
}
else
{
lean_object* x_157; lean_object* x_158; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_157 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_157, 0, x_5);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_6);
return x_158;
}
}
}
lean_object* l___private_Init_Lean_MetavarContext_5__instantiateDelayedAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_MetavarContext_5__instantiateDelayedAux___main(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
lean_object* l___private_Init_Lean_MetavarContext_5__instantiateDelayedAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_MetavarContext_5__instantiateDelayedAux___main(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Init_Lean_MetavarContext_5__instantiateDelayedAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_MetavarContext_5__instantiateDelayedAux(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
lean_object* l___private_Init_Lean_MetavarContext_6__instantiateDelayed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_69; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
lean_dec(x_3);
x_69 = l_Lean_Expr_hasMVar(x_7);
if (x_69 == 0)
{
x_8 = x_7;
x_9 = x_4;
goto block_68;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_4, 1);
lean_inc(x_70);
x_71 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_70, x_7);
lean_dec(x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
lean_inc(x_1);
lean_inc(x_7);
x_72 = lean_apply_2(x_1, x_7, x_4);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
lean_dec(x_72);
x_75 = !lean_is_exclusive(x_73);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
x_77 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_76, x_7, x_74);
lean_ctor_set(x_73, 1, x_77);
x_8 = x_74;
x_9 = x_73;
goto block_68;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_73, 0);
x_79 = lean_ctor_get(x_73, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_73);
lean_inc(x_74);
x_80 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_79, x_7, x_74);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_80);
x_8 = x_74;
x_9 = x_81;
goto block_68;
}
}
else
{
lean_object* x_82; 
lean_dec(x_7);
x_82 = lean_ctor_get(x_71, 0);
lean_inc(x_82);
lean_dec(x_71);
x_8 = x_82;
x_9 = x_4;
goto block_68;
}
}
block_68:
{
uint8_t x_10; 
x_10 = l_Lean_Expr_hasMVar(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_get_size(x_6);
x_12 = lean_expr_abstract(x_8, x_6);
lean_inc(x_5);
x_13 = l___private_Init_Lean_MetavarContext_5__instantiateDelayedAux___main(x_1, x_5, x_6, x_11, x_12, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_metavar_ctx_assign_delayed(x_19, x_2, x_5, x_6, x_8);
lean_ctor_set(x_16, 0, x_20);
x_21 = lean_box(0);
lean_ctor_set(x_13, 0, x_21);
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_metavar_ctx_assign_delayed(x_22, x_2, x_5, x_6, x_8);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_box(0);
lean_ctor_set(x_13, 1, x_25);
lean_ctor_set(x_13, 0, x_26);
return x_13;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_dec(x_13);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
x_31 = lean_metavar_ctx_assign_delayed(x_28, x_2, x_5, x_6, x_8);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_35 = !lean_is_exclusive(x_13);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_13, 1);
x_37 = lean_ctor_get(x_13, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_14, 0);
lean_inc(x_38);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 0);
lean_inc(x_2);
x_41 = lean_metavar_ctx_erase_delayed(x_40, x_2);
x_42 = lean_metavar_ctx_assign_expr(x_41, x_2, x_38);
lean_ctor_set(x_36, 0, x_42);
return x_13;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_36, 0);
x_44 = lean_ctor_get(x_36, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_36);
lean_inc(x_2);
x_45 = lean_metavar_ctx_erase_delayed(x_43, x_2);
x_46 = lean_metavar_ctx_assign_expr(x_45, x_2, x_38);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
lean_ctor_set(x_13, 1, x_47);
return x_13;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_48 = lean_ctor_get(x_13, 1);
lean_inc(x_48);
lean_dec(x_13);
x_49 = lean_ctor_get(x_14, 0);
lean_inc(x_49);
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
lean_inc(x_2);
x_53 = lean_metavar_ctx_erase_delayed(x_50, x_2);
x_54 = lean_metavar_ctx_assign_expr(x_53, x_2, x_49);
if (lean_is_scalar(x_52)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_52;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_51);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_14);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_9);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_9, 0);
x_59 = lean_metavar_ctx_assign_delayed(x_58, x_2, x_5, x_6, x_8);
lean_ctor_set(x_9, 0, x_59);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_9);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_9, 0);
x_63 = lean_ctor_get(x_9, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_9);
x_64 = lean_metavar_ctx_assign_delayed(x_62, x_2, x_5, x_6, x_8);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
}
}
lean_object* l___private_Init_Lean_MetavarContext_5__instantiateDelayedAux___main___at_Lean_MetavarContext_InstantiateExprMVars_main___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_3, x_8);
lean_dec(x_3);
x_10 = l_Lean_Expr_Inhabited;
x_11 = lean_array_get(x_10, x_2, x_9);
lean_inc(x_1);
x_12 = l_Lean_LocalContext_findFVar(x_1, x_11);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_13 = l___private_Init_Lean_MetavarContext_5__instantiateDelayedAux___main___closed__2;
x_14 = l___private_Init_Lean_MetavarContext_5__instantiateDelayedAux___main___closed__3;
x_15 = lean_panic_fn(x_14);
x_16 = lean_apply_1(x_15, x_5);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 3);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_17, sizeof(void*)*4);
lean_dec(x_17);
x_21 = l_Lean_Expr_hasMVar(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_expr_abstract_range(x_19, x_9, x_2);
lean_dec(x_19);
x_23 = l_Lean_mkLambda(x_18, x_20, x_22, x_4);
x_3 = x_9;
x_4 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_5, 1);
lean_inc(x_25);
x_26 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_25, x_19);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; 
lean_inc(x_19);
x_27 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_19, x_5);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_27, 1);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
x_33 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_32, x_19, x_31);
lean_ctor_set(x_29, 1, x_33);
x_34 = l_Lean_Expr_hasMVar(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_free_object(x_27);
x_35 = lean_expr_abstract_range(x_31, x_9, x_2);
lean_dec(x_31);
x_36 = l_Lean_mkLambda(x_18, x_20, x_35, x_4);
x_3 = x_9;
x_4 = x_36;
x_5 = x_29;
goto _start;
}
else
{
lean_object* x_38; 
lean_dec(x_31);
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_38 = lean_box(0);
lean_ctor_set(x_27, 0, x_38);
return x_27;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_39 = lean_ctor_get(x_27, 0);
x_40 = lean_ctor_get(x_29, 0);
x_41 = lean_ctor_get(x_29, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_29);
lean_inc(x_39);
x_42 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_41, x_19, x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Expr_hasMVar(x_39);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_free_object(x_27);
x_45 = lean_expr_abstract_range(x_39, x_9, x_2);
lean_dec(x_39);
x_46 = l_Lean_mkLambda(x_18, x_20, x_45, x_4);
x_3 = x_9;
x_4 = x_46;
x_5 = x_43;
goto _start;
}
else
{
lean_object* x_48; 
lean_dec(x_39);
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_48 = lean_box(0);
lean_ctor_set(x_27, 1, x_43);
lean_ctor_set(x_27, 0, x_48);
return x_27;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_49 = lean_ctor_get(x_27, 1);
x_50 = lean_ctor_get(x_27, 0);
lean_inc(x_49);
lean_inc(x_50);
lean_dec(x_27);
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
lean_inc(x_50);
x_54 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_52, x_19, x_50);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_51);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_Expr_hasMVar(x_50);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_expr_abstract_range(x_50, x_9, x_2);
lean_dec(x_50);
x_58 = l_Lean_mkLambda(x_18, x_20, x_57, x_4);
x_3 = x_9;
x_4 = x_58;
x_5 = x_55;
goto _start;
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_50);
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_55);
return x_61;
}
}
}
else
{
lean_object* x_62; uint8_t x_63; 
lean_dec(x_19);
x_62 = lean_ctor_get(x_26, 0);
lean_inc(x_62);
lean_dec(x_26);
x_63 = l_Lean_Expr_hasMVar(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_expr_abstract_range(x_62, x_9, x_2);
lean_dec(x_62);
x_65 = l_Lean_mkLambda(x_18, x_20, x_64, x_4);
x_3 = x_9;
x_4 = x_65;
goto _start;
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_62);
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_5);
return x_68;
}
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_136; 
x_69 = lean_ctor_get(x_17, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_17, 3);
lean_inc(x_70);
x_71 = lean_ctor_get(x_17, 4);
lean_inc(x_71);
lean_dec(x_17);
x_136 = l_Lean_Expr_hasMVar(x_70);
if (x_136 == 0)
{
x_72 = x_70;
x_73 = x_5;
goto block_135;
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_5, 1);
lean_inc(x_137);
x_138 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_137, x_70);
lean_dec(x_137);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
lean_inc(x_70);
x_139 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_70, x_5);
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 0);
lean_inc(x_141);
lean_dec(x_139);
x_142 = !lean_is_exclusive(x_140);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
x_144 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_143, x_70, x_141);
lean_ctor_set(x_140, 1, x_144);
x_72 = x_141;
x_73 = x_140;
goto block_135;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_145 = lean_ctor_get(x_140, 0);
x_146 = lean_ctor_get(x_140, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_140);
lean_inc(x_141);
x_147 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_146, x_70, x_141);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_147);
x_72 = x_141;
x_73 = x_148;
goto block_135;
}
}
else
{
lean_object* x_149; 
lean_dec(x_70);
x_149 = lean_ctor_get(x_138, 0);
lean_inc(x_149);
lean_dec(x_138);
x_72 = x_149;
x_73 = x_5;
goto block_135;
}
}
block_135:
{
uint8_t x_74; 
x_74 = l_Lean_Expr_hasMVar(x_72);
if (x_74 == 0)
{
uint8_t x_75; 
x_75 = l_Lean_Expr_hasMVar(x_71);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; 
x_76 = lean_expr_abstract_range(x_72, x_9, x_2);
lean_dec(x_72);
x_77 = lean_expr_abstract_range(x_71, x_9, x_2);
lean_dec(x_71);
x_78 = 0;
x_79 = l_Lean_mkLet(x_69, x_76, x_77, x_4, x_78);
x_3 = x_9;
x_4 = x_79;
x_5 = x_73;
goto _start;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_73, 1);
lean_inc(x_81);
x_82 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_81, x_71);
lean_dec(x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; uint8_t x_84; 
lean_inc(x_71);
x_83 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_71, x_73);
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_ctor_get(x_83, 1);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_87 = lean_ctor_get(x_83, 0);
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
x_89 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_88, x_71, x_87);
lean_ctor_set(x_85, 1, x_89);
x_90 = l_Lean_Expr_hasMVar(x_87);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; 
lean_free_object(x_83);
x_91 = lean_expr_abstract_range(x_72, x_9, x_2);
lean_dec(x_72);
x_92 = lean_expr_abstract_range(x_87, x_9, x_2);
lean_dec(x_87);
x_93 = 0;
x_94 = l_Lean_mkLet(x_69, x_91, x_92, x_4, x_93);
x_3 = x_9;
x_4 = x_94;
x_5 = x_85;
goto _start;
}
else
{
lean_object* x_96; 
lean_dec(x_87);
lean_dec(x_72);
lean_dec(x_69);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_96 = lean_box(0);
lean_ctor_set(x_83, 0, x_96);
return x_83;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_97 = lean_ctor_get(x_83, 0);
x_98 = lean_ctor_get(x_85, 0);
x_99 = lean_ctor_get(x_85, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_85);
lean_inc(x_97);
x_100 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_99, x_71, x_97);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_100);
x_102 = l_Lean_Expr_hasMVar(x_97);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; 
lean_free_object(x_83);
x_103 = lean_expr_abstract_range(x_72, x_9, x_2);
lean_dec(x_72);
x_104 = lean_expr_abstract_range(x_97, x_9, x_2);
lean_dec(x_97);
x_105 = 0;
x_106 = l_Lean_mkLet(x_69, x_103, x_104, x_4, x_105);
x_3 = x_9;
x_4 = x_106;
x_5 = x_101;
goto _start;
}
else
{
lean_object* x_108; 
lean_dec(x_97);
lean_dec(x_72);
lean_dec(x_69);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_108 = lean_box(0);
lean_ctor_set(x_83, 1, x_101);
lean_ctor_set(x_83, 0, x_108);
return x_83;
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_109 = lean_ctor_get(x_83, 1);
x_110 = lean_ctor_get(x_83, 0);
lean_inc(x_109);
lean_inc(x_110);
lean_dec(x_83);
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_113 = x_109;
} else {
 lean_dec_ref(x_109);
 x_113 = lean_box(0);
}
lean_inc(x_110);
x_114 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_112, x_71, x_110);
if (lean_is_scalar(x_113)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_113;
}
lean_ctor_set(x_115, 0, x_111);
lean_ctor_set(x_115, 1, x_114);
x_116 = l_Lean_Expr_hasMVar(x_110);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; 
x_117 = lean_expr_abstract_range(x_72, x_9, x_2);
lean_dec(x_72);
x_118 = lean_expr_abstract_range(x_110, x_9, x_2);
lean_dec(x_110);
x_119 = 0;
x_120 = l_Lean_mkLet(x_69, x_117, x_118, x_4, x_119);
x_3 = x_9;
x_4 = x_120;
x_5 = x_115;
goto _start;
}
else
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_110);
lean_dec(x_72);
lean_dec(x_69);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_122 = lean_box(0);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_115);
return x_123;
}
}
}
else
{
lean_object* x_124; uint8_t x_125; 
lean_dec(x_71);
x_124 = lean_ctor_get(x_82, 0);
lean_inc(x_124);
lean_dec(x_82);
x_125 = l_Lean_Expr_hasMVar(x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; 
x_126 = lean_expr_abstract_range(x_72, x_9, x_2);
lean_dec(x_72);
x_127 = lean_expr_abstract_range(x_124, x_9, x_2);
lean_dec(x_124);
x_128 = 0;
x_129 = l_Lean_mkLet(x_69, x_126, x_127, x_4, x_128);
x_3 = x_9;
x_4 = x_129;
x_5 = x_73;
goto _start;
}
else
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_124);
lean_dec(x_72);
lean_dec(x_69);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_131 = lean_box(0);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_73);
return x_132;
}
}
}
}
else
{
lean_object* x_133; lean_object* x_134; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_69);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_133 = lean_box(0);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_73);
return x_134;
}
}
}
}
}
else
{
lean_object* x_150; lean_object* x_151; 
lean_dec(x_3);
lean_dec(x_1);
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_4);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_5);
return x_151;
}
}
}
lean_object* l_List_mapM___main___at_Lean_MetavarContext_InstantiateExprMVars_main___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_2, 0);
x_10 = l_Lean_MetavarContext_instantiateLevelMVars___main(x_7, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_ctor_set(x_2, 0, x_12);
x_13 = l_List_mapM___main___at_Lean_MetavarContext_InstantiateExprMVars_main___main___spec__2(x_8, x_2);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_11);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_13);
lean_ctor_set(x_1, 1, x_16);
lean_ctor_set(x_1, 0, x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_2);
x_23 = l_Lean_MetavarContext_instantiateLevelMVars___main(x_19, x_21);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
x_27 = l_List_mapM___main___at_Lean_MetavarContext_InstantiateExprMVars_main___main___spec__2(x_20, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
lean_ctor_set(x_1, 1, x_28);
lean_ctor_set(x_1, 0, x_24);
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_32 = lean_ctor_get(x_1, 0);
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_1);
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_2, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_36 = x_2;
} else {
 lean_dec_ref(x_2);
 x_36 = lean_box(0);
}
x_37 = l_Lean_MetavarContext_instantiateLevelMVars___main(x_32, x_34);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
if (lean_is_scalar(x_36)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_36;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_35);
x_41 = l_List_mapM___main___at_Lean_MetavarContext_InstantiateExprMVars_main___main___spec__2(x_33, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_42);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_MetavarContext_InstantiateExprMVars_main___main___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_6 = l_Array_empty___closed__1;
x_7 = x_2;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_array_fget(x_2, x_1);
x_10 = lean_box(0);
lean_inc(x_9);
x_11 = x_10;
x_12 = lean_array_fset(x_2, x_1, x_11);
x_13 = l_Lean_Expr_hasMVar(x_9);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_1, x_14);
lean_inc(x_9);
x_16 = x_9;
x_17 = lean_array_fset(x_12, x_1, x_16);
lean_dec(x_1);
x_1 = x_15;
x_2 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
x_20 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_19, x_9);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_inc(x_9);
x_21 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_9, x_3);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_inc(x_9);
x_26 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_25, x_9, x_23);
lean_ctor_set(x_22, 1, x_26);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_1, x_27);
x_29 = x_23;
x_30 = lean_array_fset(x_12, x_1, x_29);
lean_dec(x_1);
x_1 = x_28;
x_2 = x_30;
x_3 = x_22;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_22, 0);
x_33 = lean_ctor_get(x_22, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_22);
lean_inc(x_23);
lean_inc(x_9);
x_34 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_33, x_9, x_23);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_1, x_36);
x_38 = x_23;
x_39 = lean_array_fset(x_12, x_1, x_38);
lean_dec(x_1);
x_1 = x_37;
x_2 = x_39;
x_3 = x_35;
goto _start;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_20, 0);
lean_inc(x_41);
lean_dec(x_20);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_add(x_1, x_42);
x_44 = x_41;
x_45 = lean_array_fset(x_12, x_1, x_44);
lean_dec(x_1);
x_1 = x_43;
x_2 = x_45;
goto _start;
}
}
}
}
}
lean_object* l___private_Init_Lean_Expr_5__withAppRevAux___main___at_Lean_MetavarContext_InstantiateExprMVars_main___main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; uint8_t x_49; 
x_4 = l_Lean_Expr_isMVar(x_1);
x_49 = l_Lean_Expr_hasMVar(x_1);
if (x_49 == 0)
{
x_5 = x_1;
x_6 = x_3;
goto block_48;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_3, 1);
lean_inc(x_50);
x_51 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_50, x_1);
lean_dec(x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_inc(x_1);
x_52 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_1, x_3);
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
x_57 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_56, x_1, x_54);
lean_ctor_set(x_53, 1, x_57);
x_5 = x_54;
x_6 = x_53;
goto block_48;
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
x_60 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_59, x_1, x_54);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_60);
x_5 = x_54;
x_6 = x_61;
goto block_48;
}
}
else
{
lean_object* x_62; 
lean_dec(x_1);
x_62 = lean_ctor_get(x_51, 0);
lean_inc(x_62);
lean_dec(x_51);
x_5 = x_62;
x_6 = x_3;
goto block_48;
}
}
block_48:
{
lean_object* x_7; 
if (x_4 == 0)
{
lean_object* x_18; 
x_18 = lean_box(0);
x_7 = x_18;
goto block_17;
}
else
{
uint8_t x_19; 
x_19 = l_Lean_Expr_isLambda(x_5);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_box(0);
x_7 = x_20;
goto block_17;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lean_Expr_betaRev(x_5, x_2);
lean_dec(x_5);
x_22 = l_Lean_Expr_hasMVar(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
x_25 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_24, x_21);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; 
lean_inc(x_21);
x_26 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_21, x_6);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_26, 1);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
x_32 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_31, x_21, x_30);
lean_ctor_set(x_28, 1, x_32);
return x_26;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_ctor_get(x_28, 0);
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_28);
lean_inc(x_33);
x_36 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_35, x_21, x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_26, 1, x_37);
return x_26;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_26, 1);
x_39 = lean_ctor_get(x_26, 0);
lean_inc(x_38);
lean_inc(x_39);
lean_dec(x_26);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_42 = x_38;
} else {
 lean_dec_ref(x_38);
 x_42 = lean_box(0);
}
lean_inc(x_39);
x_43 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_41, x_21, x_39);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_21);
x_46 = lean_ctor_get(x_25, 0);
lean_inc(x_46);
lean_dec(x_25);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_6);
return x_47;
}
}
}
}
block_17:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_dec(x_7);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_umapMAux___main___at_Lean_MetavarContext_InstantiateExprMVars_main___main___spec__3(x_8, x_2, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_mkAppRev(x_5, x_11);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_12);
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
x_15 = l_Lean_mkAppRev(x_5, x_13);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
}
case 1:
{
uint8_t x_63; lean_object* x_64; lean_object* x_65; uint8_t x_108; 
x_63 = l_Lean_Expr_isMVar(x_1);
x_108 = l_Lean_Expr_hasMVar(x_1);
if (x_108 == 0)
{
x_64 = x_1;
x_65 = x_3;
goto block_107;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_3, 1);
lean_inc(x_109);
x_110 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_109, x_1);
lean_dec(x_109);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
lean_inc(x_1);
x_111 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_1, x_3);
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
x_116 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_115, x_1, x_113);
lean_ctor_set(x_112, 1, x_116);
x_64 = x_113;
x_65 = x_112;
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
x_119 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_118, x_1, x_113);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_119);
x_64 = x_113;
x_65 = x_120;
goto block_107;
}
}
else
{
lean_object* x_121; 
lean_dec(x_1);
x_121 = lean_ctor_get(x_110, 0);
lean_inc(x_121);
lean_dec(x_110);
x_64 = x_121;
x_65 = x_3;
goto block_107;
}
}
block_107:
{
lean_object* x_66; 
if (x_63 == 0)
{
lean_object* x_77; 
x_77 = lean_box(0);
x_66 = x_77;
goto block_76;
}
else
{
uint8_t x_78; 
x_78 = l_Lean_Expr_isLambda(x_64);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = lean_box(0);
x_66 = x_79;
goto block_76;
}
else
{
lean_object* x_80; uint8_t x_81; 
x_80 = l_Lean_Expr_betaRev(x_64, x_2);
lean_dec(x_64);
x_81 = l_Lean_Expr_hasMVar(x_80);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_65);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_65, 1);
lean_inc(x_83);
x_84 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_83, x_80);
lean_dec(x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; uint8_t x_86; 
lean_inc(x_80);
x_85 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_80, x_65);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_85, 1);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_85, 0);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
x_91 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_90, x_80, x_89);
lean_ctor_set(x_87, 1, x_91);
return x_85;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_ctor_get(x_85, 0);
x_93 = lean_ctor_get(x_87, 0);
x_94 = lean_ctor_get(x_87, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_87);
lean_inc(x_92);
x_95 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_94, x_80, x_92);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_95);
lean_ctor_set(x_85, 1, x_96);
return x_85;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_97 = lean_ctor_get(x_85, 1);
x_98 = lean_ctor_get(x_85, 0);
lean_inc(x_97);
lean_inc(x_98);
lean_dec(x_85);
x_99 = lean_ctor_get(x_97, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_101 = x_97;
} else {
 lean_dec_ref(x_97);
 x_101 = lean_box(0);
}
lean_inc(x_98);
x_102 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_100, x_80, x_98);
if (lean_is_scalar(x_101)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_101;
}
lean_ctor_set(x_103, 0, x_99);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_98);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_80);
x_105 = lean_ctor_get(x_84, 0);
lean_inc(x_105);
lean_dec(x_84);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_65);
return x_106;
}
}
}
}
block_76:
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
lean_dec(x_66);
x_67 = lean_unsigned_to_nat(0u);
x_68 = l_Array_umapMAux___main___at_Lean_MetavarContext_InstantiateExprMVars_main___main___spec__3(x_67, x_2, x_65);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_68, 0);
x_71 = l_Lean_mkAppRev(x_64, x_70);
lean_dec(x_70);
lean_ctor_set(x_68, 0, x_71);
return x_68;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_68, 0);
x_73 = lean_ctor_get(x_68, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_68);
x_74 = l_Lean_mkAppRev(x_64, x_72);
lean_dec(x_72);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
}
}
case 2:
{
uint8_t x_122; lean_object* x_123; lean_object* x_124; uint8_t x_167; 
x_122 = l_Lean_Expr_isMVar(x_1);
x_167 = l_Lean_Expr_hasMVar(x_1);
if (x_167 == 0)
{
x_123 = x_1;
x_124 = x_3;
goto block_166;
}
else
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_3, 1);
lean_inc(x_168);
x_169 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_168, x_1);
lean_dec(x_168);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
lean_inc(x_1);
x_170 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_1, x_3);
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 0);
lean_inc(x_172);
lean_dec(x_170);
x_173 = !lean_is_exclusive(x_171);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_171, 1);
lean_inc(x_172);
x_175 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_174, x_1, x_172);
lean_ctor_set(x_171, 1, x_175);
x_123 = x_172;
x_124 = x_171;
goto block_166;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_176 = lean_ctor_get(x_171, 0);
x_177 = lean_ctor_get(x_171, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_171);
lean_inc(x_172);
x_178 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_177, x_1, x_172);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_176);
lean_ctor_set(x_179, 1, x_178);
x_123 = x_172;
x_124 = x_179;
goto block_166;
}
}
else
{
lean_object* x_180; 
lean_dec(x_1);
x_180 = lean_ctor_get(x_169, 0);
lean_inc(x_180);
lean_dec(x_169);
x_123 = x_180;
x_124 = x_3;
goto block_166;
}
}
block_166:
{
lean_object* x_125; 
if (x_122 == 0)
{
lean_object* x_136; 
x_136 = lean_box(0);
x_125 = x_136;
goto block_135;
}
else
{
uint8_t x_137; 
x_137 = l_Lean_Expr_isLambda(x_123);
if (x_137 == 0)
{
lean_object* x_138; 
x_138 = lean_box(0);
x_125 = x_138;
goto block_135;
}
else
{
lean_object* x_139; uint8_t x_140; 
x_139 = l_Lean_Expr_betaRev(x_123, x_2);
lean_dec(x_123);
x_140 = l_Lean_Expr_hasMVar(x_139);
if (x_140 == 0)
{
lean_object* x_141; 
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_124);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_124, 1);
lean_inc(x_142);
x_143 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_142, x_139);
lean_dec(x_142);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; uint8_t x_145; 
lean_inc(x_139);
x_144 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_139, x_124);
x_145 = !lean_is_exclusive(x_144);
if (x_145 == 0)
{
lean_object* x_146; uint8_t x_147; 
x_146 = lean_ctor_get(x_144, 1);
x_147 = !lean_is_exclusive(x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_144, 0);
x_149 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
x_150 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_149, x_139, x_148);
lean_ctor_set(x_146, 1, x_150);
return x_144;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_151 = lean_ctor_get(x_144, 0);
x_152 = lean_ctor_get(x_146, 0);
x_153 = lean_ctor_get(x_146, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_146);
lean_inc(x_151);
x_154 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_153, x_139, x_151);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_154);
lean_ctor_set(x_144, 1, x_155);
return x_144;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_156 = lean_ctor_get(x_144, 1);
x_157 = lean_ctor_get(x_144, 0);
lean_inc(x_156);
lean_inc(x_157);
lean_dec(x_144);
x_158 = lean_ctor_get(x_156, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_156, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_160 = x_156;
} else {
 lean_dec_ref(x_156);
 x_160 = lean_box(0);
}
lean_inc(x_157);
x_161 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_159, x_139, x_157);
if (lean_is_scalar(x_160)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_160;
}
lean_ctor_set(x_162, 0, x_158);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_157);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
}
else
{
lean_object* x_164; lean_object* x_165; 
lean_dec(x_139);
x_164 = lean_ctor_get(x_143, 0);
lean_inc(x_164);
lean_dec(x_143);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_124);
return x_165;
}
}
}
}
block_135:
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; 
lean_dec(x_125);
x_126 = lean_unsigned_to_nat(0u);
x_127 = l_Array_umapMAux___main___at_Lean_MetavarContext_InstantiateExprMVars_main___main___spec__3(x_126, x_2, x_124);
x_128 = !lean_is_exclusive(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_127, 0);
x_130 = l_Lean_mkAppRev(x_123, x_129);
lean_dec(x_129);
lean_ctor_set(x_127, 0, x_130);
return x_127;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_127, 0);
x_132 = lean_ctor_get(x_127, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_127);
x_133 = l_Lean_mkAppRev(x_123, x_131);
lean_dec(x_131);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
}
}
case 3:
{
uint8_t x_181; lean_object* x_182; lean_object* x_183; uint8_t x_226; 
x_181 = l_Lean_Expr_isMVar(x_1);
x_226 = l_Lean_Expr_hasMVar(x_1);
if (x_226 == 0)
{
x_182 = x_1;
x_183 = x_3;
goto block_225;
}
else
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_ctor_get(x_3, 1);
lean_inc(x_227);
x_228 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_227, x_1);
lean_dec(x_227);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; 
lean_inc(x_1);
x_229 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_1, x_3);
x_230 = lean_ctor_get(x_229, 1);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 0);
lean_inc(x_231);
lean_dec(x_229);
x_232 = !lean_is_exclusive(x_230);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; 
x_233 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
x_234 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_233, x_1, x_231);
lean_ctor_set(x_230, 1, x_234);
x_182 = x_231;
x_183 = x_230;
goto block_225;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_235 = lean_ctor_get(x_230, 0);
x_236 = lean_ctor_get(x_230, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_230);
lean_inc(x_231);
x_237 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_236, x_1, x_231);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_235);
lean_ctor_set(x_238, 1, x_237);
x_182 = x_231;
x_183 = x_238;
goto block_225;
}
}
else
{
lean_object* x_239; 
lean_dec(x_1);
x_239 = lean_ctor_get(x_228, 0);
lean_inc(x_239);
lean_dec(x_228);
x_182 = x_239;
x_183 = x_3;
goto block_225;
}
}
block_225:
{
lean_object* x_184; 
if (x_181 == 0)
{
lean_object* x_195; 
x_195 = lean_box(0);
x_184 = x_195;
goto block_194;
}
else
{
uint8_t x_196; 
x_196 = l_Lean_Expr_isLambda(x_182);
if (x_196 == 0)
{
lean_object* x_197; 
x_197 = lean_box(0);
x_184 = x_197;
goto block_194;
}
else
{
lean_object* x_198; uint8_t x_199; 
x_198 = l_Lean_Expr_betaRev(x_182, x_2);
lean_dec(x_182);
x_199 = l_Lean_Expr_hasMVar(x_198);
if (x_199 == 0)
{
lean_object* x_200; 
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_183);
return x_200;
}
else
{
lean_object* x_201; lean_object* x_202; 
x_201 = lean_ctor_get(x_183, 1);
lean_inc(x_201);
x_202 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_201, x_198);
lean_dec(x_201);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; uint8_t x_204; 
lean_inc(x_198);
x_203 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_198, x_183);
x_204 = !lean_is_exclusive(x_203);
if (x_204 == 0)
{
lean_object* x_205; uint8_t x_206; 
x_205 = lean_ctor_get(x_203, 1);
x_206 = !lean_is_exclusive(x_205);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_203, 0);
x_208 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
x_209 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_208, x_198, x_207);
lean_ctor_set(x_205, 1, x_209);
return x_203;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_210 = lean_ctor_get(x_203, 0);
x_211 = lean_ctor_get(x_205, 0);
x_212 = lean_ctor_get(x_205, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_205);
lean_inc(x_210);
x_213 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_212, x_198, x_210);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_211);
lean_ctor_set(x_214, 1, x_213);
lean_ctor_set(x_203, 1, x_214);
return x_203;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_215 = lean_ctor_get(x_203, 1);
x_216 = lean_ctor_get(x_203, 0);
lean_inc(x_215);
lean_inc(x_216);
lean_dec(x_203);
x_217 = lean_ctor_get(x_215, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_215, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_219 = x_215;
} else {
 lean_dec_ref(x_215);
 x_219 = lean_box(0);
}
lean_inc(x_216);
x_220 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_218, x_198, x_216);
if (lean_is_scalar(x_219)) {
 x_221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_221 = x_219;
}
lean_ctor_set(x_221, 0, x_217);
lean_ctor_set(x_221, 1, x_220);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_216);
lean_ctor_set(x_222, 1, x_221);
return x_222;
}
}
else
{
lean_object* x_223; lean_object* x_224; 
lean_dec(x_198);
x_223 = lean_ctor_get(x_202, 0);
lean_inc(x_223);
lean_dec(x_202);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_183);
return x_224;
}
}
}
}
block_194:
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; 
lean_dec(x_184);
x_185 = lean_unsigned_to_nat(0u);
x_186 = l_Array_umapMAux___main___at_Lean_MetavarContext_InstantiateExprMVars_main___main___spec__3(x_185, x_2, x_183);
x_187 = !lean_is_exclusive(x_186);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; 
x_188 = lean_ctor_get(x_186, 0);
x_189 = l_Lean_mkAppRev(x_182, x_188);
lean_dec(x_188);
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
x_192 = l_Lean_mkAppRev(x_182, x_190);
lean_dec(x_190);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_191);
return x_193;
}
}
}
}
case 4:
{
uint8_t x_240; lean_object* x_241; lean_object* x_242; uint8_t x_285; 
x_240 = l_Lean_Expr_isMVar(x_1);
x_285 = l_Lean_Expr_hasMVar(x_1);
if (x_285 == 0)
{
x_241 = x_1;
x_242 = x_3;
goto block_284;
}
else
{
lean_object* x_286; lean_object* x_287; 
x_286 = lean_ctor_get(x_3, 1);
lean_inc(x_286);
x_287 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_286, x_1);
lean_dec(x_286);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; 
lean_inc(x_1);
x_288 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_1, x_3);
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
x_293 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_292, x_1, x_290);
lean_ctor_set(x_289, 1, x_293);
x_241 = x_290;
x_242 = x_289;
goto block_284;
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
x_296 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_295, x_1, x_290);
x_297 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_297, 0, x_294);
lean_ctor_set(x_297, 1, x_296);
x_241 = x_290;
x_242 = x_297;
goto block_284;
}
}
else
{
lean_object* x_298; 
lean_dec(x_1);
x_298 = lean_ctor_get(x_287, 0);
lean_inc(x_298);
lean_dec(x_287);
x_241 = x_298;
x_242 = x_3;
goto block_284;
}
}
block_284:
{
lean_object* x_243; 
if (x_240 == 0)
{
lean_object* x_254; 
x_254 = lean_box(0);
x_243 = x_254;
goto block_253;
}
else
{
uint8_t x_255; 
x_255 = l_Lean_Expr_isLambda(x_241);
if (x_255 == 0)
{
lean_object* x_256; 
x_256 = lean_box(0);
x_243 = x_256;
goto block_253;
}
else
{
lean_object* x_257; uint8_t x_258; 
x_257 = l_Lean_Expr_betaRev(x_241, x_2);
lean_dec(x_241);
x_258 = l_Lean_Expr_hasMVar(x_257);
if (x_258 == 0)
{
lean_object* x_259; 
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_242);
return x_259;
}
else
{
lean_object* x_260; lean_object* x_261; 
x_260 = lean_ctor_get(x_242, 1);
lean_inc(x_260);
x_261 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_260, x_257);
lean_dec(x_260);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; uint8_t x_263; 
lean_inc(x_257);
x_262 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_257, x_242);
x_263 = !lean_is_exclusive(x_262);
if (x_263 == 0)
{
lean_object* x_264; uint8_t x_265; 
x_264 = lean_ctor_get(x_262, 1);
x_265 = !lean_is_exclusive(x_264);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_ctor_get(x_262, 0);
x_267 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
x_268 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_267, x_257, x_266);
lean_ctor_set(x_264, 1, x_268);
return x_262;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_269 = lean_ctor_get(x_262, 0);
x_270 = lean_ctor_get(x_264, 0);
x_271 = lean_ctor_get(x_264, 1);
lean_inc(x_271);
lean_inc(x_270);
lean_dec(x_264);
lean_inc(x_269);
x_272 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_271, x_257, x_269);
x_273 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_273, 0, x_270);
lean_ctor_set(x_273, 1, x_272);
lean_ctor_set(x_262, 1, x_273);
return x_262;
}
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_274 = lean_ctor_get(x_262, 1);
x_275 = lean_ctor_get(x_262, 0);
lean_inc(x_274);
lean_inc(x_275);
lean_dec(x_262);
x_276 = lean_ctor_get(x_274, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_274, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_278 = x_274;
} else {
 lean_dec_ref(x_274);
 x_278 = lean_box(0);
}
lean_inc(x_275);
x_279 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_277, x_257, x_275);
if (lean_is_scalar(x_278)) {
 x_280 = lean_alloc_ctor(0, 2, 0);
} else {
 x_280 = x_278;
}
lean_ctor_set(x_280, 0, x_276);
lean_ctor_set(x_280, 1, x_279);
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_275);
lean_ctor_set(x_281, 1, x_280);
return x_281;
}
}
else
{
lean_object* x_282; lean_object* x_283; 
lean_dec(x_257);
x_282 = lean_ctor_get(x_261, 0);
lean_inc(x_282);
lean_dec(x_261);
x_283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_242);
return x_283;
}
}
}
}
block_253:
{
lean_object* x_244; lean_object* x_245; uint8_t x_246; 
lean_dec(x_243);
x_244 = lean_unsigned_to_nat(0u);
x_245 = l_Array_umapMAux___main___at_Lean_MetavarContext_InstantiateExprMVars_main___main___spec__3(x_244, x_2, x_242);
x_246 = !lean_is_exclusive(x_245);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; 
x_247 = lean_ctor_get(x_245, 0);
x_248 = l_Lean_mkAppRev(x_241, x_247);
lean_dec(x_247);
lean_ctor_set(x_245, 0, x_248);
return x_245;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_249 = lean_ctor_get(x_245, 0);
x_250 = lean_ctor_get(x_245, 1);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_245);
x_251 = l_Lean_mkAppRev(x_241, x_249);
lean_dec(x_249);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_250);
return x_252;
}
}
}
}
case 5:
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_299 = lean_ctor_get(x_1, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_1, 1);
lean_inc(x_300);
lean_dec(x_1);
x_301 = lean_array_push(x_2, x_300);
x_1 = x_299;
x_2 = x_301;
goto _start;
}
case 6:
{
uint8_t x_303; lean_object* x_304; lean_object* x_305; uint8_t x_348; 
x_303 = l_Lean_Expr_isMVar(x_1);
x_348 = l_Lean_Expr_hasMVar(x_1);
if (x_348 == 0)
{
x_304 = x_1;
x_305 = x_3;
goto block_347;
}
else
{
lean_object* x_349; lean_object* x_350; 
x_349 = lean_ctor_get(x_3, 1);
lean_inc(x_349);
x_350 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_349, x_1);
lean_dec(x_349);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; uint8_t x_354; 
lean_inc(x_1);
x_351 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_1, x_3);
x_352 = lean_ctor_get(x_351, 1);
lean_inc(x_352);
x_353 = lean_ctor_get(x_351, 0);
lean_inc(x_353);
lean_dec(x_351);
x_354 = !lean_is_exclusive(x_352);
if (x_354 == 0)
{
lean_object* x_355; lean_object* x_356; 
x_355 = lean_ctor_get(x_352, 1);
lean_inc(x_353);
x_356 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_355, x_1, x_353);
lean_ctor_set(x_352, 1, x_356);
x_304 = x_353;
x_305 = x_352;
goto block_347;
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_357 = lean_ctor_get(x_352, 0);
x_358 = lean_ctor_get(x_352, 1);
lean_inc(x_358);
lean_inc(x_357);
lean_dec(x_352);
lean_inc(x_353);
x_359 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_358, x_1, x_353);
x_360 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_360, 0, x_357);
lean_ctor_set(x_360, 1, x_359);
x_304 = x_353;
x_305 = x_360;
goto block_347;
}
}
else
{
lean_object* x_361; 
lean_dec(x_1);
x_361 = lean_ctor_get(x_350, 0);
lean_inc(x_361);
lean_dec(x_350);
x_304 = x_361;
x_305 = x_3;
goto block_347;
}
}
block_347:
{
lean_object* x_306; 
if (x_303 == 0)
{
lean_object* x_317; 
x_317 = lean_box(0);
x_306 = x_317;
goto block_316;
}
else
{
uint8_t x_318; 
x_318 = l_Lean_Expr_isLambda(x_304);
if (x_318 == 0)
{
lean_object* x_319; 
x_319 = lean_box(0);
x_306 = x_319;
goto block_316;
}
else
{
lean_object* x_320; uint8_t x_321; 
x_320 = l_Lean_Expr_betaRev(x_304, x_2);
lean_dec(x_304);
x_321 = l_Lean_Expr_hasMVar(x_320);
if (x_321 == 0)
{
lean_object* x_322; 
x_322 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_305);
return x_322;
}
else
{
lean_object* x_323; lean_object* x_324; 
x_323 = lean_ctor_get(x_305, 1);
lean_inc(x_323);
x_324 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_323, x_320);
lean_dec(x_323);
if (lean_obj_tag(x_324) == 0)
{
lean_object* x_325; uint8_t x_326; 
lean_inc(x_320);
x_325 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_320, x_305);
x_326 = !lean_is_exclusive(x_325);
if (x_326 == 0)
{
lean_object* x_327; uint8_t x_328; 
x_327 = lean_ctor_get(x_325, 1);
x_328 = !lean_is_exclusive(x_327);
if (x_328 == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_329 = lean_ctor_get(x_325, 0);
x_330 = lean_ctor_get(x_327, 1);
lean_inc(x_329);
x_331 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_330, x_320, x_329);
lean_ctor_set(x_327, 1, x_331);
return x_325;
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_332 = lean_ctor_get(x_325, 0);
x_333 = lean_ctor_get(x_327, 0);
x_334 = lean_ctor_get(x_327, 1);
lean_inc(x_334);
lean_inc(x_333);
lean_dec(x_327);
lean_inc(x_332);
x_335 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_334, x_320, x_332);
x_336 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_336, 0, x_333);
lean_ctor_set(x_336, 1, x_335);
lean_ctor_set(x_325, 1, x_336);
return x_325;
}
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_337 = lean_ctor_get(x_325, 1);
x_338 = lean_ctor_get(x_325, 0);
lean_inc(x_337);
lean_inc(x_338);
lean_dec(x_325);
x_339 = lean_ctor_get(x_337, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_337, 1);
lean_inc(x_340);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 x_341 = x_337;
} else {
 lean_dec_ref(x_337);
 x_341 = lean_box(0);
}
lean_inc(x_338);
x_342 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_340, x_320, x_338);
if (lean_is_scalar(x_341)) {
 x_343 = lean_alloc_ctor(0, 2, 0);
} else {
 x_343 = x_341;
}
lean_ctor_set(x_343, 0, x_339);
lean_ctor_set(x_343, 1, x_342);
x_344 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_344, 0, x_338);
lean_ctor_set(x_344, 1, x_343);
return x_344;
}
}
else
{
lean_object* x_345; lean_object* x_346; 
lean_dec(x_320);
x_345 = lean_ctor_get(x_324, 0);
lean_inc(x_345);
lean_dec(x_324);
x_346 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_346, 0, x_345);
lean_ctor_set(x_346, 1, x_305);
return x_346;
}
}
}
}
block_316:
{
lean_object* x_307; lean_object* x_308; uint8_t x_309; 
lean_dec(x_306);
x_307 = lean_unsigned_to_nat(0u);
x_308 = l_Array_umapMAux___main___at_Lean_MetavarContext_InstantiateExprMVars_main___main___spec__3(x_307, x_2, x_305);
x_309 = !lean_is_exclusive(x_308);
if (x_309 == 0)
{
lean_object* x_310; lean_object* x_311; 
x_310 = lean_ctor_get(x_308, 0);
x_311 = l_Lean_mkAppRev(x_304, x_310);
lean_dec(x_310);
lean_ctor_set(x_308, 0, x_311);
return x_308;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_312 = lean_ctor_get(x_308, 0);
x_313 = lean_ctor_get(x_308, 1);
lean_inc(x_313);
lean_inc(x_312);
lean_dec(x_308);
x_314 = l_Lean_mkAppRev(x_304, x_312);
lean_dec(x_312);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_313);
return x_315;
}
}
}
}
case 7:
{
uint8_t x_362; lean_object* x_363; lean_object* x_364; uint8_t x_407; 
x_362 = l_Lean_Expr_isMVar(x_1);
x_407 = l_Lean_Expr_hasMVar(x_1);
if (x_407 == 0)
{
x_363 = x_1;
x_364 = x_3;
goto block_406;
}
else
{
lean_object* x_408; lean_object* x_409; 
x_408 = lean_ctor_get(x_3, 1);
lean_inc(x_408);
x_409 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_408, x_1);
lean_dec(x_408);
if (lean_obj_tag(x_409) == 0)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; uint8_t x_413; 
lean_inc(x_1);
x_410 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_1, x_3);
x_411 = lean_ctor_get(x_410, 1);
lean_inc(x_411);
x_412 = lean_ctor_get(x_410, 0);
lean_inc(x_412);
lean_dec(x_410);
x_413 = !lean_is_exclusive(x_411);
if (x_413 == 0)
{
lean_object* x_414; lean_object* x_415; 
x_414 = lean_ctor_get(x_411, 1);
lean_inc(x_412);
x_415 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_414, x_1, x_412);
lean_ctor_set(x_411, 1, x_415);
x_363 = x_412;
x_364 = x_411;
goto block_406;
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_416 = lean_ctor_get(x_411, 0);
x_417 = lean_ctor_get(x_411, 1);
lean_inc(x_417);
lean_inc(x_416);
lean_dec(x_411);
lean_inc(x_412);
x_418 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_417, x_1, x_412);
x_419 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_419, 0, x_416);
lean_ctor_set(x_419, 1, x_418);
x_363 = x_412;
x_364 = x_419;
goto block_406;
}
}
else
{
lean_object* x_420; 
lean_dec(x_1);
x_420 = lean_ctor_get(x_409, 0);
lean_inc(x_420);
lean_dec(x_409);
x_363 = x_420;
x_364 = x_3;
goto block_406;
}
}
block_406:
{
lean_object* x_365; 
if (x_362 == 0)
{
lean_object* x_376; 
x_376 = lean_box(0);
x_365 = x_376;
goto block_375;
}
else
{
uint8_t x_377; 
x_377 = l_Lean_Expr_isLambda(x_363);
if (x_377 == 0)
{
lean_object* x_378; 
x_378 = lean_box(0);
x_365 = x_378;
goto block_375;
}
else
{
lean_object* x_379; uint8_t x_380; 
x_379 = l_Lean_Expr_betaRev(x_363, x_2);
lean_dec(x_363);
x_380 = l_Lean_Expr_hasMVar(x_379);
if (x_380 == 0)
{
lean_object* x_381; 
x_381 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_381, 0, x_379);
lean_ctor_set(x_381, 1, x_364);
return x_381;
}
else
{
lean_object* x_382; lean_object* x_383; 
x_382 = lean_ctor_get(x_364, 1);
lean_inc(x_382);
x_383 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_382, x_379);
lean_dec(x_382);
if (lean_obj_tag(x_383) == 0)
{
lean_object* x_384; uint8_t x_385; 
lean_inc(x_379);
x_384 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_379, x_364);
x_385 = !lean_is_exclusive(x_384);
if (x_385 == 0)
{
lean_object* x_386; uint8_t x_387; 
x_386 = lean_ctor_get(x_384, 1);
x_387 = !lean_is_exclusive(x_386);
if (x_387 == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_388 = lean_ctor_get(x_384, 0);
x_389 = lean_ctor_get(x_386, 1);
lean_inc(x_388);
x_390 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_389, x_379, x_388);
lean_ctor_set(x_386, 1, x_390);
return x_384;
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_391 = lean_ctor_get(x_384, 0);
x_392 = lean_ctor_get(x_386, 0);
x_393 = lean_ctor_get(x_386, 1);
lean_inc(x_393);
lean_inc(x_392);
lean_dec(x_386);
lean_inc(x_391);
x_394 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_393, x_379, x_391);
x_395 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_395, 0, x_392);
lean_ctor_set(x_395, 1, x_394);
lean_ctor_set(x_384, 1, x_395);
return x_384;
}
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_396 = lean_ctor_get(x_384, 1);
x_397 = lean_ctor_get(x_384, 0);
lean_inc(x_396);
lean_inc(x_397);
lean_dec(x_384);
x_398 = lean_ctor_get(x_396, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_396, 1);
lean_inc(x_399);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 lean_ctor_release(x_396, 1);
 x_400 = x_396;
} else {
 lean_dec_ref(x_396);
 x_400 = lean_box(0);
}
lean_inc(x_397);
x_401 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_399, x_379, x_397);
if (lean_is_scalar(x_400)) {
 x_402 = lean_alloc_ctor(0, 2, 0);
} else {
 x_402 = x_400;
}
lean_ctor_set(x_402, 0, x_398);
lean_ctor_set(x_402, 1, x_401);
x_403 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_403, 0, x_397);
lean_ctor_set(x_403, 1, x_402);
return x_403;
}
}
else
{
lean_object* x_404; lean_object* x_405; 
lean_dec(x_379);
x_404 = lean_ctor_get(x_383, 0);
lean_inc(x_404);
lean_dec(x_383);
x_405 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_405, 0, x_404);
lean_ctor_set(x_405, 1, x_364);
return x_405;
}
}
}
}
block_375:
{
lean_object* x_366; lean_object* x_367; uint8_t x_368; 
lean_dec(x_365);
x_366 = lean_unsigned_to_nat(0u);
x_367 = l_Array_umapMAux___main___at_Lean_MetavarContext_InstantiateExprMVars_main___main___spec__3(x_366, x_2, x_364);
x_368 = !lean_is_exclusive(x_367);
if (x_368 == 0)
{
lean_object* x_369; lean_object* x_370; 
x_369 = lean_ctor_get(x_367, 0);
x_370 = l_Lean_mkAppRev(x_363, x_369);
lean_dec(x_369);
lean_ctor_set(x_367, 0, x_370);
return x_367;
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_371 = lean_ctor_get(x_367, 0);
x_372 = lean_ctor_get(x_367, 1);
lean_inc(x_372);
lean_inc(x_371);
lean_dec(x_367);
x_373 = l_Lean_mkAppRev(x_363, x_371);
lean_dec(x_371);
x_374 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_374, 0, x_373);
lean_ctor_set(x_374, 1, x_372);
return x_374;
}
}
}
}
case 8:
{
uint8_t x_421; lean_object* x_422; lean_object* x_423; uint8_t x_466; 
x_421 = l_Lean_Expr_isMVar(x_1);
x_466 = l_Lean_Expr_hasMVar(x_1);
if (x_466 == 0)
{
x_422 = x_1;
x_423 = x_3;
goto block_465;
}
else
{
lean_object* x_467; lean_object* x_468; 
x_467 = lean_ctor_get(x_3, 1);
lean_inc(x_467);
x_468 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_467, x_1);
lean_dec(x_467);
if (lean_obj_tag(x_468) == 0)
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; uint8_t x_472; 
lean_inc(x_1);
x_469 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_1, x_3);
x_470 = lean_ctor_get(x_469, 1);
lean_inc(x_470);
x_471 = lean_ctor_get(x_469, 0);
lean_inc(x_471);
lean_dec(x_469);
x_472 = !lean_is_exclusive(x_470);
if (x_472 == 0)
{
lean_object* x_473; lean_object* x_474; 
x_473 = lean_ctor_get(x_470, 1);
lean_inc(x_471);
x_474 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_473, x_1, x_471);
lean_ctor_set(x_470, 1, x_474);
x_422 = x_471;
x_423 = x_470;
goto block_465;
}
else
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_475 = lean_ctor_get(x_470, 0);
x_476 = lean_ctor_get(x_470, 1);
lean_inc(x_476);
lean_inc(x_475);
lean_dec(x_470);
lean_inc(x_471);
x_477 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_476, x_1, x_471);
x_478 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_478, 0, x_475);
lean_ctor_set(x_478, 1, x_477);
x_422 = x_471;
x_423 = x_478;
goto block_465;
}
}
else
{
lean_object* x_479; 
lean_dec(x_1);
x_479 = lean_ctor_get(x_468, 0);
lean_inc(x_479);
lean_dec(x_468);
x_422 = x_479;
x_423 = x_3;
goto block_465;
}
}
block_465:
{
lean_object* x_424; 
if (x_421 == 0)
{
lean_object* x_435; 
x_435 = lean_box(0);
x_424 = x_435;
goto block_434;
}
else
{
uint8_t x_436; 
x_436 = l_Lean_Expr_isLambda(x_422);
if (x_436 == 0)
{
lean_object* x_437; 
x_437 = lean_box(0);
x_424 = x_437;
goto block_434;
}
else
{
lean_object* x_438; uint8_t x_439; 
x_438 = l_Lean_Expr_betaRev(x_422, x_2);
lean_dec(x_422);
x_439 = l_Lean_Expr_hasMVar(x_438);
if (x_439 == 0)
{
lean_object* x_440; 
x_440 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_440, 0, x_438);
lean_ctor_set(x_440, 1, x_423);
return x_440;
}
else
{
lean_object* x_441; lean_object* x_442; 
x_441 = lean_ctor_get(x_423, 1);
lean_inc(x_441);
x_442 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_441, x_438);
lean_dec(x_441);
if (lean_obj_tag(x_442) == 0)
{
lean_object* x_443; uint8_t x_444; 
lean_inc(x_438);
x_443 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_438, x_423);
x_444 = !lean_is_exclusive(x_443);
if (x_444 == 0)
{
lean_object* x_445; uint8_t x_446; 
x_445 = lean_ctor_get(x_443, 1);
x_446 = !lean_is_exclusive(x_445);
if (x_446 == 0)
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_447 = lean_ctor_get(x_443, 0);
x_448 = lean_ctor_get(x_445, 1);
lean_inc(x_447);
x_449 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_448, x_438, x_447);
lean_ctor_set(x_445, 1, x_449);
return x_443;
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_450 = lean_ctor_get(x_443, 0);
x_451 = lean_ctor_get(x_445, 0);
x_452 = lean_ctor_get(x_445, 1);
lean_inc(x_452);
lean_inc(x_451);
lean_dec(x_445);
lean_inc(x_450);
x_453 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_452, x_438, x_450);
x_454 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_454, 0, x_451);
lean_ctor_set(x_454, 1, x_453);
lean_ctor_set(x_443, 1, x_454);
return x_443;
}
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_455 = lean_ctor_get(x_443, 1);
x_456 = lean_ctor_get(x_443, 0);
lean_inc(x_455);
lean_inc(x_456);
lean_dec(x_443);
x_457 = lean_ctor_get(x_455, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_455, 1);
lean_inc(x_458);
if (lean_is_exclusive(x_455)) {
 lean_ctor_release(x_455, 0);
 lean_ctor_release(x_455, 1);
 x_459 = x_455;
} else {
 lean_dec_ref(x_455);
 x_459 = lean_box(0);
}
lean_inc(x_456);
x_460 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_458, x_438, x_456);
if (lean_is_scalar(x_459)) {
 x_461 = lean_alloc_ctor(0, 2, 0);
} else {
 x_461 = x_459;
}
lean_ctor_set(x_461, 0, x_457);
lean_ctor_set(x_461, 1, x_460);
x_462 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_462, 0, x_456);
lean_ctor_set(x_462, 1, x_461);
return x_462;
}
}
else
{
lean_object* x_463; lean_object* x_464; 
lean_dec(x_438);
x_463 = lean_ctor_get(x_442, 0);
lean_inc(x_463);
lean_dec(x_442);
x_464 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_464, 0, x_463);
lean_ctor_set(x_464, 1, x_423);
return x_464;
}
}
}
}
block_434:
{
lean_object* x_425; lean_object* x_426; uint8_t x_427; 
lean_dec(x_424);
x_425 = lean_unsigned_to_nat(0u);
x_426 = l_Array_umapMAux___main___at_Lean_MetavarContext_InstantiateExprMVars_main___main___spec__3(x_425, x_2, x_423);
x_427 = !lean_is_exclusive(x_426);
if (x_427 == 0)
{
lean_object* x_428; lean_object* x_429; 
x_428 = lean_ctor_get(x_426, 0);
x_429 = l_Lean_mkAppRev(x_422, x_428);
lean_dec(x_428);
lean_ctor_set(x_426, 0, x_429);
return x_426;
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_430 = lean_ctor_get(x_426, 0);
x_431 = lean_ctor_get(x_426, 1);
lean_inc(x_431);
lean_inc(x_430);
lean_dec(x_426);
x_432 = l_Lean_mkAppRev(x_422, x_430);
lean_dec(x_430);
x_433 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_433, 0, x_432);
lean_ctor_set(x_433, 1, x_431);
return x_433;
}
}
}
}
case 9:
{
uint8_t x_480; lean_object* x_481; lean_object* x_482; uint8_t x_525; 
x_480 = l_Lean_Expr_isMVar(x_1);
x_525 = l_Lean_Expr_hasMVar(x_1);
if (x_525 == 0)
{
x_481 = x_1;
x_482 = x_3;
goto block_524;
}
else
{
lean_object* x_526; lean_object* x_527; 
x_526 = lean_ctor_get(x_3, 1);
lean_inc(x_526);
x_527 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_526, x_1);
lean_dec(x_526);
if (lean_obj_tag(x_527) == 0)
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; uint8_t x_531; 
lean_inc(x_1);
x_528 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_1, x_3);
x_529 = lean_ctor_get(x_528, 1);
lean_inc(x_529);
x_530 = lean_ctor_get(x_528, 0);
lean_inc(x_530);
lean_dec(x_528);
x_531 = !lean_is_exclusive(x_529);
if (x_531 == 0)
{
lean_object* x_532; lean_object* x_533; 
x_532 = lean_ctor_get(x_529, 1);
lean_inc(x_530);
x_533 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_532, x_1, x_530);
lean_ctor_set(x_529, 1, x_533);
x_481 = x_530;
x_482 = x_529;
goto block_524;
}
else
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; 
x_534 = lean_ctor_get(x_529, 0);
x_535 = lean_ctor_get(x_529, 1);
lean_inc(x_535);
lean_inc(x_534);
lean_dec(x_529);
lean_inc(x_530);
x_536 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_535, x_1, x_530);
x_537 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_537, 0, x_534);
lean_ctor_set(x_537, 1, x_536);
x_481 = x_530;
x_482 = x_537;
goto block_524;
}
}
else
{
lean_object* x_538; 
lean_dec(x_1);
x_538 = lean_ctor_get(x_527, 0);
lean_inc(x_538);
lean_dec(x_527);
x_481 = x_538;
x_482 = x_3;
goto block_524;
}
}
block_524:
{
lean_object* x_483; 
if (x_480 == 0)
{
lean_object* x_494; 
x_494 = lean_box(0);
x_483 = x_494;
goto block_493;
}
else
{
uint8_t x_495; 
x_495 = l_Lean_Expr_isLambda(x_481);
if (x_495 == 0)
{
lean_object* x_496; 
x_496 = lean_box(0);
x_483 = x_496;
goto block_493;
}
else
{
lean_object* x_497; uint8_t x_498; 
x_497 = l_Lean_Expr_betaRev(x_481, x_2);
lean_dec(x_481);
x_498 = l_Lean_Expr_hasMVar(x_497);
if (x_498 == 0)
{
lean_object* x_499; 
x_499 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_499, 0, x_497);
lean_ctor_set(x_499, 1, x_482);
return x_499;
}
else
{
lean_object* x_500; lean_object* x_501; 
x_500 = lean_ctor_get(x_482, 1);
lean_inc(x_500);
x_501 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_500, x_497);
lean_dec(x_500);
if (lean_obj_tag(x_501) == 0)
{
lean_object* x_502; uint8_t x_503; 
lean_inc(x_497);
x_502 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_497, x_482);
x_503 = !lean_is_exclusive(x_502);
if (x_503 == 0)
{
lean_object* x_504; uint8_t x_505; 
x_504 = lean_ctor_get(x_502, 1);
x_505 = !lean_is_exclusive(x_504);
if (x_505 == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; 
x_506 = lean_ctor_get(x_502, 0);
x_507 = lean_ctor_get(x_504, 1);
lean_inc(x_506);
x_508 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_507, x_497, x_506);
lean_ctor_set(x_504, 1, x_508);
return x_502;
}
else
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; 
x_509 = lean_ctor_get(x_502, 0);
x_510 = lean_ctor_get(x_504, 0);
x_511 = lean_ctor_get(x_504, 1);
lean_inc(x_511);
lean_inc(x_510);
lean_dec(x_504);
lean_inc(x_509);
x_512 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_511, x_497, x_509);
x_513 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_513, 0, x_510);
lean_ctor_set(x_513, 1, x_512);
lean_ctor_set(x_502, 1, x_513);
return x_502;
}
}
else
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; 
x_514 = lean_ctor_get(x_502, 1);
x_515 = lean_ctor_get(x_502, 0);
lean_inc(x_514);
lean_inc(x_515);
lean_dec(x_502);
x_516 = lean_ctor_get(x_514, 0);
lean_inc(x_516);
x_517 = lean_ctor_get(x_514, 1);
lean_inc(x_517);
if (lean_is_exclusive(x_514)) {
 lean_ctor_release(x_514, 0);
 lean_ctor_release(x_514, 1);
 x_518 = x_514;
} else {
 lean_dec_ref(x_514);
 x_518 = lean_box(0);
}
lean_inc(x_515);
x_519 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_517, x_497, x_515);
if (lean_is_scalar(x_518)) {
 x_520 = lean_alloc_ctor(0, 2, 0);
} else {
 x_520 = x_518;
}
lean_ctor_set(x_520, 0, x_516);
lean_ctor_set(x_520, 1, x_519);
x_521 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_521, 0, x_515);
lean_ctor_set(x_521, 1, x_520);
return x_521;
}
}
else
{
lean_object* x_522; lean_object* x_523; 
lean_dec(x_497);
x_522 = lean_ctor_get(x_501, 0);
lean_inc(x_522);
lean_dec(x_501);
x_523 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_523, 0, x_522);
lean_ctor_set(x_523, 1, x_482);
return x_523;
}
}
}
}
block_493:
{
lean_object* x_484; lean_object* x_485; uint8_t x_486; 
lean_dec(x_483);
x_484 = lean_unsigned_to_nat(0u);
x_485 = l_Array_umapMAux___main___at_Lean_MetavarContext_InstantiateExprMVars_main___main___spec__3(x_484, x_2, x_482);
x_486 = !lean_is_exclusive(x_485);
if (x_486 == 0)
{
lean_object* x_487; lean_object* x_488; 
x_487 = lean_ctor_get(x_485, 0);
x_488 = l_Lean_mkAppRev(x_481, x_487);
lean_dec(x_487);
lean_ctor_set(x_485, 0, x_488);
return x_485;
}
else
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; 
x_489 = lean_ctor_get(x_485, 0);
x_490 = lean_ctor_get(x_485, 1);
lean_inc(x_490);
lean_inc(x_489);
lean_dec(x_485);
x_491 = l_Lean_mkAppRev(x_481, x_489);
lean_dec(x_489);
x_492 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_492, 0, x_491);
lean_ctor_set(x_492, 1, x_490);
return x_492;
}
}
}
}
case 10:
{
uint8_t x_539; lean_object* x_540; lean_object* x_541; uint8_t x_584; 
x_539 = l_Lean_Expr_isMVar(x_1);
x_584 = l_Lean_Expr_hasMVar(x_1);
if (x_584 == 0)
{
x_540 = x_1;
x_541 = x_3;
goto block_583;
}
else
{
lean_object* x_585; lean_object* x_586; 
x_585 = lean_ctor_get(x_3, 1);
lean_inc(x_585);
x_586 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_585, x_1);
lean_dec(x_585);
if (lean_obj_tag(x_586) == 0)
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; uint8_t x_590; 
lean_inc(x_1);
x_587 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_1, x_3);
x_588 = lean_ctor_get(x_587, 1);
lean_inc(x_588);
x_589 = lean_ctor_get(x_587, 0);
lean_inc(x_589);
lean_dec(x_587);
x_590 = !lean_is_exclusive(x_588);
if (x_590 == 0)
{
lean_object* x_591; lean_object* x_592; 
x_591 = lean_ctor_get(x_588, 1);
lean_inc(x_589);
x_592 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_591, x_1, x_589);
lean_ctor_set(x_588, 1, x_592);
x_540 = x_589;
x_541 = x_588;
goto block_583;
}
else
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; 
x_593 = lean_ctor_get(x_588, 0);
x_594 = lean_ctor_get(x_588, 1);
lean_inc(x_594);
lean_inc(x_593);
lean_dec(x_588);
lean_inc(x_589);
x_595 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_594, x_1, x_589);
x_596 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_596, 0, x_593);
lean_ctor_set(x_596, 1, x_595);
x_540 = x_589;
x_541 = x_596;
goto block_583;
}
}
else
{
lean_object* x_597; 
lean_dec(x_1);
x_597 = lean_ctor_get(x_586, 0);
lean_inc(x_597);
lean_dec(x_586);
x_540 = x_597;
x_541 = x_3;
goto block_583;
}
}
block_583:
{
lean_object* x_542; 
if (x_539 == 0)
{
lean_object* x_553; 
x_553 = lean_box(0);
x_542 = x_553;
goto block_552;
}
else
{
uint8_t x_554; 
x_554 = l_Lean_Expr_isLambda(x_540);
if (x_554 == 0)
{
lean_object* x_555; 
x_555 = lean_box(0);
x_542 = x_555;
goto block_552;
}
else
{
lean_object* x_556; uint8_t x_557; 
x_556 = l_Lean_Expr_betaRev(x_540, x_2);
lean_dec(x_540);
x_557 = l_Lean_Expr_hasMVar(x_556);
if (x_557 == 0)
{
lean_object* x_558; 
x_558 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_558, 0, x_556);
lean_ctor_set(x_558, 1, x_541);
return x_558;
}
else
{
lean_object* x_559; lean_object* x_560; 
x_559 = lean_ctor_get(x_541, 1);
lean_inc(x_559);
x_560 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_559, x_556);
lean_dec(x_559);
if (lean_obj_tag(x_560) == 0)
{
lean_object* x_561; uint8_t x_562; 
lean_inc(x_556);
x_561 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_556, x_541);
x_562 = !lean_is_exclusive(x_561);
if (x_562 == 0)
{
lean_object* x_563; uint8_t x_564; 
x_563 = lean_ctor_get(x_561, 1);
x_564 = !lean_is_exclusive(x_563);
if (x_564 == 0)
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; 
x_565 = lean_ctor_get(x_561, 0);
x_566 = lean_ctor_get(x_563, 1);
lean_inc(x_565);
x_567 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_566, x_556, x_565);
lean_ctor_set(x_563, 1, x_567);
return x_561;
}
else
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; 
x_568 = lean_ctor_get(x_561, 0);
x_569 = lean_ctor_get(x_563, 0);
x_570 = lean_ctor_get(x_563, 1);
lean_inc(x_570);
lean_inc(x_569);
lean_dec(x_563);
lean_inc(x_568);
x_571 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_570, x_556, x_568);
x_572 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_572, 0, x_569);
lean_ctor_set(x_572, 1, x_571);
lean_ctor_set(x_561, 1, x_572);
return x_561;
}
}
else
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; 
x_573 = lean_ctor_get(x_561, 1);
x_574 = lean_ctor_get(x_561, 0);
lean_inc(x_573);
lean_inc(x_574);
lean_dec(x_561);
x_575 = lean_ctor_get(x_573, 0);
lean_inc(x_575);
x_576 = lean_ctor_get(x_573, 1);
lean_inc(x_576);
if (lean_is_exclusive(x_573)) {
 lean_ctor_release(x_573, 0);
 lean_ctor_release(x_573, 1);
 x_577 = x_573;
} else {
 lean_dec_ref(x_573);
 x_577 = lean_box(0);
}
lean_inc(x_574);
x_578 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_576, x_556, x_574);
if (lean_is_scalar(x_577)) {
 x_579 = lean_alloc_ctor(0, 2, 0);
} else {
 x_579 = x_577;
}
lean_ctor_set(x_579, 0, x_575);
lean_ctor_set(x_579, 1, x_578);
x_580 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_580, 0, x_574);
lean_ctor_set(x_580, 1, x_579);
return x_580;
}
}
else
{
lean_object* x_581; lean_object* x_582; 
lean_dec(x_556);
x_581 = lean_ctor_get(x_560, 0);
lean_inc(x_581);
lean_dec(x_560);
x_582 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_582, 0, x_581);
lean_ctor_set(x_582, 1, x_541);
return x_582;
}
}
}
}
block_552:
{
lean_object* x_543; lean_object* x_544; uint8_t x_545; 
lean_dec(x_542);
x_543 = lean_unsigned_to_nat(0u);
x_544 = l_Array_umapMAux___main___at_Lean_MetavarContext_InstantiateExprMVars_main___main___spec__3(x_543, x_2, x_541);
x_545 = !lean_is_exclusive(x_544);
if (x_545 == 0)
{
lean_object* x_546; lean_object* x_547; 
x_546 = lean_ctor_get(x_544, 0);
x_547 = l_Lean_mkAppRev(x_540, x_546);
lean_dec(x_546);
lean_ctor_set(x_544, 0, x_547);
return x_544;
}
else
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; 
x_548 = lean_ctor_get(x_544, 0);
x_549 = lean_ctor_get(x_544, 1);
lean_inc(x_549);
lean_inc(x_548);
lean_dec(x_544);
x_550 = l_Lean_mkAppRev(x_540, x_548);
lean_dec(x_548);
x_551 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_551, 0, x_550);
lean_ctor_set(x_551, 1, x_549);
return x_551;
}
}
}
}
case 11:
{
uint8_t x_598; lean_object* x_599; lean_object* x_600; uint8_t x_643; 
x_598 = l_Lean_Expr_isMVar(x_1);
x_643 = l_Lean_Expr_hasMVar(x_1);
if (x_643 == 0)
{
x_599 = x_1;
x_600 = x_3;
goto block_642;
}
else
{
lean_object* x_644; lean_object* x_645; 
x_644 = lean_ctor_get(x_3, 1);
lean_inc(x_644);
x_645 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_644, x_1);
lean_dec(x_644);
if (lean_obj_tag(x_645) == 0)
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; uint8_t x_649; 
lean_inc(x_1);
x_646 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_1, x_3);
x_647 = lean_ctor_get(x_646, 1);
lean_inc(x_647);
x_648 = lean_ctor_get(x_646, 0);
lean_inc(x_648);
lean_dec(x_646);
x_649 = !lean_is_exclusive(x_647);
if (x_649 == 0)
{
lean_object* x_650; lean_object* x_651; 
x_650 = lean_ctor_get(x_647, 1);
lean_inc(x_648);
x_651 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_650, x_1, x_648);
lean_ctor_set(x_647, 1, x_651);
x_599 = x_648;
x_600 = x_647;
goto block_642;
}
else
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; 
x_652 = lean_ctor_get(x_647, 0);
x_653 = lean_ctor_get(x_647, 1);
lean_inc(x_653);
lean_inc(x_652);
lean_dec(x_647);
lean_inc(x_648);
x_654 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_653, x_1, x_648);
x_655 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_655, 0, x_652);
lean_ctor_set(x_655, 1, x_654);
x_599 = x_648;
x_600 = x_655;
goto block_642;
}
}
else
{
lean_object* x_656; 
lean_dec(x_1);
x_656 = lean_ctor_get(x_645, 0);
lean_inc(x_656);
lean_dec(x_645);
x_599 = x_656;
x_600 = x_3;
goto block_642;
}
}
block_642:
{
lean_object* x_601; 
if (x_598 == 0)
{
lean_object* x_612; 
x_612 = lean_box(0);
x_601 = x_612;
goto block_611;
}
else
{
uint8_t x_613; 
x_613 = l_Lean_Expr_isLambda(x_599);
if (x_613 == 0)
{
lean_object* x_614; 
x_614 = lean_box(0);
x_601 = x_614;
goto block_611;
}
else
{
lean_object* x_615; uint8_t x_616; 
x_615 = l_Lean_Expr_betaRev(x_599, x_2);
lean_dec(x_599);
x_616 = l_Lean_Expr_hasMVar(x_615);
if (x_616 == 0)
{
lean_object* x_617; 
x_617 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_617, 0, x_615);
lean_ctor_set(x_617, 1, x_600);
return x_617;
}
else
{
lean_object* x_618; lean_object* x_619; 
x_618 = lean_ctor_get(x_600, 1);
lean_inc(x_618);
x_619 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_618, x_615);
lean_dec(x_618);
if (lean_obj_tag(x_619) == 0)
{
lean_object* x_620; uint8_t x_621; 
lean_inc(x_615);
x_620 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_615, x_600);
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
x_626 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_625, x_615, x_624);
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
x_630 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_629, x_615, x_627);
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
x_637 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_635, x_615, x_633);
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
lean_dec(x_615);
x_640 = lean_ctor_get(x_619, 0);
lean_inc(x_640);
lean_dec(x_619);
x_641 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_641, 0, x_640);
lean_ctor_set(x_641, 1, x_600);
return x_641;
}
}
}
}
block_611:
{
lean_object* x_602; lean_object* x_603; uint8_t x_604; 
lean_dec(x_601);
x_602 = lean_unsigned_to_nat(0u);
x_603 = l_Array_umapMAux___main___at_Lean_MetavarContext_InstantiateExprMVars_main___main___spec__3(x_602, x_2, x_600);
x_604 = !lean_is_exclusive(x_603);
if (x_604 == 0)
{
lean_object* x_605; lean_object* x_606; 
x_605 = lean_ctor_get(x_603, 0);
x_606 = l_Lean_mkAppRev(x_599, x_605);
lean_dec(x_605);
lean_ctor_set(x_603, 0, x_606);
return x_603;
}
else
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; 
x_607 = lean_ctor_get(x_603, 0);
x_608 = lean_ctor_get(x_603, 1);
lean_inc(x_608);
lean_inc(x_607);
lean_dec(x_603);
x_609 = l_Lean_mkAppRev(x_599, x_607);
lean_dec(x_607);
x_610 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_610, 0, x_609);
lean_ctor_set(x_610, 1, x_608);
return x_610;
}
}
}
}
default: 
{
uint8_t x_657; lean_object* x_658; lean_object* x_659; uint8_t x_702; 
x_657 = l_Lean_Expr_isMVar(x_1);
x_702 = l_Lean_Expr_hasMVar(x_1);
if (x_702 == 0)
{
x_658 = x_1;
x_659 = x_3;
goto block_701;
}
else
{
lean_object* x_703; lean_object* x_704; 
x_703 = lean_ctor_get(x_3, 1);
lean_inc(x_703);
x_704 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_703, x_1);
lean_dec(x_703);
if (lean_obj_tag(x_704) == 0)
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; uint8_t x_708; 
lean_inc(x_1);
x_705 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_1, x_3);
x_706 = lean_ctor_get(x_705, 1);
lean_inc(x_706);
x_707 = lean_ctor_get(x_705, 0);
lean_inc(x_707);
lean_dec(x_705);
x_708 = !lean_is_exclusive(x_706);
if (x_708 == 0)
{
lean_object* x_709; lean_object* x_710; 
x_709 = lean_ctor_get(x_706, 1);
lean_inc(x_707);
x_710 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_709, x_1, x_707);
lean_ctor_set(x_706, 1, x_710);
x_658 = x_707;
x_659 = x_706;
goto block_701;
}
else
{
lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; 
x_711 = lean_ctor_get(x_706, 0);
x_712 = lean_ctor_get(x_706, 1);
lean_inc(x_712);
lean_inc(x_711);
lean_dec(x_706);
lean_inc(x_707);
x_713 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_712, x_1, x_707);
x_714 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_714, 0, x_711);
lean_ctor_set(x_714, 1, x_713);
x_658 = x_707;
x_659 = x_714;
goto block_701;
}
}
else
{
lean_object* x_715; 
lean_dec(x_1);
x_715 = lean_ctor_get(x_704, 0);
lean_inc(x_715);
lean_dec(x_704);
x_658 = x_715;
x_659 = x_3;
goto block_701;
}
}
block_701:
{
lean_object* x_660; 
if (x_657 == 0)
{
lean_object* x_671; 
x_671 = lean_box(0);
x_660 = x_671;
goto block_670;
}
else
{
uint8_t x_672; 
x_672 = l_Lean_Expr_isLambda(x_658);
if (x_672 == 0)
{
lean_object* x_673; 
x_673 = lean_box(0);
x_660 = x_673;
goto block_670;
}
else
{
lean_object* x_674; uint8_t x_675; 
x_674 = l_Lean_Expr_betaRev(x_658, x_2);
lean_dec(x_658);
x_675 = l_Lean_Expr_hasMVar(x_674);
if (x_675 == 0)
{
lean_object* x_676; 
x_676 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_676, 0, x_674);
lean_ctor_set(x_676, 1, x_659);
return x_676;
}
else
{
lean_object* x_677; lean_object* x_678; 
x_677 = lean_ctor_get(x_659, 1);
lean_inc(x_677);
x_678 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_677, x_674);
lean_dec(x_677);
if (lean_obj_tag(x_678) == 0)
{
lean_object* x_679; uint8_t x_680; 
lean_inc(x_674);
x_679 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_674, x_659);
x_680 = !lean_is_exclusive(x_679);
if (x_680 == 0)
{
lean_object* x_681; uint8_t x_682; 
x_681 = lean_ctor_get(x_679, 1);
x_682 = !lean_is_exclusive(x_681);
if (x_682 == 0)
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; 
x_683 = lean_ctor_get(x_679, 0);
x_684 = lean_ctor_get(x_681, 1);
lean_inc(x_683);
x_685 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_684, x_674, x_683);
lean_ctor_set(x_681, 1, x_685);
return x_679;
}
else
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; 
x_686 = lean_ctor_get(x_679, 0);
x_687 = lean_ctor_get(x_681, 0);
x_688 = lean_ctor_get(x_681, 1);
lean_inc(x_688);
lean_inc(x_687);
lean_dec(x_681);
lean_inc(x_686);
x_689 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_688, x_674, x_686);
x_690 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_690, 0, x_687);
lean_ctor_set(x_690, 1, x_689);
lean_ctor_set(x_679, 1, x_690);
return x_679;
}
}
else
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; 
x_691 = lean_ctor_get(x_679, 1);
x_692 = lean_ctor_get(x_679, 0);
lean_inc(x_691);
lean_inc(x_692);
lean_dec(x_679);
x_693 = lean_ctor_get(x_691, 0);
lean_inc(x_693);
x_694 = lean_ctor_get(x_691, 1);
lean_inc(x_694);
if (lean_is_exclusive(x_691)) {
 lean_ctor_release(x_691, 0);
 lean_ctor_release(x_691, 1);
 x_695 = x_691;
} else {
 lean_dec_ref(x_691);
 x_695 = lean_box(0);
}
lean_inc(x_692);
x_696 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_694, x_674, x_692);
if (lean_is_scalar(x_695)) {
 x_697 = lean_alloc_ctor(0, 2, 0);
} else {
 x_697 = x_695;
}
lean_ctor_set(x_697, 0, x_693);
lean_ctor_set(x_697, 1, x_696);
x_698 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_698, 0, x_692);
lean_ctor_set(x_698, 1, x_697);
return x_698;
}
}
else
{
lean_object* x_699; lean_object* x_700; 
lean_dec(x_674);
x_699 = lean_ctor_get(x_678, 0);
lean_inc(x_699);
lean_dec(x_678);
x_700 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_700, 0, x_699);
lean_ctor_set(x_700, 1, x_659);
return x_700;
}
}
}
}
block_670:
{
lean_object* x_661; lean_object* x_662; uint8_t x_663; 
lean_dec(x_660);
x_661 = lean_unsigned_to_nat(0u);
x_662 = l_Array_umapMAux___main___at_Lean_MetavarContext_InstantiateExprMVars_main___main___spec__3(x_661, x_2, x_659);
x_663 = !lean_is_exclusive(x_662);
if (x_663 == 0)
{
lean_object* x_664; lean_object* x_665; 
x_664 = lean_ctor_get(x_662, 0);
x_665 = l_Lean_mkAppRev(x_658, x_664);
lean_dec(x_664);
lean_ctor_set(x_662, 0, x_665);
return x_662;
}
else
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; 
x_666 = lean_ctor_get(x_662, 0);
x_667 = lean_ctor_get(x_662, 1);
lean_inc(x_667);
lean_inc(x_666);
lean_dec(x_662);
x_668 = l_Lean_mkAppRev(x_658, x_666);
lean_dec(x_666);
x_669 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_669, 0, x_668);
lean_ctor_set(x_669, 1, x_667);
return x_669;
}
}
}
}
}
}
}
lean_object* l_Lean_MetavarContext_InstantiateExprMVars_main___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_15; lean_object* x_16; lean_object* x_24; lean_object* x_25; 
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_2, 1);
lean_inc(x_35);
x_36 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_35, x_1);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
lean_inc(x_33);
lean_inc(x_34);
x_37 = lean_metavar_ctx_get_expr_assignment(x_34, x_33);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
lean_inc(x_33);
x_38 = lean_metavar_ctx_get_delayed_assignment(x_34, x_33);
if (lean_obj_tag(x_38) == 0)
{
lean_dec(x_35);
lean_dec(x_33);
lean_inc(x_1);
x_3 = x_1;
x_4 = x_2;
goto block_14;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_77; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 2);
lean_inc(x_42);
lean_dec(x_39);
x_77 = l_Lean_Expr_hasMVar(x_42);
if (x_77 == 0)
{
lean_dec(x_35);
x_43 = x_42;
x_44 = x_2;
goto block_76;
}
else
{
lean_object* x_78; 
x_78 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_35, x_42);
lean_dec(x_35);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
lean_inc(x_42);
x_79 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_42, x_2);
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
x_84 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_83, x_42, x_81);
lean_ctor_set(x_80, 1, x_84);
x_43 = x_81;
x_44 = x_80;
goto block_76;
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
x_87 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_86, x_42, x_81);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_87);
x_43 = x_81;
x_44 = x_88;
goto block_76;
}
}
else
{
lean_object* x_89; 
lean_dec(x_42);
x_89 = lean_ctor_get(x_78, 0);
lean_inc(x_89);
lean_dec(x_78);
x_43 = x_89;
x_44 = x_2;
goto block_76;
}
}
block_76:
{
uint8_t x_45; 
x_45 = l_Lean_Expr_hasMVar(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_array_get_size(x_41);
x_47 = lean_expr_abstract(x_43, x_41);
lean_inc(x_40);
x_48 = l___private_Init_Lean_MetavarContext_5__instantiateDelayedAux___main___at_Lean_MetavarContext_InstantiateExprMVars_main___main___spec__1(x_40, x_41, x_46, x_47, x_44);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_metavar_ctx_assign_delayed(x_52, x_33, x_40, x_41, x_43);
lean_ctor_set(x_50, 0, x_53);
lean_inc(x_1);
x_3 = x_1;
x_4 = x_50;
goto block_14;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_50, 0);
x_55 = lean_ctor_get(x_50, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_50);
x_56 = lean_metavar_ctx_assign_delayed(x_54, x_33, x_40, x_41, x_43);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
lean_inc(x_1);
x_3 = x_1;
x_4 = x_57;
goto block_14;
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_40);
x_58 = lean_ctor_get(x_48, 1);
lean_inc(x_58);
lean_dec(x_48);
x_59 = lean_ctor_get(x_49, 0);
lean_inc(x_59);
lean_dec(x_49);
x_60 = !lean_is_exclusive(x_58);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_58, 0);
lean_inc(x_33);
x_62 = lean_metavar_ctx_erase_delayed(x_61, x_33);
lean_inc(x_59);
x_63 = lean_metavar_ctx_assign_expr(x_62, x_33, x_59);
lean_ctor_set(x_58, 0, x_63);
x_3 = x_59;
x_4 = x_58;
goto block_14;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_58, 0);
x_65 = lean_ctor_get(x_58, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_58);
lean_inc(x_33);
x_66 = lean_metavar_ctx_erase_delayed(x_64, x_33);
lean_inc(x_59);
x_67 = lean_metavar_ctx_assign_expr(x_66, x_33, x_59);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
x_3 = x_59;
x_4 = x_68;
goto block_14;
}
}
}
else
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_44);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_44, 0);
x_71 = lean_metavar_ctx_assign_delayed(x_70, x_33, x_40, x_41, x_43);
lean_ctor_set(x_44, 0, x_71);
lean_inc(x_1);
x_3 = x_1;
x_4 = x_44;
goto block_14;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_44, 0);
x_73 = lean_ctor_get(x_44, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_44);
x_74 = lean_metavar_ctx_assign_delayed(x_72, x_33, x_40, x_41, x_43);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
lean_inc(x_1);
x_3 = x_1;
x_4 = x_75;
goto block_14;
}
}
}
}
}
else
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_ctor_get(x_37, 0);
lean_inc(x_90);
lean_dec(x_37);
x_91 = l_Lean_Expr_hasMVar(x_90);
if (x_91 == 0)
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_2);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_2, 1);
lean_dec(x_93);
x_94 = lean_ctor_get(x_2, 0);
lean_dec(x_94);
lean_inc(x_90);
x_95 = lean_metavar_ctx_assign_expr(x_34, x_33, x_90);
lean_ctor_set(x_2, 0, x_95);
x_3 = x_90;
x_4 = x_2;
goto block_14;
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_2);
lean_inc(x_90);
x_96 = lean_metavar_ctx_assign_expr(x_34, x_33, x_90);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_35);
x_3 = x_90;
x_4 = x_97;
goto block_14;
}
}
else
{
lean_object* x_98; 
x_98 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_35, x_90);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; uint8_t x_100; 
lean_dec(x_35);
lean_dec(x_34);
lean_inc(x_2);
lean_inc(x_90);
x_99 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_90, x_2);
x_100 = !lean_is_exclusive(x_2);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_101 = lean_ctor_get(x_2, 1);
lean_dec(x_101);
x_102 = lean_ctor_get(x_2, 0);
lean_dec(x_102);
x_103 = lean_ctor_get(x_99, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_99, 1);
lean_inc(x_104);
lean_dec(x_99);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
lean_inc(x_103);
x_107 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_106, x_90, x_103);
lean_inc(x_103);
x_108 = lean_metavar_ctx_assign_expr(x_105, x_33, x_103);
lean_ctor_set(x_2, 1, x_107);
lean_ctor_set(x_2, 0, x_108);
x_3 = x_103;
x_4 = x_2;
goto block_14;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_2);
x_109 = lean_ctor_get(x_99, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_99, 1);
lean_inc(x_110);
lean_dec(x_99);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
lean_inc(x_109);
x_113 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_112, x_90, x_109);
lean_inc(x_109);
x_114 = lean_metavar_ctx_assign_expr(x_111, x_33, x_109);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
x_3 = x_109;
x_4 = x_115;
goto block_14;
}
}
else
{
uint8_t x_116; 
lean_dec(x_90);
x_116 = !lean_is_exclusive(x_2);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_2, 1);
lean_dec(x_117);
x_118 = lean_ctor_get(x_2, 0);
lean_dec(x_118);
x_119 = lean_ctor_get(x_98, 0);
lean_inc(x_119);
lean_dec(x_98);
lean_inc(x_119);
x_120 = lean_metavar_ctx_assign_expr(x_34, x_33, x_119);
lean_ctor_set(x_2, 0, x_120);
x_3 = x_119;
x_4 = x_2;
goto block_14;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_2);
x_121 = lean_ctor_get(x_98, 0);
lean_inc(x_121);
lean_dec(x_98);
lean_inc(x_121);
x_122 = lean_metavar_ctx_assign_expr(x_34, x_33, x_121);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_35);
x_3 = x_121;
x_4 = x_123;
goto block_14;
}
}
}
}
}
else
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_1);
x_124 = lean_ctor_get(x_36, 0);
lean_inc(x_124);
lean_dec(x_36);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_2);
return x_125;
}
}
case 3:
{
lean_object* x_126; uint8_t x_127; 
x_126 = lean_ctor_get(x_1, 0);
lean_inc(x_126);
x_127 = !lean_is_exclusive(x_2);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_128 = lean_ctor_get(x_2, 0);
x_129 = l_Lean_MetavarContext_instantiateLevelMVars___main(x_126, x_128);
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_129, 0);
x_132 = lean_ctor_get(x_129, 1);
lean_ctor_set(x_2, 0, x_132);
x_133 = lean_expr_update_sort(x_1, x_131);
lean_ctor_set(x_129, 1, x_2);
lean_ctor_set(x_129, 0, x_133);
return x_129;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_134 = lean_ctor_get(x_129, 0);
x_135 = lean_ctor_get(x_129, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_129);
lean_ctor_set(x_2, 0, x_135);
x_136 = lean_expr_update_sort(x_1, x_134);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_2);
return x_137;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_138 = lean_ctor_get(x_2, 0);
x_139 = lean_ctor_get(x_2, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_2);
x_140 = l_Lean_MetavarContext_instantiateLevelMVars___main(x_126, x_138);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_143 = x_140;
} else {
 lean_dec_ref(x_140);
 x_143 = lean_box(0);
}
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_139);
x_145 = lean_expr_update_sort(x_1, x_141);
if (lean_is_scalar(x_143)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_143;
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
}
case 4:
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_147 = lean_ctor_get(x_1, 1);
lean_inc(x_147);
x_148 = l_List_mapM___main___at_Lean_MetavarContext_InstantiateExprMVars_main___main___spec__2(x_147, x_2);
x_149 = !lean_is_exclusive(x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_148, 0);
x_151 = lean_expr_update_const(x_1, x_150);
lean_ctor_set(x_148, 0, x_151);
return x_148;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_152 = lean_ctor_get(x_148, 0);
x_153 = lean_ctor_get(x_148, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_148);
x_154 = lean_expr_update_const(x_1, x_152);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_153);
return x_155;
}
}
case 5:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_156 = lean_unsigned_to_nat(0u);
x_157 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_156);
x_158 = lean_mk_empty_array_with_capacity(x_157);
lean_dec(x_157);
x_159 = l___private_Init_Lean_Expr_5__withAppRevAux___main___at_Lean_MetavarContext_InstantiateExprMVars_main___main___spec__4(x_1, x_158, x_2);
return x_159;
}
case 6:
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_190; 
x_160 = lean_ctor_get(x_1, 1);
lean_inc(x_160);
x_161 = lean_ctor_get(x_1, 2);
lean_inc(x_161);
x_190 = l_Lean_Expr_hasMVar(x_160);
if (x_190 == 0)
{
x_162 = x_160;
x_163 = x_2;
goto block_189;
}
else
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_ctor_get(x_2, 1);
lean_inc(x_191);
x_192 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_191, x_160);
lean_dec(x_191);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
lean_inc(x_160);
x_193 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_160, x_2);
x_194 = lean_ctor_get(x_193, 1);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 0);
lean_inc(x_195);
lean_dec(x_193);
x_196 = !lean_is_exclusive(x_194);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_194, 1);
lean_inc(x_195);
x_198 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_197, x_160, x_195);
lean_ctor_set(x_194, 1, x_198);
x_162 = x_195;
x_163 = x_194;
goto block_189;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_199 = lean_ctor_get(x_194, 0);
x_200 = lean_ctor_get(x_194, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_194);
lean_inc(x_195);
x_201 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_200, x_160, x_195);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_201);
x_162 = x_195;
x_163 = x_202;
goto block_189;
}
}
else
{
lean_object* x_203; 
lean_dec(x_160);
x_203 = lean_ctor_get(x_192, 0);
lean_inc(x_203);
lean_dec(x_192);
x_162 = x_203;
x_163 = x_2;
goto block_189;
}
}
block_189:
{
lean_object* x_164; lean_object* x_165; uint8_t x_175; 
x_175 = l_Lean_Expr_hasMVar(x_161);
if (x_175 == 0)
{
x_164 = x_161;
x_165 = x_163;
goto block_174;
}
else
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_163, 1);
lean_inc(x_176);
x_177 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_176, x_161);
lean_dec(x_176);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; 
lean_inc(x_161);
x_178 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_161, x_163);
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 0);
lean_inc(x_180);
lean_dec(x_178);
x_181 = !lean_is_exclusive(x_179);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
x_183 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_182, x_161, x_180);
lean_ctor_set(x_179, 1, x_183);
x_164 = x_180;
x_165 = x_179;
goto block_174;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_ctor_get(x_179, 0);
x_185 = lean_ctor_get(x_179, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_179);
lean_inc(x_180);
x_186 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_185, x_161, x_180);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_186);
x_164 = x_180;
x_165 = x_187;
goto block_174;
}
}
else
{
lean_object* x_188; 
lean_dec(x_161);
x_188 = lean_ctor_get(x_177, 0);
lean_inc(x_188);
lean_dec(x_177);
x_164 = x_188;
x_165 = x_163;
goto block_174;
}
}
block_174:
{
if (lean_obj_tag(x_1) == 6)
{
uint64_t x_166; uint8_t x_167; lean_object* x_168; lean_object* x_169; 
x_166 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_167 = (uint8_t)((x_166 << 24) >> 61);
x_168 = lean_expr_update_lambda(x_1, x_167, x_162, x_164);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_165);
return x_169;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_164);
lean_dec(x_162);
lean_dec(x_1);
x_170 = l_Lean_Expr_Inhabited;
x_171 = l_Lean_Expr_updateLambdaE_x21___closed__1;
x_172 = lean_panic_fn(x_171);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_165);
return x_173;
}
}
}
}
case 7:
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_234; 
x_204 = lean_ctor_get(x_1, 1);
lean_inc(x_204);
x_205 = lean_ctor_get(x_1, 2);
lean_inc(x_205);
x_234 = l_Lean_Expr_hasMVar(x_204);
if (x_234 == 0)
{
x_206 = x_204;
x_207 = x_2;
goto block_233;
}
else
{
lean_object* x_235; lean_object* x_236; 
x_235 = lean_ctor_get(x_2, 1);
lean_inc(x_235);
x_236 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_235, x_204);
lean_dec(x_235);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; 
lean_inc(x_204);
x_237 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_204, x_2);
x_238 = lean_ctor_get(x_237, 1);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 0);
lean_inc(x_239);
lean_dec(x_237);
x_240 = !lean_is_exclusive(x_238);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; 
x_241 = lean_ctor_get(x_238, 1);
lean_inc(x_239);
x_242 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_241, x_204, x_239);
lean_ctor_set(x_238, 1, x_242);
x_206 = x_239;
x_207 = x_238;
goto block_233;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_243 = lean_ctor_get(x_238, 0);
x_244 = lean_ctor_get(x_238, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_238);
lean_inc(x_239);
x_245 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_244, x_204, x_239);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_243);
lean_ctor_set(x_246, 1, x_245);
x_206 = x_239;
x_207 = x_246;
goto block_233;
}
}
else
{
lean_object* x_247; 
lean_dec(x_204);
x_247 = lean_ctor_get(x_236, 0);
lean_inc(x_247);
lean_dec(x_236);
x_206 = x_247;
x_207 = x_2;
goto block_233;
}
}
block_233:
{
lean_object* x_208; lean_object* x_209; uint8_t x_219; 
x_219 = l_Lean_Expr_hasMVar(x_205);
if (x_219 == 0)
{
x_208 = x_205;
x_209 = x_207;
goto block_218;
}
else
{
lean_object* x_220; lean_object* x_221; 
x_220 = lean_ctor_get(x_207, 1);
lean_inc(x_220);
x_221 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_220, x_205);
lean_dec(x_220);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
lean_inc(x_205);
x_222 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_205, x_207);
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 0);
lean_inc(x_224);
lean_dec(x_222);
x_225 = !lean_is_exclusive(x_223);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_ctor_get(x_223, 1);
lean_inc(x_224);
x_227 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_226, x_205, x_224);
lean_ctor_set(x_223, 1, x_227);
x_208 = x_224;
x_209 = x_223;
goto block_218;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_228 = lean_ctor_get(x_223, 0);
x_229 = lean_ctor_get(x_223, 1);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_223);
lean_inc(x_224);
x_230 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_229, x_205, x_224);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_228);
lean_ctor_set(x_231, 1, x_230);
x_208 = x_224;
x_209 = x_231;
goto block_218;
}
}
else
{
lean_object* x_232; 
lean_dec(x_205);
x_232 = lean_ctor_get(x_221, 0);
lean_inc(x_232);
lean_dec(x_221);
x_208 = x_232;
x_209 = x_207;
goto block_218;
}
}
block_218:
{
if (lean_obj_tag(x_1) == 7)
{
uint64_t x_210; uint8_t x_211; lean_object* x_212; lean_object* x_213; 
x_210 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_211 = (uint8_t)((x_210 << 24) >> 61);
x_212 = lean_expr_update_forall(x_1, x_211, x_206, x_208);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_209);
return x_213;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_208);
lean_dec(x_206);
lean_dec(x_1);
x_214 = l_Lean_Expr_Inhabited;
x_215 = l_Lean_Expr_updateForallE_x21___closed__1;
x_216 = lean_panic_fn(x_215);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_209);
return x_217;
}
}
}
}
case 8:
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_294; 
x_248 = lean_ctor_get(x_1, 1);
lean_inc(x_248);
x_249 = lean_ctor_get(x_1, 2);
lean_inc(x_249);
x_250 = lean_ctor_get(x_1, 3);
lean_inc(x_250);
x_294 = l_Lean_Expr_hasMVar(x_248);
if (x_294 == 0)
{
x_251 = x_248;
x_252 = x_2;
goto block_293;
}
else
{
lean_object* x_295; lean_object* x_296; 
x_295 = lean_ctor_get(x_2, 1);
lean_inc(x_295);
x_296 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_295, x_248);
lean_dec(x_295);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; uint8_t x_300; 
lean_inc(x_248);
x_297 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_248, x_2);
x_298 = lean_ctor_get(x_297, 1);
lean_inc(x_298);
x_299 = lean_ctor_get(x_297, 0);
lean_inc(x_299);
lean_dec(x_297);
x_300 = !lean_is_exclusive(x_298);
if (x_300 == 0)
{
lean_object* x_301; lean_object* x_302; 
x_301 = lean_ctor_get(x_298, 1);
lean_inc(x_299);
x_302 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_301, x_248, x_299);
lean_ctor_set(x_298, 1, x_302);
x_251 = x_299;
x_252 = x_298;
goto block_293;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_303 = lean_ctor_get(x_298, 0);
x_304 = lean_ctor_get(x_298, 1);
lean_inc(x_304);
lean_inc(x_303);
lean_dec(x_298);
lean_inc(x_299);
x_305 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_304, x_248, x_299);
x_306 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_306, 0, x_303);
lean_ctor_set(x_306, 1, x_305);
x_251 = x_299;
x_252 = x_306;
goto block_293;
}
}
else
{
lean_object* x_307; 
lean_dec(x_248);
x_307 = lean_ctor_get(x_296, 0);
lean_inc(x_307);
lean_dec(x_296);
x_251 = x_307;
x_252 = x_2;
goto block_293;
}
}
block_293:
{
lean_object* x_253; lean_object* x_254; uint8_t x_279; 
x_279 = l_Lean_Expr_hasMVar(x_249);
if (x_279 == 0)
{
x_253 = x_249;
x_254 = x_252;
goto block_278;
}
else
{
lean_object* x_280; lean_object* x_281; 
x_280 = lean_ctor_get(x_252, 1);
lean_inc(x_280);
x_281 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_280, x_249);
lean_dec(x_280);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; 
lean_inc(x_249);
x_282 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_249, x_252);
x_283 = lean_ctor_get(x_282, 1);
lean_inc(x_283);
x_284 = lean_ctor_get(x_282, 0);
lean_inc(x_284);
lean_dec(x_282);
x_285 = !lean_is_exclusive(x_283);
if (x_285 == 0)
{
lean_object* x_286; lean_object* x_287; 
x_286 = lean_ctor_get(x_283, 1);
lean_inc(x_284);
x_287 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_286, x_249, x_284);
lean_ctor_set(x_283, 1, x_287);
x_253 = x_284;
x_254 = x_283;
goto block_278;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_288 = lean_ctor_get(x_283, 0);
x_289 = lean_ctor_get(x_283, 1);
lean_inc(x_289);
lean_inc(x_288);
lean_dec(x_283);
lean_inc(x_284);
x_290 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_289, x_249, x_284);
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_288);
lean_ctor_set(x_291, 1, x_290);
x_253 = x_284;
x_254 = x_291;
goto block_278;
}
}
else
{
lean_object* x_292; 
lean_dec(x_249);
x_292 = lean_ctor_get(x_281, 0);
lean_inc(x_292);
lean_dec(x_281);
x_253 = x_292;
x_254 = x_252;
goto block_278;
}
}
block_278:
{
lean_object* x_255; lean_object* x_256; uint8_t x_264; 
x_264 = l_Lean_Expr_hasMVar(x_250);
if (x_264 == 0)
{
x_255 = x_250;
x_256 = x_254;
goto block_263;
}
else
{
lean_object* x_265; lean_object* x_266; 
x_265 = lean_ctor_get(x_254, 1);
lean_inc(x_265);
x_266 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_265, x_250);
lean_dec(x_265);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; 
lean_inc(x_250);
x_267 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_250, x_254);
x_268 = lean_ctor_get(x_267, 1);
lean_inc(x_268);
x_269 = lean_ctor_get(x_267, 0);
lean_inc(x_269);
lean_dec(x_267);
x_270 = !lean_is_exclusive(x_268);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; 
x_271 = lean_ctor_get(x_268, 1);
lean_inc(x_269);
x_272 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_271, x_250, x_269);
lean_ctor_set(x_268, 1, x_272);
x_255 = x_269;
x_256 = x_268;
goto block_263;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_273 = lean_ctor_get(x_268, 0);
x_274 = lean_ctor_get(x_268, 1);
lean_inc(x_274);
lean_inc(x_273);
lean_dec(x_268);
lean_inc(x_269);
x_275 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_274, x_250, x_269);
x_276 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_276, 0, x_273);
lean_ctor_set(x_276, 1, x_275);
x_255 = x_269;
x_256 = x_276;
goto block_263;
}
}
else
{
lean_object* x_277; 
lean_dec(x_250);
x_277 = lean_ctor_get(x_266, 0);
lean_inc(x_277);
lean_dec(x_266);
x_255 = x_277;
x_256 = x_254;
goto block_263;
}
}
block_263:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_257; lean_object* x_258; 
x_257 = lean_expr_update_let(x_1, x_251, x_253, x_255);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_256);
return x_258;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_255);
lean_dec(x_253);
lean_dec(x_251);
lean_dec(x_1);
x_259 = l_Lean_Expr_Inhabited;
x_260 = l_Lean_Expr_updateLet_x21___closed__1;
x_261 = lean_panic_fn(x_260);
x_262 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_256);
return x_262;
}
}
}
}
}
case 10:
{
lean_object* x_308; uint8_t x_309; 
x_308 = lean_ctor_get(x_1, 1);
lean_inc(x_308);
x_309 = l_Lean_Expr_hasMVar(x_308);
if (x_309 == 0)
{
x_15 = x_308;
x_16 = x_2;
goto block_23;
}
else
{
lean_object* x_310; lean_object* x_311; 
x_310 = lean_ctor_get(x_2, 1);
lean_inc(x_310);
x_311 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_310, x_308);
lean_dec(x_310);
if (lean_obj_tag(x_311) == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; 
lean_inc(x_308);
x_312 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_308, x_2);
x_313 = lean_ctor_get(x_312, 1);
lean_inc(x_313);
x_314 = lean_ctor_get(x_312, 0);
lean_inc(x_314);
lean_dec(x_312);
x_315 = !lean_is_exclusive(x_313);
if (x_315 == 0)
{
lean_object* x_316; lean_object* x_317; 
x_316 = lean_ctor_get(x_313, 1);
lean_inc(x_314);
x_317 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_316, x_308, x_314);
lean_ctor_set(x_313, 1, x_317);
x_15 = x_314;
x_16 = x_313;
goto block_23;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_318 = lean_ctor_get(x_313, 0);
x_319 = lean_ctor_get(x_313, 1);
lean_inc(x_319);
lean_inc(x_318);
lean_dec(x_313);
lean_inc(x_314);
x_320 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_319, x_308, x_314);
x_321 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_321, 0, x_318);
lean_ctor_set(x_321, 1, x_320);
x_15 = x_314;
x_16 = x_321;
goto block_23;
}
}
else
{
lean_object* x_322; 
lean_dec(x_308);
x_322 = lean_ctor_get(x_311, 0);
lean_inc(x_322);
lean_dec(x_311);
x_15 = x_322;
x_16 = x_2;
goto block_23;
}
}
}
case 11:
{
lean_object* x_323; uint8_t x_324; 
x_323 = lean_ctor_get(x_1, 2);
lean_inc(x_323);
x_324 = l_Lean_Expr_hasMVar(x_323);
if (x_324 == 0)
{
x_24 = x_323;
x_25 = x_2;
goto block_32;
}
else
{
lean_object* x_325; lean_object* x_326; 
x_325 = lean_ctor_get(x_2, 1);
lean_inc(x_325);
x_326 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_325, x_323);
lean_dec(x_325);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; 
lean_inc(x_323);
x_327 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_323, x_2);
x_328 = lean_ctor_get(x_327, 1);
lean_inc(x_328);
x_329 = lean_ctor_get(x_327, 0);
lean_inc(x_329);
lean_dec(x_327);
x_330 = !lean_is_exclusive(x_328);
if (x_330 == 0)
{
lean_object* x_331; lean_object* x_332; 
x_331 = lean_ctor_get(x_328, 1);
lean_inc(x_329);
x_332 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_331, x_323, x_329);
lean_ctor_set(x_328, 1, x_332);
x_24 = x_329;
x_25 = x_328;
goto block_32;
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_333 = lean_ctor_get(x_328, 0);
x_334 = lean_ctor_get(x_328, 1);
lean_inc(x_334);
lean_inc(x_333);
lean_dec(x_328);
lean_inc(x_329);
x_335 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_334, x_323, x_329);
x_336 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_336, 0, x_333);
lean_ctor_set(x_336, 1, x_335);
x_24 = x_329;
x_25 = x_336;
goto block_32;
}
}
else
{
lean_object* x_337; 
lean_dec(x_323);
x_337 = lean_ctor_get(x_326, 0);
lean_inc(x_337);
lean_dec(x_326);
x_24 = x_337;
x_25 = x_2;
goto block_32;
}
}
}
default: 
{
lean_object* x_338; 
x_338 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_338, 0, x_1);
lean_ctor_set(x_338, 1, x_2);
return x_338;
}
}
block_14:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_3);
x_7 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_6, x_1, x_3);
lean_ctor_set(x_4, 1, x_7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
lean_inc(x_3);
x_11 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_10, x_1, x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
block_23:
{
if (lean_obj_tag(x_1) == 10)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_expr_update_mdata(x_1, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_15);
lean_dec(x_1);
x_19 = l_Lean_Expr_Inhabited;
x_20 = l_Lean_Expr_updateMData_x21___closed__2;
x_21 = lean_panic_fn(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
return x_22;
}
}
block_32:
{
if (lean_obj_tag(x_1) == 11)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_expr_update_proj(x_1, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_24);
lean_dec(x_1);
x_28 = l_Lean_Expr_Inhabited;
x_29 = l_Lean_Expr_updateProj_x21___closed__2;
x_30 = lean_panic_fn(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_25);
return x_31;
}
}
}
}
lean_object* l___private_Init_Lean_MetavarContext_5__instantiateDelayedAux___main___at_Lean_MetavarContext_InstantiateExprMVars_main___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_MetavarContext_5__instantiateDelayedAux___main___at_Lean_MetavarContext_InstantiateExprMVars_main___main___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_MetavarContext_InstantiateExprMVars_main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_1, x_2);
return x_3;
}
}
lean_object* l_mkHashMap___at_Lean_MetavarContext_instantiateMVars___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_MetavarContext_instantiateMVars___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_Lean_MetavarContext_instantiateMVars(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Expr_hasMVar(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = l_Lean_MetavarContext_instantiateMVars___closed__1;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_MetavarContext_InstantiateExprMVars_main___main(x_2, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
lean_ctor_set(x_7, 1, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
uint8_t l_AssocList_contains___main___at___private_Init_Lean_MetavarContext_8__visit_x3f___spec__2(lean_object* x_1, lean_object* x_2) {
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
uint8_t l_HashMapImp_contains___at___private_Init_Lean_MetavarContext_8__visit_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_contains___main___at___private_Init_Lean_MetavarContext_8__visit_x3f___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_AssocList_foldlM___main___at___private_Init_Lean_MetavarContext_8__visit_x3f___spec__6(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_Expr_hash(x_4);
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
x_16 = l_Lean_Expr_hash(x_12);
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
lean_object* l_HashMapImp_moveEntries___main___at___private_Init_Lean_MetavarContext_8__visit_x3f___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_AssocList_foldlM___main___at___private_Init_Lean_MetavarContext_8__visit_x3f___spec__6(x_3, x_6);
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
lean_object* l_HashMapImp_expand___at___private_Init_Lean_MetavarContext_8__visit_x3f___spec__4(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_HashMapImp_moveEntries___main___at___private_Init_Lean_MetavarContext_8__visit_x3f___spec__5(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at___private_Init_Lean_MetavarContext_8__visit_x3f___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_AssocList_replace___main___at___private_Init_Lean_MetavarContext_8__visit_x3f___spec__7(x_1, x_2, x_7);
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
x_14 = l_AssocList_replace___main___at___private_Init_Lean_MetavarContext_8__visit_x3f___spec__7(x_1, x_2, x_12);
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
lean_object* l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_8__visit_x3f___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l_Lean_Expr_hash(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_AssocList_contains___main___at___private_Init_Lean_MetavarContext_8__visit_x3f___spec__2(x_2, x_10);
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
x_17 = l_HashMapImp_expand___at___private_Init_Lean_MetavarContext_8__visit_x3f___spec__4(x_13, x_15);
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
x_18 = l_AssocList_replace___main___at___private_Init_Lean_MetavarContext_8__visit_x3f___spec__7(x_2, x_3, x_10);
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
x_23 = l_Lean_Expr_hash(x_2);
x_24 = lean_usize_modn(x_23, x_22);
x_25 = lean_array_uget(x_21, x_24);
x_26 = l_AssocList_contains___main___at___private_Init_Lean_MetavarContext_8__visit_x3f___spec__2(x_2, x_25);
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
x_32 = l_HashMapImp_expand___at___private_Init_Lean_MetavarContext_8__visit_x3f___spec__4(x_28, x_30);
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
x_34 = l_AssocList_replace___main___at___private_Init_Lean_MetavarContext_8__visit_x3f___spec__7(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l___private_Init_Lean_MetavarContext_8__visit_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_14; 
x_14 = l_Lean_Expr_hasMVar(x_1);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = l_Lean_Expr_hasFVar(x_1);
if (x_15 == 0)
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_16 = 0;
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_2);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = lean_box(0);
x_3 = x_19;
goto block_13;
}
}
else
{
lean_object* x_20; 
x_20 = lean_box(0);
x_3 = x_20;
goto block_13;
}
block_13:
{
uint8_t x_4; 
lean_dec(x_3);
x_4 = l_HashMapImp_contains___at___private_Init_Lean_MetavarContext_8__visit_x3f___spec__1(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_box(0);
x_6 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_8__visit_x3f___spec__3(x_2, x_1, x_5);
x_7 = 1;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_10 = 0;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
return x_12;
}
}
}
}
lean_object* l_AssocList_contains___main___at___private_Init_Lean_MetavarContext_8__visit_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AssocList_contains___main___at___private_Init_Lean_MetavarContext_8__visit_x3f___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_HashMapImp_contains___at___private_Init_Lean_MetavarContext_8__visit_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_HashMapImp_contains___at___private_Init_Lean_MetavarContext_8__visit_x3f___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_MetavarContext_9__visit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
lean_inc(x_2);
x_4 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_unbox(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_apply_2(x_1, x_2, x_11);
return x_12;
}
}
}
lean_object* l___private_Init_Lean_MetavarContext_10__dep___main___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; lean_object* x_4; 
lean_dec(x_1);
x_3 = 0;
x_4 = lean_box(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = l_Lean_LocalDecl_fvarId(x_5);
x_7 = lean_apply_1(x_1, x_6);
return x_7;
}
}
}
lean_object* l___private_Init_Lean_MetavarContext_10__dep___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_apply_1(x_2, x_5);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
case 2:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
lean_inc(x_10);
lean_inc(x_1);
x_11 = lean_metavar_ctx_get_expr_assignment(x_1, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_12 = l_Lean_MetavarContext_getDecl(x_1, x_10);
lean_dec(x_10);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_alloc_closure((void*)(l___private_Init_Lean_MetavarContext_10__dep___main___lambda__1___boxed), 2, 1);
lean_closure_set(x_15, 0, x_2);
x_16 = l_Id_Monad;
x_17 = l_PersistentArray_anyM___rarg(x_16, x_14, x_15);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_4);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_10);
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
lean_dec(x_11);
lean_inc(x_21);
x_22 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_21, x_4);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
if (x_24 == 0)
{
uint8_t x_25; 
lean_dec(x_21);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_22, 0);
lean_dec(x_26);
return x_22;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_object* x_29; 
lean_dec(x_23);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_dec(x_22);
x_3 = x_21;
x_4 = x_29;
goto _start;
}
}
}
case 5:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_3, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_3, 1);
lean_inc(x_32);
lean_dec(x_3);
lean_inc(x_32);
x_33 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_32, x_4);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
lean_dec(x_32);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = l_Lean_Expr_isApp(x_31);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_inc(x_31);
x_38 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_31, x_36);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
if (x_40 == 0)
{
uint8_t x_41; 
lean_dec(x_31);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_38, 0);
lean_dec(x_42);
return x_38;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
lean_dec(x_38);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_39);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
lean_object* x_45; 
lean_dec(x_39);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_dec(x_38);
x_3 = x_31;
x_4 = x_45;
goto _start;
}
}
else
{
x_3 = x_31;
x_4 = x_36;
goto _start;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_33, 1);
lean_inc(x_48);
lean_dec(x_33);
lean_inc(x_2);
lean_inc(x_1);
x_49 = l___private_Init_Lean_MetavarContext_10__dep___main(x_1, x_2, x_32, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
lean_dec(x_50);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = l_Lean_Expr_isApp(x_31);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_inc(x_31);
x_54 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_31, x_52);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_unbox(x_55);
if (x_56 == 0)
{
uint8_t x_57; 
lean_dec(x_31);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_54);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_54, 0);
lean_dec(x_58);
return x_54;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_dec(x_54);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
else
{
lean_object* x_61; 
lean_dec(x_55);
x_61 = lean_ctor_get(x_54, 1);
lean_inc(x_61);
lean_dec(x_54);
x_3 = x_31;
x_4 = x_61;
goto _start;
}
}
else
{
x_3 = x_31;
x_4 = x_52;
goto _start;
}
}
else
{
uint8_t x_64; 
lean_dec(x_31);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_49);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_49, 0);
lean_dec(x_65);
return x_49;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_49, 1);
lean_inc(x_66);
lean_dec(x_49);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_50);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
case 6:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_68 = lean_ctor_get(x_3, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_3, 2);
lean_inc(x_69);
lean_dec(x_3);
lean_inc(x_68);
x_70 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_68, x_4);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_unbox(x_71);
lean_dec(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
lean_dec(x_68);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
lean_inc(x_69);
x_74 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_69, x_73);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_unbox(x_75);
if (x_76 == 0)
{
uint8_t x_77; 
lean_dec(x_69);
lean_dec(x_2);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_74);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_74, 0);
lean_dec(x_78);
return x_74;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_74, 1);
lean_inc(x_79);
lean_dec(x_74);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_75);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
else
{
lean_object* x_81; 
lean_dec(x_75);
x_81 = lean_ctor_get(x_74, 1);
lean_inc(x_81);
lean_dec(x_74);
x_3 = x_69;
x_4 = x_81;
goto _start;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_83 = lean_ctor_get(x_70, 1);
lean_inc(x_83);
lean_dec(x_70);
lean_inc(x_2);
lean_inc(x_1);
x_84 = l___private_Init_Lean_MetavarContext_10__dep___main(x_1, x_2, x_68, x_83);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_unbox(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
lean_dec(x_85);
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
lean_dec(x_84);
lean_inc(x_69);
x_88 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_69, x_87);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_unbox(x_89);
if (x_90 == 0)
{
uint8_t x_91; 
lean_dec(x_69);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_88);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_88, 0);
lean_dec(x_92);
return x_88;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_88, 1);
lean_inc(x_93);
lean_dec(x_88);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_89);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
else
{
lean_object* x_95; 
lean_dec(x_89);
x_95 = lean_ctor_get(x_88, 1);
lean_inc(x_95);
lean_dec(x_88);
x_3 = x_69;
x_4 = x_95;
goto _start;
}
}
else
{
uint8_t x_97; 
lean_dec(x_69);
lean_dec(x_2);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_84);
if (x_97 == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_84, 0);
lean_dec(x_98);
return x_84;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_84, 1);
lean_inc(x_99);
lean_dec(x_84);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_85);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
}
case 7:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_101 = lean_ctor_get(x_3, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_3, 2);
lean_inc(x_102);
lean_dec(x_3);
lean_inc(x_101);
x_103 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_101, x_4);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_unbox(x_104);
lean_dec(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
lean_dec(x_101);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
lean_inc(x_102);
x_107 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_102, x_106);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_unbox(x_108);
if (x_109 == 0)
{
uint8_t x_110; 
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_107);
if (x_110 == 0)
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_107, 0);
lean_dec(x_111);
return x_107;
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_107, 1);
lean_inc(x_112);
lean_dec(x_107);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_108);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
else
{
lean_object* x_114; 
lean_dec(x_108);
x_114 = lean_ctor_get(x_107, 1);
lean_inc(x_114);
lean_dec(x_107);
x_3 = x_102;
x_4 = x_114;
goto _start;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_116 = lean_ctor_get(x_103, 1);
lean_inc(x_116);
lean_dec(x_103);
lean_inc(x_2);
lean_inc(x_1);
x_117 = l___private_Init_Lean_MetavarContext_10__dep___main(x_1, x_2, x_101, x_116);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_unbox(x_118);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
lean_dec(x_118);
x_120 = lean_ctor_get(x_117, 1);
lean_inc(x_120);
lean_dec(x_117);
lean_inc(x_102);
x_121 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_102, x_120);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_unbox(x_122);
if (x_123 == 0)
{
uint8_t x_124; 
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_121);
if (x_124 == 0)
{
lean_object* x_125; 
x_125 = lean_ctor_get(x_121, 0);
lean_dec(x_125);
return x_121;
}
else
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_121, 1);
lean_inc(x_126);
lean_dec(x_121);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_122);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
else
{
lean_object* x_128; 
lean_dec(x_122);
x_128 = lean_ctor_get(x_121, 1);
lean_inc(x_128);
lean_dec(x_121);
x_3 = x_102;
x_4 = x_128;
goto _start;
}
}
else
{
uint8_t x_130; 
lean_dec(x_102);
lean_dec(x_2);
lean_dec(x_1);
x_130 = !lean_is_exclusive(x_117);
if (x_130 == 0)
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_117, 0);
lean_dec(x_131);
return x_117;
}
else
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_117, 1);
lean_inc(x_132);
lean_dec(x_117);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_118);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
}
case 8:
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_134 = lean_ctor_get(x_3, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_3, 2);
lean_inc(x_135);
x_136 = lean_ctor_get(x_3, 3);
lean_inc(x_136);
lean_dec(x_3);
lean_inc(x_134);
x_173 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_134, x_4);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_unbox(x_174);
if (x_175 == 0)
{
lean_object* x_176; uint8_t x_177; 
lean_dec(x_134);
x_176 = lean_ctor_get(x_173, 1);
lean_inc(x_176);
lean_dec(x_173);
x_177 = lean_unbox(x_174);
lean_dec(x_174);
x_137 = x_177;
x_138 = x_176;
goto block_172;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
lean_dec(x_174);
x_178 = lean_ctor_get(x_173, 1);
lean_inc(x_178);
lean_dec(x_173);
lean_inc(x_2);
lean_inc(x_1);
x_179 = l___private_Init_Lean_MetavarContext_10__dep___main(x_1, x_2, x_134, x_178);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_unbox(x_180);
lean_dec(x_180);
x_137 = x_182;
x_138 = x_181;
goto block_172;
}
block_172:
{
if (x_137 == 0)
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; 
lean_inc(x_135);
x_139 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_135, x_138);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_unbox(x_140);
lean_dec(x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
lean_dec(x_135);
x_142 = lean_ctor_get(x_139, 1);
lean_inc(x_142);
lean_dec(x_139);
lean_inc(x_136);
x_143 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_136, x_142);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_unbox(x_144);
if (x_145 == 0)
{
uint8_t x_146; 
lean_dec(x_136);
lean_dec(x_2);
lean_dec(x_1);
x_146 = !lean_is_exclusive(x_143);
if (x_146 == 0)
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_143, 0);
lean_dec(x_147);
return x_143;
}
else
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_143, 1);
lean_inc(x_148);
lean_dec(x_143);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_144);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
}
else
{
lean_object* x_150; 
lean_dec(x_144);
x_150 = lean_ctor_get(x_143, 1);
lean_inc(x_150);
lean_dec(x_143);
x_3 = x_136;
x_4 = x_150;
goto _start;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_152 = lean_ctor_get(x_139, 1);
lean_inc(x_152);
lean_dec(x_139);
lean_inc(x_2);
lean_inc(x_1);
x_153 = l___private_Init_Lean_MetavarContext_10__dep___main(x_1, x_2, x_135, x_152);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_unbox(x_154);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
lean_dec(x_154);
x_156 = lean_ctor_get(x_153, 1);
lean_inc(x_156);
lean_dec(x_153);
lean_inc(x_136);
x_157 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_136, x_156);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_unbox(x_158);
if (x_159 == 0)
{
uint8_t x_160; 
lean_dec(x_136);
lean_dec(x_2);
lean_dec(x_1);
x_160 = !lean_is_exclusive(x_157);
if (x_160 == 0)
{
lean_object* x_161; 
x_161 = lean_ctor_get(x_157, 0);
lean_dec(x_161);
return x_157;
}
else
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_157, 1);
lean_inc(x_162);
lean_dec(x_157);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_158);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
}
else
{
lean_object* x_164; 
lean_dec(x_158);
x_164 = lean_ctor_get(x_157, 1);
lean_inc(x_164);
lean_dec(x_157);
x_3 = x_136;
x_4 = x_164;
goto _start;
}
}
else
{
uint8_t x_166; 
lean_dec(x_136);
lean_dec(x_2);
lean_dec(x_1);
x_166 = !lean_is_exclusive(x_153);
if (x_166 == 0)
{
lean_object* x_167; 
x_167 = lean_ctor_get(x_153, 0);
lean_dec(x_167);
return x_153;
}
else
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_153, 1);
lean_inc(x_168);
lean_dec(x_153);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_154);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
}
}
else
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_2);
lean_dec(x_1);
x_170 = lean_box(x_137);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_138);
return x_171;
}
}
}
case 10:
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_183 = lean_ctor_get(x_3, 1);
lean_inc(x_183);
lean_dec(x_3);
lean_inc(x_183);
x_184 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_183, x_4);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_unbox(x_185);
if (x_186 == 0)
{
uint8_t x_187; 
lean_dec(x_183);
lean_dec(x_2);
lean_dec(x_1);
x_187 = !lean_is_exclusive(x_184);
if (x_187 == 0)
{
lean_object* x_188; 
x_188 = lean_ctor_get(x_184, 0);
lean_dec(x_188);
return x_184;
}
else
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_ctor_get(x_184, 1);
lean_inc(x_189);
lean_dec(x_184);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_185);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
else
{
lean_object* x_191; 
lean_dec(x_185);
x_191 = lean_ctor_get(x_184, 1);
lean_inc(x_191);
lean_dec(x_184);
x_3 = x_183;
x_4 = x_191;
goto _start;
}
}
case 11:
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_193 = lean_ctor_get(x_3, 2);
lean_inc(x_193);
lean_dec(x_3);
lean_inc(x_193);
x_194 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_193, x_4);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_unbox(x_195);
if (x_196 == 0)
{
uint8_t x_197; 
lean_dec(x_193);
lean_dec(x_2);
lean_dec(x_1);
x_197 = !lean_is_exclusive(x_194);
if (x_197 == 0)
{
lean_object* x_198; 
x_198 = lean_ctor_get(x_194, 0);
lean_dec(x_198);
return x_194;
}
else
{
lean_object* x_199; lean_object* x_200; 
x_199 = lean_ctor_get(x_194, 1);
lean_inc(x_199);
lean_dec(x_194);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_195);
lean_ctor_set(x_200, 1, x_199);
return x_200;
}
}
else
{
lean_object* x_201; 
lean_dec(x_195);
x_201 = lean_ctor_get(x_194, 1);
lean_inc(x_201);
lean_dec(x_194);
x_3 = x_193;
x_4 = x_201;
goto _start;
}
}
default: 
{
uint8_t x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_203 = 0;
x_204 = lean_box(x_203);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_4);
return x_205;
}
}
}
}
lean_object* l___private_Init_Lean_MetavarContext_10__dep___main___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_MetavarContext_10__dep___main___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_MetavarContext_10__dep(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_MetavarContext_10__dep___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_MetavarContext_DependsOn_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Expr_hasFVar(x_3);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l_Lean_Expr_hasMVar(x_3);
if (x_6 == 0)
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = l___private_Init_Lean_MetavarContext_10__dep___main(x_1, x_2, x_3, x_4);
return x_10;
}
}
else
{
lean_object* x_11; 
x_11 = l___private_Init_Lean_MetavarContext_10__dep___main(x_1, x_2, x_3, x_4);
return x_11;
}
}
}
lean_object* l_mkHashMap___at_Lean_MetavarContext_exprDependsOn___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_mkHashSet___at_Lean_MetavarContext_exprDependsOn___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_MetavarContext_exprDependsOn___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_Lean_MetavarContext_exprDependsOn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasFVar(x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = l_Lean_Expr_hasMVar(x_3);
if (x_5 == 0)
{
uint8_t x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = 0;
x_7 = lean_box(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_MetavarContext_exprDependsOn___closed__1;
x_9 = l___private_Init_Lean_MetavarContext_10__dep___main(x_1, x_2, x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_MetavarContext_exprDependsOn___closed__1;
x_12 = l___private_Init_Lean_MetavarContext_10__dep___main(x_1, x_2, x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
return x_13;
}
}
}
lean_object* l_Lean_MetavarContext_localDeclDependsOn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 3);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Expr_hasFVar(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l_Lean_Expr_hasMVar(x_4);
if (x_6 == 0)
{
uint8_t x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_7 = 0;
x_8 = lean_box(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_HashMap_Inhabited___closed__1;
x_10 = l___private_Init_Lean_MetavarContext_10__dep___main(x_1, x_2, x_4, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_HashMap_Inhabited___closed__1;
x_13 = l___private_Init_Lean_MetavarContext_10__dep___main(x_1, x_2, x_4, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_29; 
x_15 = lean_ctor_get(x_3, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 4);
lean_inc(x_16);
lean_dec(x_3);
x_29 = l_Lean_Expr_hasFVar(x_15);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = l_Lean_Expr_hasMVar(x_15);
if (x_30 == 0)
{
uint8_t x_31; lean_object* x_32; 
lean_dec(x_15);
x_31 = 0;
x_32 = l_HashMap_Inhabited___closed__1;
x_17 = x_31;
x_18 = x_32;
goto block_28;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = l_HashMap_Inhabited___closed__1;
lean_inc(x_2);
lean_inc(x_1);
x_34 = l___private_Init_Lean_MetavarContext_10__dep___main(x_1, x_2, x_15, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_unbox(x_35);
lean_dec(x_35);
x_17 = x_37;
x_18 = x_36;
goto block_28;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_38 = l_HashMap_Inhabited___closed__1;
lean_inc(x_2);
lean_inc(x_1);
x_39 = l___private_Init_Lean_MetavarContext_10__dep___main(x_1, x_2, x_15, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_unbox(x_40);
lean_dec(x_40);
x_17 = x_42;
x_18 = x_41;
goto block_28;
}
block_28:
{
if (x_17 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_Expr_hasFVar(x_16);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = l_Lean_Expr_hasMVar(x_16);
if (x_20 == 0)
{
uint8_t x_21; lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_2);
lean_dec(x_1);
x_21 = 0;
x_22 = lean_box(x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = l___private_Init_Lean_MetavarContext_10__dep___main(x_1, x_2, x_16, x_18);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = l___private_Init_Lean_MetavarContext_10__dep___main(x_1, x_2, x_16, x_18);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
return x_26;
}
}
else
{
lean_object* x_27; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_box(x_17);
return x_27;
}
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_MetavarContext_MkBinding_Exception_toString___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = l_Array_empty___closed__1;
x_7 = x_3;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_array_fget(x_3, x_2);
x_9 = lean_box(0);
lean_inc(x_8);
x_10 = x_9;
x_11 = lean_array_fset(x_3, x_2, x_10);
lean_inc(x_1);
x_12 = l_Lean_LocalContext_findFVar(x_1, x_8);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_2, x_13);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_15 = l_Lean_LocalDecl_Inhabited;
x_16 = l_Option_get_x21___rarg___closed__3;
x_17 = lean_panic_fn(x_16);
x_18 = l_Lean_LocalDecl_userName(x_17);
lean_dec(x_17);
x_19 = l_System_FilePath_dirName___closed__1;
x_20 = l_Lean_Name_toStringWithSep___main(x_19, x_18);
x_21 = l_Char_HasRepr___closed__1;
x_22 = lean_string_append(x_21, x_20);
lean_dec(x_20);
x_23 = lean_string_append(x_22, x_21);
x_24 = x_23;
x_25 = lean_array_fset(x_11, x_2, x_24);
lean_dec(x_2);
x_2 = x_14;
x_3 = x_25;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_12, 0);
lean_inc(x_27);
lean_dec(x_12);
x_28 = l_Lean_LocalDecl_userName(x_27);
lean_dec(x_27);
x_29 = l_System_FilePath_dirName___closed__1;
x_30 = l_Lean_Name_toStringWithSep___main(x_29, x_28);
x_31 = l_Char_HasRepr___closed__1;
x_32 = lean_string_append(x_31, x_30);
lean_dec(x_30);
x_33 = lean_string_append(x_32, x_31);
x_34 = x_33;
x_35 = lean_array_fset(x_11, x_2, x_34);
lean_dec(x_2);
x_2 = x_14;
x_3 = x_35;
goto _start;
}
}
}
}
lean_object* l_List_toStringAux___main___at_Lean_MetavarContext_MkBinding_Exception_toString___spec__3(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_String_splitAux___main___closed__1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_List_reprAux___main___rarg___closed__1;
x_7 = lean_string_append(x_6, x_4);
lean_dec(x_4);
x_8 = l_List_toStringAux___main___at_Lean_MetavarContext_MkBinding_Exception_toString___spec__3(x_1, x_5);
x_9 = lean_string_append(x_7, x_8);
lean_dec(x_8);
return x_9;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; 
x_10 = l_String_splitAux___main___closed__1;
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = 0;
x_14 = l_List_toStringAux___main___at_Lean_MetavarContext_MkBinding_Exception_toString___spec__3(x_13, x_12);
x_15 = lean_string_append(x_11, x_14);
lean_dec(x_14);
return x_15;
}
}
}
}
lean_object* l_List_toString___at_Lean_MetavarContext_MkBinding_Exception_toString___spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_repr___rarg___closed__1;
return x_2;
}
else
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = 1;
x_4 = l_List_toStringAux___main___at_Lean_MetavarContext_MkBinding_Exception_toString___spec__3(x_3, x_1);
x_5 = l_List_repr___rarg___closed__2;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_List_repr___rarg___closed__3;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
}
}
lean_object* _init_l_Lean_MetavarContext_MkBinding_Exception_toString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to revert ");
return x_1;
}
}
lean_object* _init_l_Lean_MetavarContext_MkBinding_Exception_toString___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", '");
return x_1;
}
}
lean_object* _init_l_Lean_MetavarContext_MkBinding_Exception_toString___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' depends on them, and it is an auxiliary declaration created by the elaborator");
return x_1;
}
}
lean_object* _init_l_Lean_MetavarContext_MkBinding_Exception_toString___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" (possible solution: use tactic 'clear' to remove '");
return x_1;
}
}
lean_object* _init_l_Lean_MetavarContext_MkBinding_Exception_toString___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' from local context)");
return x_1;
}
}
lean_object* _init_l_Lean_MetavarContext_MkBinding_Exception_toString___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to create binding due to read only metavariable ");
return x_1;
}
}
lean_object* l_Lean_MetavarContext_MkBinding_Exception_toString(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_umapMAux___main___at_Lean_MetavarContext_MkBinding_Exception_toString___spec__1(x_2, x_5, x_3);
x_7 = l_Array_toList___rarg(x_6);
lean_dec(x_6);
x_8 = l_List_toString___at_Lean_MetavarContext_MkBinding_Exception_toString___spec__2(x_7);
x_9 = l_Array_HasRepr___rarg___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_Lean_MetavarContext_MkBinding_Exception_toString___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lean_MetavarContext_MkBinding_Exception_toString___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_Lean_LocalDecl_userName(x_4);
lean_dec(x_4);
x_16 = l_System_FilePath_dirName___closed__1;
x_17 = l_Lean_Name_toStringWithSep___main(x_16, x_15);
x_18 = lean_string_append(x_14, x_17);
x_19 = l_Lean_MetavarContext_MkBinding_Exception_toString___closed__3;
x_20 = lean_string_append(x_18, x_19);
x_21 = l_Lean_MetavarContext_MkBinding_Exception_toString___closed__4;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_string_append(x_22, x_17);
lean_dec(x_17);
x_24 = l_Lean_MetavarContext_MkBinding_Exception_toString___closed__5;
x_25 = lean_string_append(x_23, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_dec(x_1);
x_27 = l_System_FilePath_dirName___closed__1;
x_28 = l_Lean_Name_toStringWithSep___main(x_27, x_26);
x_29 = l_Lean_MetavarContext_MkBinding_Exception_toString___closed__6;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
return x_30;
}
}
}
lean_object* l_List_toStringAux___main___at_Lean_MetavarContext_MkBinding_Exception_toString___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_toStringAux___main___at_Lean_MetavarContext_MkBinding_Exception_toString___spec__3(x_3, x_2);
return x_4;
}
}
lean_object* _init_l_Lean_MetavarContext_MkBinding_Exception_hasToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MetavarContext_MkBinding_Exception_toString), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_MetavarContext_MkBinding_Exception_hasToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_MetavarContext_MkBinding_Exception_hasToString___closed__1;
return x_1;
}
}
lean_object* l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 2, x_5);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_11 = lean_apply_1(x_1, x_10);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_11);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
lean_object* _init_l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter___lambda__1___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_EStateM_MonadState___closed__2;
x_2 = l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter___closed__1;
x_3 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter___lambda__2), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter___closed__2;
x_2 = l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter___closed__4;
return x_1;
}
}
lean_object* l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter___lambda__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_MetavarContext_11__abstractRange(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_3);
x_7 = lean_apply_3(x_1, x_3, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_expr_abstract_range(x_9, x_4, x_3);
lean_dec(x_3);
lean_dec(x_9);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = lean_expr_abstract_range(x_11, x_4, x_3);
lean_dec(x_3);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_3);
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l___private_Init_Lean_MetavarContext_11__abstractRange___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_MetavarContext_11__abstractRange(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_7;
}
}
lean_object* _init_l_Lean_MetavarContext_MkBinding_mkBinding___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_MetavarContext_getDecl___closed__1;
x_2 = lean_unsigned_to_nat(627u);
x_3 = lean_unsigned_to_nat(13u);
x_4 = l_Nat_foldRevAux___main___at_Lean_LocalContext_mkBinding___spec__1___closed__1;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_MetavarContext_MkBinding_mkBinding___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_Expr_Inhabited;
x_10 = lean_array_get(x_9, x_1, x_6);
x_11 = l_Lean_LocalContext_findFVar(x_2, x_10);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_12 = l_monadInhabited___rarg(x_3, x_9);
x_13 = l_Lean_MetavarContext_MkBinding_mkBinding___lambda__1___closed__1;
x_14 = lean_panic_fn(x_13);
x_15 = lean_apply_1(x_14, x_8);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_3);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 3);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_16, sizeof(void*)*4);
lean_dec(x_16);
lean_inc(x_1);
x_20 = lean_apply_3(x_4, x_1, x_18, x_8);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_expr_abstract_range(x_22, x_6, x_1);
lean_dec(x_1);
lean_dec(x_22);
if (x_5 == 0)
{
lean_object* x_24; 
x_24 = l_Lean_mkForall(x_17, x_19, x_23, x_7);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; 
x_25 = l_Lean_mkLambda(x_17, x_19, x_23, x_7);
lean_ctor_set(x_20, 0, x_25);
return x_20;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = lean_expr_abstract_range(x_26, x_6, x_1);
lean_dec(x_1);
lean_dec(x_26);
if (x_5 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_mkForall(x_17, x_19, x_28, x_7);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_mkLambda(x_17, x_19, x_28, x_7);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_20);
if (x_33 == 0)
{
return x_20;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_20, 0);
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_20);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_16, 2);
lean_inc(x_37);
x_38 = lean_ctor_get(x_16, 3);
lean_inc(x_38);
x_39 = lean_ctor_get(x_16, 4);
lean_inc(x_39);
lean_dec(x_16);
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_expr_has_loose_bvar(x_7, x_40);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_4);
lean_dec(x_1);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_7);
lean_ctor_set(x_42, 1, x_8);
return x_42;
}
else
{
lean_object* x_43; 
lean_inc(x_4);
lean_inc(x_1);
x_43 = lean_apply_3(x_4, x_1, x_38, x_8);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_expr_abstract_range(x_44, x_6, x_1);
lean_dec(x_44);
lean_inc(x_1);
x_47 = lean_apply_3(x_4, x_1, x_39, x_45);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_expr_abstract_range(x_49, x_6, x_1);
lean_dec(x_1);
lean_dec(x_49);
x_51 = 0;
x_52 = l_Lean_mkLet(x_37, x_46, x_50, x_7, x_51);
lean_ctor_set(x_47, 0, x_52);
return x_47;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_47, 0);
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_47);
x_55 = lean_expr_abstract_range(x_53, x_6, x_1);
lean_dec(x_1);
lean_dec(x_53);
x_56 = 0;
x_57 = l_Lean_mkLet(x_37, x_46, x_55, x_7, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_54);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_dec(x_46);
lean_dec(x_37);
lean_dec(x_7);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_47);
if (x_59 == 0)
{
return x_47;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_47, 0);
x_61 = lean_ctor_get(x_47, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_47);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_43);
if (x_63 == 0)
{
return x_43;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_43, 0);
x_65 = lean_ctor_get(x_43, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_43);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
}
}
}
lean_object* l_Lean_MetavarContext_MkBinding_mkBinding(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_array_get_size(x_4);
lean_inc(x_2);
lean_inc(x_4);
x_8 = lean_apply_3(x_2, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_expr_abstract_range(x_9, x_7, x_4);
lean_dec(x_9);
x_12 = l_EIO_Monad___closed__1;
x_13 = lean_box(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_MetavarContext_MkBinding_mkBinding___lambda__1___boxed), 8, 5);
lean_closure_set(x_14, 0, x_4);
lean_closure_set(x_14, 1, x_3);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_2);
lean_closure_set(x_14, 4, x_13);
x_15 = l_Nat_foldRevMAux___main___rarg(x_12, x_14, x_7, x_11);
lean_dec(x_7);
x_16 = lean_apply_1(x_15, x_10);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
return x_8;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Lean_MetavarContext_MkBinding_mkBinding___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l_Lean_MetavarContext_MkBinding_mkBinding___lambda__1(x_1, x_2, x_3, x_4, x_9, x_6, x_7, x_8);
lean_dec(x_6);
return x_10;
}
}
lean_object* l_Lean_MetavarContext_MkBinding_mkBinding___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Lean_MetavarContext_MkBinding_mkBinding(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_MetavarContext_MkBinding_mkLambda(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = 1;
x_7 = l_Lean_MetavarContext_MkBinding_mkBinding(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_MetavarContext_MkBinding_mkForall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = 0;
x_7 = l_Lean_MetavarContext_MkBinding_mkBinding(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_12__getLocalDeclWithSmallestIdx___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_9 = l_Lean_LocalContext_findFVar(x_1, x_8);
lean_dec(x_8);
x_10 = l_Lean_LocalDecl_index(x_5);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = l_Lean_LocalDecl_Inhabited;
x_14 = l_Option_get_x21___rarg___closed__3;
x_15 = lean_panic_fn(x_14);
x_16 = l_Lean_LocalDecl_index(x_15);
x_17 = lean_nat_dec_lt(x_16, x_10);
lean_dec(x_10);
lean_dec(x_16);
if (x_17 == 0)
{
lean_dec(x_15);
x_4 = x_12;
goto _start;
}
else
{
lean_dec(x_5);
x_4 = x_12;
x_5 = x_15;
goto _start;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_9, 0);
lean_inc(x_20);
lean_dec(x_9);
x_21 = l_Lean_LocalDecl_index(x_20);
x_22 = lean_nat_dec_lt(x_21, x_10);
lean_dec(x_10);
lean_dec(x_21);
if (x_22 == 0)
{
lean_dec(x_20);
x_4 = x_12;
goto _start;
}
else
{
lean_dec(x_5);
x_4 = x_12;
x_5 = x_20;
goto _start;
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_12__getLocalDeclWithSmallestIdx___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_9 = l_Lean_LocalContext_findFVar(x_1, x_8);
lean_dec(x_8);
x_10 = l_Lean_LocalDecl_index(x_5);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = l_Lean_LocalDecl_Inhabited;
x_14 = l_Option_get_x21___rarg___closed__3;
x_15 = lean_panic_fn(x_14);
x_16 = l_Lean_LocalDecl_index(x_15);
x_17 = lean_nat_dec_lt(x_16, x_10);
lean_dec(x_10);
lean_dec(x_16);
if (x_17 == 0)
{
lean_dec(x_15);
x_4 = x_12;
goto _start;
}
else
{
lean_dec(x_5);
x_4 = x_12;
x_5 = x_15;
goto _start;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_9, 0);
lean_inc(x_20);
lean_dec(x_9);
x_21 = l_Lean_LocalDecl_index(x_20);
x_22 = lean_nat_dec_lt(x_21, x_10);
lean_dec(x_10);
lean_dec(x_21);
if (x_22 == 0)
{
lean_dec(x_20);
x_4 = x_12;
goto _start;
}
else
{
lean_dec(x_5);
x_4 = x_12;
x_5 = x_20;
goto _start;
}
}
}
}
}
lean_object* l___private_Init_Lean_MetavarContext_12__getLocalDeclWithSmallestIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_Expr_Inhabited;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get(x_3, x_2, x_4);
lean_inc(x_1);
x_6 = l_Lean_LocalContext_findFVar(x_1, x_5);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_LocalDecl_Inhabited;
x_8 = l_Option_get_x21___rarg___closed__3;
x_9 = lean_panic_fn(x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_12__getLocalDeclWithSmallestIdx___spec__1(x_1, x_2, x_2, x_10, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_12__getLocalDeclWithSmallestIdx___spec__2(x_1, x_2, x_2, x_13, x_12);
return x_14;
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_12__getLocalDeclWithSmallestIdx___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_12__getLocalDeclWithSmallestIdx___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_12__getLocalDeclWithSmallestIdx___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_12__getLocalDeclWithSmallestIdx___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l___private_Init_Lean_MetavarContext_12__getLocalDeclWithSmallestIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_MetavarContext_12__getLocalDeclWithSmallestIdx(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = l_Lean_LocalDecl_fvarId(x_2);
x_10 = l_Lean_Expr_fvarId_x21(x_8);
lean_dec(x_8);
x_11 = lean_name_eq(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_5 = x_13;
goto _start;
}
else
{
lean_dec(x_5);
return x_11;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = l_Lean_Expr_fvarId_x21(x_8);
lean_dec(x_8);
x_10 = lean_name_eq(x_9, x_2);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_5, x_11);
lean_dec(x_5);
x_5 = x_12;
goto _start;
}
else
{
lean_dec(x_5);
return x_10;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__5(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_5, x_10);
lean_dec(x_5);
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_5);
return x_9;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_array_fget(x_3, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_5, x_9);
lean_dec(x_5);
x_5 = x_10;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = l_Lean_LocalDecl_fvarId(x_12);
lean_dec(x_12);
x_14 = lean_array_get_size(x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__2(x_1, x_13, x_1, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_5, x_17);
lean_dec(x_5);
x_5 = x_18;
goto _start;
}
else
{
lean_dec(x_5);
return x_16;
}
}
}
}
}
uint8_t l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__6(x_1, x_3, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__7(x_1, x_7, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_array_fget(x_3, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_5, x_9);
lean_dec(x_5);
x_5 = x_10;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = l_Lean_LocalDecl_fvarId(x_12);
lean_dec(x_12);
x_14 = lean_array_get_size(x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__2(x_1, x_13, x_1, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_5, x_17);
lean_dec(x_5);
x_5 = x_18;
goto _start;
}
else
{
lean_dec(x_5);
return x_16;
}
}
}
}
}
uint8_t l_PersistentArray_anyM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__5(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__8(x_1, x_2, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
else
{
return x_4;
}
}
}
lean_object* l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_array_get_size(x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__2(x_1, x_5, x_1, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
lean_inc(x_11);
lean_inc(x_2);
x_12 = lean_metavar_ctx_get_expr_assignment(x_2, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_13 = l_Lean_MetavarContext_getDecl(x_2, x_11);
lean_dec(x_11);
lean_dec(x_2);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_PersistentArray_anyM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__4(x_1, x_15);
lean_dec(x_15);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_11);
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
lean_inc(x_19);
x_20 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_19, x_4);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
if (x_22 == 0)
{
uint8_t x_23; 
lean_dec(x_19);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_20, 0);
lean_dec(x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; 
lean_dec(x_21);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_dec(x_20);
x_3 = x_19;
x_4 = x_27;
goto _start;
}
}
}
case 5:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_3, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_3, 1);
lean_inc(x_30);
lean_dec(x_3);
lean_inc(x_30);
x_31 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_30, x_4);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
lean_dec(x_30);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = l_Lean_Expr_isApp(x_29);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_inc(x_29);
x_36 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_29, x_34);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
if (x_38 == 0)
{
uint8_t x_39; 
lean_dec(x_29);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_36, 0);
lean_dec(x_40);
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_dec(x_36);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_object* x_43; 
lean_dec(x_37);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
lean_dec(x_36);
x_3 = x_29;
x_4 = x_43;
goto _start;
}
}
else
{
x_3 = x_29;
x_4 = x_34;
goto _start;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_31, 1);
lean_inc(x_46);
lean_dec(x_31);
lean_inc(x_2);
x_47 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__3(x_1, x_2, x_30, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_unbox(x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
lean_dec(x_48);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = l_Lean_Expr_isApp(x_29);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_inc(x_29);
x_52 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_29, x_50);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
if (x_54 == 0)
{
uint8_t x_55; 
lean_dec(x_29);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_52);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_52, 0);
lean_dec(x_56);
return x_52;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_52, 1);
lean_inc(x_57);
lean_dec(x_52);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
else
{
lean_object* x_59; 
lean_dec(x_53);
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_dec(x_52);
x_3 = x_29;
x_4 = x_59;
goto _start;
}
}
else
{
x_3 = x_29;
x_4 = x_50;
goto _start;
}
}
else
{
uint8_t x_62; 
lean_dec(x_29);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_47);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_47, 0);
lean_dec(x_63);
return x_47;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_47, 1);
lean_inc(x_64);
lean_dec(x_47);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_48);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
case 6:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_66 = lean_ctor_get(x_3, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_3, 2);
lean_inc(x_67);
lean_dec(x_3);
lean_inc(x_66);
x_68 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_66, x_4);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_unbox(x_69);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_dec(x_66);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
lean_inc(x_67);
x_72 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_67, x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
if (x_74 == 0)
{
uint8_t x_75; 
lean_dec(x_67);
lean_dec(x_2);
x_75 = !lean_is_exclusive(x_72);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_72, 0);
lean_dec(x_76);
return x_72;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
lean_dec(x_72);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_73);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
else
{
lean_object* x_79; 
lean_dec(x_73);
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
lean_dec(x_72);
x_3 = x_67;
x_4 = x_79;
goto _start;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_81 = lean_ctor_get(x_68, 1);
lean_inc(x_81);
lean_dec(x_68);
lean_inc(x_2);
x_82 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__3(x_1, x_2, x_66, x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_unbox(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
lean_dec(x_83);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
lean_inc(x_67);
x_86 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_67, x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_unbox(x_87);
if (x_88 == 0)
{
uint8_t x_89; 
lean_dec(x_67);
lean_dec(x_2);
x_89 = !lean_is_exclusive(x_86);
if (x_89 == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_86, 0);
lean_dec(x_90);
return x_86;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_86, 1);
lean_inc(x_91);
lean_dec(x_86);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_87);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
else
{
lean_object* x_93; 
lean_dec(x_87);
x_93 = lean_ctor_get(x_86, 1);
lean_inc(x_93);
lean_dec(x_86);
x_3 = x_67;
x_4 = x_93;
goto _start;
}
}
else
{
uint8_t x_95; 
lean_dec(x_67);
lean_dec(x_2);
x_95 = !lean_is_exclusive(x_82);
if (x_95 == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_82, 0);
lean_dec(x_96);
return x_82;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_82, 1);
lean_inc(x_97);
lean_dec(x_82);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_83);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
case 7:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_99 = lean_ctor_get(x_3, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_3, 2);
lean_inc(x_100);
lean_dec(x_3);
lean_inc(x_99);
x_101 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_99, x_4);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_unbox(x_102);
lean_dec(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
lean_dec(x_99);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
lean_dec(x_101);
lean_inc(x_100);
x_105 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_100, x_104);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_unbox(x_106);
if (x_107 == 0)
{
uint8_t x_108; 
lean_dec(x_100);
lean_dec(x_2);
x_108 = !lean_is_exclusive(x_105);
if (x_108 == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_105, 0);
lean_dec(x_109);
return x_105;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_105, 1);
lean_inc(x_110);
lean_dec(x_105);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_106);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
else
{
lean_object* x_112; 
lean_dec(x_106);
x_112 = lean_ctor_get(x_105, 1);
lean_inc(x_112);
lean_dec(x_105);
x_3 = x_100;
x_4 = x_112;
goto _start;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_114 = lean_ctor_get(x_101, 1);
lean_inc(x_114);
lean_dec(x_101);
lean_inc(x_2);
x_115 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__3(x_1, x_2, x_99, x_114);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_unbox(x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
lean_dec(x_116);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec(x_115);
lean_inc(x_100);
x_119 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_100, x_118);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_unbox(x_120);
if (x_121 == 0)
{
uint8_t x_122; 
lean_dec(x_100);
lean_dec(x_2);
x_122 = !lean_is_exclusive(x_119);
if (x_122 == 0)
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_119, 0);
lean_dec(x_123);
return x_119;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_119, 1);
lean_inc(x_124);
lean_dec(x_119);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_120);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
else
{
lean_object* x_126; 
lean_dec(x_120);
x_126 = lean_ctor_get(x_119, 1);
lean_inc(x_126);
lean_dec(x_119);
x_3 = x_100;
x_4 = x_126;
goto _start;
}
}
else
{
uint8_t x_128; 
lean_dec(x_100);
lean_dec(x_2);
x_128 = !lean_is_exclusive(x_115);
if (x_128 == 0)
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_115, 0);
lean_dec(x_129);
return x_115;
}
else
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_115, 1);
lean_inc(x_130);
lean_dec(x_115);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_116);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
}
case 8:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_132 = lean_ctor_get(x_3, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_3, 2);
lean_inc(x_133);
x_134 = lean_ctor_get(x_3, 3);
lean_inc(x_134);
lean_dec(x_3);
lean_inc(x_132);
x_171 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_132, x_4);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_unbox(x_172);
if (x_173 == 0)
{
lean_object* x_174; uint8_t x_175; 
lean_dec(x_132);
x_174 = lean_ctor_get(x_171, 1);
lean_inc(x_174);
lean_dec(x_171);
x_175 = lean_unbox(x_172);
lean_dec(x_172);
x_135 = x_175;
x_136 = x_174;
goto block_170;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
lean_dec(x_172);
x_176 = lean_ctor_get(x_171, 1);
lean_inc(x_176);
lean_dec(x_171);
lean_inc(x_2);
x_177 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__3(x_1, x_2, x_132, x_176);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = lean_unbox(x_178);
lean_dec(x_178);
x_135 = x_180;
x_136 = x_179;
goto block_170;
}
block_170:
{
if (x_135 == 0)
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; 
lean_inc(x_133);
x_137 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_133, x_136);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_unbox(x_138);
lean_dec(x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
lean_dec(x_133);
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
lean_dec(x_137);
lean_inc(x_134);
x_141 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_134, x_140);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_unbox(x_142);
if (x_143 == 0)
{
uint8_t x_144; 
lean_dec(x_134);
lean_dec(x_2);
x_144 = !lean_is_exclusive(x_141);
if (x_144 == 0)
{
lean_object* x_145; 
x_145 = lean_ctor_get(x_141, 0);
lean_dec(x_145);
return x_141;
}
else
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_141, 1);
lean_inc(x_146);
lean_dec(x_141);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_142);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
else
{
lean_object* x_148; 
lean_dec(x_142);
x_148 = lean_ctor_get(x_141, 1);
lean_inc(x_148);
lean_dec(x_141);
x_3 = x_134;
x_4 = x_148;
goto _start;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_150 = lean_ctor_get(x_137, 1);
lean_inc(x_150);
lean_dec(x_137);
lean_inc(x_2);
x_151 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__3(x_1, x_2, x_133, x_150);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_unbox(x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
lean_dec(x_152);
x_154 = lean_ctor_get(x_151, 1);
lean_inc(x_154);
lean_dec(x_151);
lean_inc(x_134);
x_155 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_134, x_154);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_unbox(x_156);
if (x_157 == 0)
{
uint8_t x_158; 
lean_dec(x_134);
lean_dec(x_2);
x_158 = !lean_is_exclusive(x_155);
if (x_158 == 0)
{
lean_object* x_159; 
x_159 = lean_ctor_get(x_155, 0);
lean_dec(x_159);
return x_155;
}
else
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_155, 1);
lean_inc(x_160);
lean_dec(x_155);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_156);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
else
{
lean_object* x_162; 
lean_dec(x_156);
x_162 = lean_ctor_get(x_155, 1);
lean_inc(x_162);
lean_dec(x_155);
x_3 = x_134;
x_4 = x_162;
goto _start;
}
}
else
{
uint8_t x_164; 
lean_dec(x_134);
lean_dec(x_2);
x_164 = !lean_is_exclusive(x_151);
if (x_164 == 0)
{
lean_object* x_165; 
x_165 = lean_ctor_get(x_151, 0);
lean_dec(x_165);
return x_151;
}
else
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_151, 1);
lean_inc(x_166);
lean_dec(x_151);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_152);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
}
else
{
lean_object* x_168; lean_object* x_169; 
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_2);
x_168 = lean_box(x_135);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_136);
return x_169;
}
}
}
case 10:
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_181 = lean_ctor_get(x_3, 1);
lean_inc(x_181);
lean_dec(x_3);
lean_inc(x_181);
x_182 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_181, x_4);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_unbox(x_183);
if (x_184 == 0)
{
uint8_t x_185; 
lean_dec(x_181);
lean_dec(x_2);
x_185 = !lean_is_exclusive(x_182);
if (x_185 == 0)
{
lean_object* x_186; 
x_186 = lean_ctor_get(x_182, 0);
lean_dec(x_186);
return x_182;
}
else
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_ctor_get(x_182, 1);
lean_inc(x_187);
lean_dec(x_182);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_183);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
else
{
lean_object* x_189; 
lean_dec(x_183);
x_189 = lean_ctor_get(x_182, 1);
lean_inc(x_189);
lean_dec(x_182);
x_3 = x_181;
x_4 = x_189;
goto _start;
}
}
case 11:
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_191 = lean_ctor_get(x_3, 2);
lean_inc(x_191);
lean_dec(x_3);
lean_inc(x_191);
x_192 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_191, x_4);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_unbox(x_193);
if (x_194 == 0)
{
uint8_t x_195; 
lean_dec(x_191);
lean_dec(x_2);
x_195 = !lean_is_exclusive(x_192);
if (x_195 == 0)
{
lean_object* x_196; 
x_196 = lean_ctor_get(x_192, 0);
lean_dec(x_196);
return x_192;
}
else
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_192, 1);
lean_inc(x_197);
lean_dec(x_192);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_193);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
else
{
lean_object* x_199; 
lean_dec(x_193);
x_199 = lean_ctor_get(x_192, 1);
lean_inc(x_199);
lean_dec(x_192);
x_3 = x_191;
x_4 = x_199;
goto _start;
}
}
default: 
{
uint8_t x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_3);
lean_dec(x_2);
x_201 = 0;
x_202 = lean_box(x_201);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_4);
return x_203;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__11(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_5, x_10);
lean_dec(x_5);
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_5);
return x_9;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_array_fget(x_3, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_5, x_9);
lean_dec(x_5);
x_5 = x_10;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = l_Lean_LocalDecl_fvarId(x_12);
lean_dec(x_12);
x_14 = lean_array_get_size(x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__2(x_1, x_13, x_1, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_5, x_17);
lean_dec(x_5);
x_5 = x_18;
goto _start;
}
else
{
lean_dec(x_5);
return x_16;
}
}
}
}
}
uint8_t l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__11(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__12(x_1, x_3, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__13(x_1, x_7, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_array_fget(x_3, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_5, x_9);
lean_dec(x_5);
x_5 = x_10;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = l_Lean_LocalDecl_fvarId(x_12);
lean_dec(x_12);
x_14 = lean_array_get_size(x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__2(x_1, x_13, x_1, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_5, x_17);
lean_dec(x_5);
x_5 = x_18;
goto _start;
}
else
{
lean_dec(x_5);
return x_16;
}
}
}
}
}
uint8_t l_PersistentArray_anyM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__10(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__11(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__14(x_1, x_2, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
else
{
return x_4;
}
}
}
lean_object* l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_array_get_size(x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__2(x_1, x_5, x_1, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
lean_inc(x_11);
lean_inc(x_2);
x_12 = lean_metavar_ctx_get_expr_assignment(x_2, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_13 = l_Lean_MetavarContext_getDecl(x_2, x_11);
lean_dec(x_11);
lean_dec(x_2);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_PersistentArray_anyM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__10(x_1, x_15);
lean_dec(x_15);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_11);
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
lean_inc(x_19);
x_20 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_19, x_4);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
if (x_22 == 0)
{
uint8_t x_23; 
lean_dec(x_19);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_20, 0);
lean_dec(x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; 
lean_dec(x_21);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_dec(x_20);
x_3 = x_19;
x_4 = x_27;
goto _start;
}
}
}
case 5:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_3, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_3, 1);
lean_inc(x_30);
lean_dec(x_3);
lean_inc(x_30);
x_31 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_30, x_4);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
lean_dec(x_30);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = l_Lean_Expr_isApp(x_29);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_inc(x_29);
x_36 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_29, x_34);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
if (x_38 == 0)
{
uint8_t x_39; 
lean_dec(x_29);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_36, 0);
lean_dec(x_40);
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_dec(x_36);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_object* x_43; 
lean_dec(x_37);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
lean_dec(x_36);
x_3 = x_29;
x_4 = x_43;
goto _start;
}
}
else
{
x_3 = x_29;
x_4 = x_34;
goto _start;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_31, 1);
lean_inc(x_46);
lean_dec(x_31);
lean_inc(x_2);
x_47 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__9(x_1, x_2, x_30, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_unbox(x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
lean_dec(x_48);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = l_Lean_Expr_isApp(x_29);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_inc(x_29);
x_52 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_29, x_50);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
if (x_54 == 0)
{
uint8_t x_55; 
lean_dec(x_29);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_52);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_52, 0);
lean_dec(x_56);
return x_52;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_52, 1);
lean_inc(x_57);
lean_dec(x_52);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
else
{
lean_object* x_59; 
lean_dec(x_53);
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_dec(x_52);
x_3 = x_29;
x_4 = x_59;
goto _start;
}
}
else
{
x_3 = x_29;
x_4 = x_50;
goto _start;
}
}
else
{
uint8_t x_62; 
lean_dec(x_29);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_47);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_47, 0);
lean_dec(x_63);
return x_47;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_47, 1);
lean_inc(x_64);
lean_dec(x_47);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_48);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
case 6:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_66 = lean_ctor_get(x_3, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_3, 2);
lean_inc(x_67);
lean_dec(x_3);
lean_inc(x_66);
x_68 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_66, x_4);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_unbox(x_69);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_dec(x_66);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
lean_inc(x_67);
x_72 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_67, x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
if (x_74 == 0)
{
uint8_t x_75; 
lean_dec(x_67);
lean_dec(x_2);
x_75 = !lean_is_exclusive(x_72);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_72, 0);
lean_dec(x_76);
return x_72;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
lean_dec(x_72);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_73);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
else
{
lean_object* x_79; 
lean_dec(x_73);
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
lean_dec(x_72);
x_3 = x_67;
x_4 = x_79;
goto _start;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_81 = lean_ctor_get(x_68, 1);
lean_inc(x_81);
lean_dec(x_68);
lean_inc(x_2);
x_82 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__9(x_1, x_2, x_66, x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_unbox(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
lean_dec(x_83);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
lean_inc(x_67);
x_86 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_67, x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_unbox(x_87);
if (x_88 == 0)
{
uint8_t x_89; 
lean_dec(x_67);
lean_dec(x_2);
x_89 = !lean_is_exclusive(x_86);
if (x_89 == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_86, 0);
lean_dec(x_90);
return x_86;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_86, 1);
lean_inc(x_91);
lean_dec(x_86);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_87);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
else
{
lean_object* x_93; 
lean_dec(x_87);
x_93 = lean_ctor_get(x_86, 1);
lean_inc(x_93);
lean_dec(x_86);
x_3 = x_67;
x_4 = x_93;
goto _start;
}
}
else
{
uint8_t x_95; 
lean_dec(x_67);
lean_dec(x_2);
x_95 = !lean_is_exclusive(x_82);
if (x_95 == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_82, 0);
lean_dec(x_96);
return x_82;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_82, 1);
lean_inc(x_97);
lean_dec(x_82);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_83);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
case 7:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_99 = lean_ctor_get(x_3, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_3, 2);
lean_inc(x_100);
lean_dec(x_3);
lean_inc(x_99);
x_101 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_99, x_4);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_unbox(x_102);
lean_dec(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
lean_dec(x_99);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
lean_dec(x_101);
lean_inc(x_100);
x_105 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_100, x_104);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_unbox(x_106);
if (x_107 == 0)
{
uint8_t x_108; 
lean_dec(x_100);
lean_dec(x_2);
x_108 = !lean_is_exclusive(x_105);
if (x_108 == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_105, 0);
lean_dec(x_109);
return x_105;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_105, 1);
lean_inc(x_110);
lean_dec(x_105);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_106);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
else
{
lean_object* x_112; 
lean_dec(x_106);
x_112 = lean_ctor_get(x_105, 1);
lean_inc(x_112);
lean_dec(x_105);
x_3 = x_100;
x_4 = x_112;
goto _start;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_114 = lean_ctor_get(x_101, 1);
lean_inc(x_114);
lean_dec(x_101);
lean_inc(x_2);
x_115 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__9(x_1, x_2, x_99, x_114);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_unbox(x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
lean_dec(x_116);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec(x_115);
lean_inc(x_100);
x_119 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_100, x_118);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_unbox(x_120);
if (x_121 == 0)
{
uint8_t x_122; 
lean_dec(x_100);
lean_dec(x_2);
x_122 = !lean_is_exclusive(x_119);
if (x_122 == 0)
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_119, 0);
lean_dec(x_123);
return x_119;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_119, 1);
lean_inc(x_124);
lean_dec(x_119);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_120);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
else
{
lean_object* x_126; 
lean_dec(x_120);
x_126 = lean_ctor_get(x_119, 1);
lean_inc(x_126);
lean_dec(x_119);
x_3 = x_100;
x_4 = x_126;
goto _start;
}
}
else
{
uint8_t x_128; 
lean_dec(x_100);
lean_dec(x_2);
x_128 = !lean_is_exclusive(x_115);
if (x_128 == 0)
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_115, 0);
lean_dec(x_129);
return x_115;
}
else
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_115, 1);
lean_inc(x_130);
lean_dec(x_115);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_116);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
}
case 8:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_132 = lean_ctor_get(x_3, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_3, 2);
lean_inc(x_133);
x_134 = lean_ctor_get(x_3, 3);
lean_inc(x_134);
lean_dec(x_3);
lean_inc(x_132);
x_171 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_132, x_4);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_unbox(x_172);
if (x_173 == 0)
{
lean_object* x_174; uint8_t x_175; 
lean_dec(x_132);
x_174 = lean_ctor_get(x_171, 1);
lean_inc(x_174);
lean_dec(x_171);
x_175 = lean_unbox(x_172);
lean_dec(x_172);
x_135 = x_175;
x_136 = x_174;
goto block_170;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
lean_dec(x_172);
x_176 = lean_ctor_get(x_171, 1);
lean_inc(x_176);
lean_dec(x_171);
lean_inc(x_2);
x_177 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__9(x_1, x_2, x_132, x_176);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = lean_unbox(x_178);
lean_dec(x_178);
x_135 = x_180;
x_136 = x_179;
goto block_170;
}
block_170:
{
if (x_135 == 0)
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; 
lean_inc(x_133);
x_137 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_133, x_136);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_unbox(x_138);
lean_dec(x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
lean_dec(x_133);
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
lean_dec(x_137);
lean_inc(x_134);
x_141 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_134, x_140);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_unbox(x_142);
if (x_143 == 0)
{
uint8_t x_144; 
lean_dec(x_134);
lean_dec(x_2);
x_144 = !lean_is_exclusive(x_141);
if (x_144 == 0)
{
lean_object* x_145; 
x_145 = lean_ctor_get(x_141, 0);
lean_dec(x_145);
return x_141;
}
else
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_141, 1);
lean_inc(x_146);
lean_dec(x_141);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_142);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
else
{
lean_object* x_148; 
lean_dec(x_142);
x_148 = lean_ctor_get(x_141, 1);
lean_inc(x_148);
lean_dec(x_141);
x_3 = x_134;
x_4 = x_148;
goto _start;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_150 = lean_ctor_get(x_137, 1);
lean_inc(x_150);
lean_dec(x_137);
lean_inc(x_2);
x_151 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__9(x_1, x_2, x_133, x_150);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_unbox(x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
lean_dec(x_152);
x_154 = lean_ctor_get(x_151, 1);
lean_inc(x_154);
lean_dec(x_151);
lean_inc(x_134);
x_155 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_134, x_154);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_unbox(x_156);
if (x_157 == 0)
{
uint8_t x_158; 
lean_dec(x_134);
lean_dec(x_2);
x_158 = !lean_is_exclusive(x_155);
if (x_158 == 0)
{
lean_object* x_159; 
x_159 = lean_ctor_get(x_155, 0);
lean_dec(x_159);
return x_155;
}
else
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_155, 1);
lean_inc(x_160);
lean_dec(x_155);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_156);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
else
{
lean_object* x_162; 
lean_dec(x_156);
x_162 = lean_ctor_get(x_155, 1);
lean_inc(x_162);
lean_dec(x_155);
x_3 = x_134;
x_4 = x_162;
goto _start;
}
}
else
{
uint8_t x_164; 
lean_dec(x_134);
lean_dec(x_2);
x_164 = !lean_is_exclusive(x_151);
if (x_164 == 0)
{
lean_object* x_165; 
x_165 = lean_ctor_get(x_151, 0);
lean_dec(x_165);
return x_151;
}
else
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_151, 1);
lean_inc(x_166);
lean_dec(x_151);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_152);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
}
else
{
lean_object* x_168; lean_object* x_169; 
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_2);
x_168 = lean_box(x_135);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_136);
return x_169;
}
}
}
case 10:
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_181 = lean_ctor_get(x_3, 1);
lean_inc(x_181);
lean_dec(x_3);
lean_inc(x_181);
x_182 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_181, x_4);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_unbox(x_183);
if (x_184 == 0)
{
uint8_t x_185; 
lean_dec(x_181);
lean_dec(x_2);
x_185 = !lean_is_exclusive(x_182);
if (x_185 == 0)
{
lean_object* x_186; 
x_186 = lean_ctor_get(x_182, 0);
lean_dec(x_186);
return x_182;
}
else
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_ctor_get(x_182, 1);
lean_inc(x_187);
lean_dec(x_182);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_183);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
else
{
lean_object* x_189; 
lean_dec(x_183);
x_189 = lean_ctor_get(x_182, 1);
lean_inc(x_189);
lean_dec(x_182);
x_3 = x_181;
x_4 = x_189;
goto _start;
}
}
case 11:
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_191 = lean_ctor_get(x_3, 2);
lean_inc(x_191);
lean_dec(x_3);
lean_inc(x_191);
x_192 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_191, x_4);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_unbox(x_193);
if (x_194 == 0)
{
uint8_t x_195; 
lean_dec(x_191);
lean_dec(x_2);
x_195 = !lean_is_exclusive(x_192);
if (x_195 == 0)
{
lean_object* x_196; 
x_196 = lean_ctor_get(x_192, 0);
lean_dec(x_196);
return x_192;
}
else
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_192, 1);
lean_inc(x_197);
lean_dec(x_192);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_193);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
else
{
lean_object* x_199; 
lean_dec(x_193);
x_199 = lean_ctor_get(x_192, 1);
lean_inc(x_199);
lean_dec(x_192);
x_3 = x_191;
x_4 = x_199;
goto _start;
}
}
default: 
{
uint8_t x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_3);
lean_dec(x_2);
x_201 = 0;
x_202 = lean_box(x_201);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_4);
return x_203;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__17(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_5, x_10);
lean_dec(x_5);
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_5);
return x_9;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_array_fget(x_3, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_5, x_9);
lean_dec(x_5);
x_5 = x_10;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = l_Lean_LocalDecl_fvarId(x_12);
lean_dec(x_12);
x_14 = lean_array_get_size(x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__2(x_1, x_13, x_1, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_5, x_17);
lean_dec(x_5);
x_5 = x_18;
goto _start;
}
else
{
lean_dec(x_5);
return x_16;
}
}
}
}
}
uint8_t l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__17(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__18(x_1, x_3, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__19(x_1, x_7, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_array_fget(x_3, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_5, x_9);
lean_dec(x_5);
x_5 = x_10;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = l_Lean_LocalDecl_fvarId(x_12);
lean_dec(x_12);
x_14 = lean_array_get_size(x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__2(x_1, x_13, x_1, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_5, x_17);
lean_dec(x_5);
x_5 = x_18;
goto _start;
}
else
{
lean_dec(x_5);
return x_16;
}
}
}
}
}
uint8_t l_PersistentArray_anyM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__16(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__17(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__20(x_1, x_2, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
else
{
return x_4;
}
}
}
lean_object* l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_array_get_size(x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__2(x_1, x_5, x_1, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
lean_inc(x_11);
lean_inc(x_2);
x_12 = lean_metavar_ctx_get_expr_assignment(x_2, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_13 = l_Lean_MetavarContext_getDecl(x_2, x_11);
lean_dec(x_11);
lean_dec(x_2);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_PersistentArray_anyM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__16(x_1, x_15);
lean_dec(x_15);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_11);
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
lean_inc(x_19);
x_20 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_19, x_4);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
if (x_22 == 0)
{
uint8_t x_23; 
lean_dec(x_19);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_20, 0);
lean_dec(x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; 
lean_dec(x_21);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_dec(x_20);
x_3 = x_19;
x_4 = x_27;
goto _start;
}
}
}
case 5:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_3, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_3, 1);
lean_inc(x_30);
lean_dec(x_3);
lean_inc(x_30);
x_31 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_30, x_4);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
lean_dec(x_30);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = l_Lean_Expr_isApp(x_29);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_inc(x_29);
x_36 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_29, x_34);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
if (x_38 == 0)
{
uint8_t x_39; 
lean_dec(x_29);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_36, 0);
lean_dec(x_40);
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_dec(x_36);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_object* x_43; 
lean_dec(x_37);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
lean_dec(x_36);
x_3 = x_29;
x_4 = x_43;
goto _start;
}
}
else
{
x_3 = x_29;
x_4 = x_34;
goto _start;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_31, 1);
lean_inc(x_46);
lean_dec(x_31);
lean_inc(x_2);
x_47 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__15(x_1, x_2, x_30, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_unbox(x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
lean_dec(x_48);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = l_Lean_Expr_isApp(x_29);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_inc(x_29);
x_52 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_29, x_50);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
if (x_54 == 0)
{
uint8_t x_55; 
lean_dec(x_29);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_52);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_52, 0);
lean_dec(x_56);
return x_52;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_52, 1);
lean_inc(x_57);
lean_dec(x_52);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
else
{
lean_object* x_59; 
lean_dec(x_53);
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_dec(x_52);
x_3 = x_29;
x_4 = x_59;
goto _start;
}
}
else
{
x_3 = x_29;
x_4 = x_50;
goto _start;
}
}
else
{
uint8_t x_62; 
lean_dec(x_29);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_47);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_47, 0);
lean_dec(x_63);
return x_47;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_47, 1);
lean_inc(x_64);
lean_dec(x_47);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_48);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
case 6:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_66 = lean_ctor_get(x_3, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_3, 2);
lean_inc(x_67);
lean_dec(x_3);
lean_inc(x_66);
x_68 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_66, x_4);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_unbox(x_69);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_dec(x_66);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
lean_inc(x_67);
x_72 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_67, x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
if (x_74 == 0)
{
uint8_t x_75; 
lean_dec(x_67);
lean_dec(x_2);
x_75 = !lean_is_exclusive(x_72);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_72, 0);
lean_dec(x_76);
return x_72;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
lean_dec(x_72);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_73);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
else
{
lean_object* x_79; 
lean_dec(x_73);
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
lean_dec(x_72);
x_3 = x_67;
x_4 = x_79;
goto _start;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_81 = lean_ctor_get(x_68, 1);
lean_inc(x_81);
lean_dec(x_68);
lean_inc(x_2);
x_82 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__15(x_1, x_2, x_66, x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_unbox(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
lean_dec(x_83);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
lean_inc(x_67);
x_86 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_67, x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_unbox(x_87);
if (x_88 == 0)
{
uint8_t x_89; 
lean_dec(x_67);
lean_dec(x_2);
x_89 = !lean_is_exclusive(x_86);
if (x_89 == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_86, 0);
lean_dec(x_90);
return x_86;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_86, 1);
lean_inc(x_91);
lean_dec(x_86);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_87);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
else
{
lean_object* x_93; 
lean_dec(x_87);
x_93 = lean_ctor_get(x_86, 1);
lean_inc(x_93);
lean_dec(x_86);
x_3 = x_67;
x_4 = x_93;
goto _start;
}
}
else
{
uint8_t x_95; 
lean_dec(x_67);
lean_dec(x_2);
x_95 = !lean_is_exclusive(x_82);
if (x_95 == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_82, 0);
lean_dec(x_96);
return x_82;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_82, 1);
lean_inc(x_97);
lean_dec(x_82);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_83);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
case 7:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_99 = lean_ctor_get(x_3, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_3, 2);
lean_inc(x_100);
lean_dec(x_3);
lean_inc(x_99);
x_101 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_99, x_4);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_unbox(x_102);
lean_dec(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
lean_dec(x_99);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
lean_dec(x_101);
lean_inc(x_100);
x_105 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_100, x_104);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_unbox(x_106);
if (x_107 == 0)
{
uint8_t x_108; 
lean_dec(x_100);
lean_dec(x_2);
x_108 = !lean_is_exclusive(x_105);
if (x_108 == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_105, 0);
lean_dec(x_109);
return x_105;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_105, 1);
lean_inc(x_110);
lean_dec(x_105);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_106);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
else
{
lean_object* x_112; 
lean_dec(x_106);
x_112 = lean_ctor_get(x_105, 1);
lean_inc(x_112);
lean_dec(x_105);
x_3 = x_100;
x_4 = x_112;
goto _start;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_114 = lean_ctor_get(x_101, 1);
lean_inc(x_114);
lean_dec(x_101);
lean_inc(x_2);
x_115 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__15(x_1, x_2, x_99, x_114);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_unbox(x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
lean_dec(x_116);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec(x_115);
lean_inc(x_100);
x_119 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_100, x_118);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_unbox(x_120);
if (x_121 == 0)
{
uint8_t x_122; 
lean_dec(x_100);
lean_dec(x_2);
x_122 = !lean_is_exclusive(x_119);
if (x_122 == 0)
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_119, 0);
lean_dec(x_123);
return x_119;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_119, 1);
lean_inc(x_124);
lean_dec(x_119);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_120);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
else
{
lean_object* x_126; 
lean_dec(x_120);
x_126 = lean_ctor_get(x_119, 1);
lean_inc(x_126);
lean_dec(x_119);
x_3 = x_100;
x_4 = x_126;
goto _start;
}
}
else
{
uint8_t x_128; 
lean_dec(x_100);
lean_dec(x_2);
x_128 = !lean_is_exclusive(x_115);
if (x_128 == 0)
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_115, 0);
lean_dec(x_129);
return x_115;
}
else
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_115, 1);
lean_inc(x_130);
lean_dec(x_115);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_116);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
}
case 8:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_132 = lean_ctor_get(x_3, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_3, 2);
lean_inc(x_133);
x_134 = lean_ctor_get(x_3, 3);
lean_inc(x_134);
lean_dec(x_3);
lean_inc(x_132);
x_171 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_132, x_4);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_unbox(x_172);
if (x_173 == 0)
{
lean_object* x_174; uint8_t x_175; 
lean_dec(x_132);
x_174 = lean_ctor_get(x_171, 1);
lean_inc(x_174);
lean_dec(x_171);
x_175 = lean_unbox(x_172);
lean_dec(x_172);
x_135 = x_175;
x_136 = x_174;
goto block_170;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
lean_dec(x_172);
x_176 = lean_ctor_get(x_171, 1);
lean_inc(x_176);
lean_dec(x_171);
lean_inc(x_2);
x_177 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__15(x_1, x_2, x_132, x_176);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = lean_unbox(x_178);
lean_dec(x_178);
x_135 = x_180;
x_136 = x_179;
goto block_170;
}
block_170:
{
if (x_135 == 0)
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; 
lean_inc(x_133);
x_137 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_133, x_136);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_unbox(x_138);
lean_dec(x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
lean_dec(x_133);
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
lean_dec(x_137);
lean_inc(x_134);
x_141 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_134, x_140);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_unbox(x_142);
if (x_143 == 0)
{
uint8_t x_144; 
lean_dec(x_134);
lean_dec(x_2);
x_144 = !lean_is_exclusive(x_141);
if (x_144 == 0)
{
lean_object* x_145; 
x_145 = lean_ctor_get(x_141, 0);
lean_dec(x_145);
return x_141;
}
else
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_141, 1);
lean_inc(x_146);
lean_dec(x_141);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_142);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
else
{
lean_object* x_148; 
lean_dec(x_142);
x_148 = lean_ctor_get(x_141, 1);
lean_inc(x_148);
lean_dec(x_141);
x_3 = x_134;
x_4 = x_148;
goto _start;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_150 = lean_ctor_get(x_137, 1);
lean_inc(x_150);
lean_dec(x_137);
lean_inc(x_2);
x_151 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__15(x_1, x_2, x_133, x_150);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_unbox(x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
lean_dec(x_152);
x_154 = lean_ctor_get(x_151, 1);
lean_inc(x_154);
lean_dec(x_151);
lean_inc(x_134);
x_155 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_134, x_154);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_unbox(x_156);
if (x_157 == 0)
{
uint8_t x_158; 
lean_dec(x_134);
lean_dec(x_2);
x_158 = !lean_is_exclusive(x_155);
if (x_158 == 0)
{
lean_object* x_159; 
x_159 = lean_ctor_get(x_155, 0);
lean_dec(x_159);
return x_155;
}
else
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_155, 1);
lean_inc(x_160);
lean_dec(x_155);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_156);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
else
{
lean_object* x_162; 
lean_dec(x_156);
x_162 = lean_ctor_get(x_155, 1);
lean_inc(x_162);
lean_dec(x_155);
x_3 = x_134;
x_4 = x_162;
goto _start;
}
}
else
{
uint8_t x_164; 
lean_dec(x_134);
lean_dec(x_2);
x_164 = !lean_is_exclusive(x_151);
if (x_164 == 0)
{
lean_object* x_165; 
x_165 = lean_ctor_get(x_151, 0);
lean_dec(x_165);
return x_151;
}
else
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_151, 1);
lean_inc(x_166);
lean_dec(x_151);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_152);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
}
else
{
lean_object* x_168; lean_object* x_169; 
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_2);
x_168 = lean_box(x_135);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_136);
return x_169;
}
}
}
case 10:
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_181 = lean_ctor_get(x_3, 1);
lean_inc(x_181);
lean_dec(x_3);
lean_inc(x_181);
x_182 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_181, x_4);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_unbox(x_183);
if (x_184 == 0)
{
uint8_t x_185; 
lean_dec(x_181);
lean_dec(x_2);
x_185 = !lean_is_exclusive(x_182);
if (x_185 == 0)
{
lean_object* x_186; 
x_186 = lean_ctor_get(x_182, 0);
lean_dec(x_186);
return x_182;
}
else
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_ctor_get(x_182, 1);
lean_inc(x_187);
lean_dec(x_182);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_183);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
else
{
lean_object* x_189; 
lean_dec(x_183);
x_189 = lean_ctor_get(x_182, 1);
lean_inc(x_189);
lean_dec(x_182);
x_3 = x_181;
x_4 = x_189;
goto _start;
}
}
case 11:
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_191 = lean_ctor_get(x_3, 2);
lean_inc(x_191);
lean_dec(x_3);
lean_inc(x_191);
x_192 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_191, x_4);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_unbox(x_193);
if (x_194 == 0)
{
uint8_t x_195; 
lean_dec(x_191);
lean_dec(x_2);
x_195 = !lean_is_exclusive(x_192);
if (x_195 == 0)
{
lean_object* x_196; 
x_196 = lean_ctor_get(x_192, 0);
lean_dec(x_196);
return x_192;
}
else
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_192, 1);
lean_inc(x_197);
lean_dec(x_192);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_193);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
else
{
lean_object* x_199; 
lean_dec(x_193);
x_199 = lean_ctor_get(x_192, 1);
lean_inc(x_199);
lean_dec(x_192);
x_3 = x_191;
x_4 = x_199;
goto _start;
}
}
default: 
{
uint8_t x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_3);
lean_dec(x_2);
x_201 = 0;
x_202 = lean_box(x_201);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_4);
return x_203;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__24(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__23(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_5, x_10);
lean_dec(x_5);
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_5);
return x_9;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__25(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_array_fget(x_3, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_5, x_9);
lean_dec(x_5);
x_5 = x_10;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = l_Lean_LocalDecl_fvarId(x_12);
lean_dec(x_12);
x_14 = lean_array_get_size(x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__2(x_1, x_13, x_1, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_5, x_17);
lean_dec(x_5);
x_5 = x_18;
goto _start;
}
else
{
lean_dec(x_5);
return x_16;
}
}
}
}
}
uint8_t l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__23(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__24(x_1, x_3, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__25(x_1, x_7, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__26(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_array_fget(x_3, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_5, x_9);
lean_dec(x_5);
x_5 = x_10;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = l_Lean_LocalDecl_fvarId(x_12);
lean_dec(x_12);
x_14 = lean_array_get_size(x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__2(x_1, x_13, x_1, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_5, x_17);
lean_dec(x_5);
x_5 = x_18;
goto _start;
}
else
{
lean_dec(x_5);
return x_16;
}
}
}
}
}
uint8_t l_PersistentArray_anyM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__22(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__23(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__26(x_1, x_2, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
else
{
return x_4;
}
}
}
lean_object* l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_array_get_size(x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__2(x_1, x_5, x_1, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
lean_inc(x_11);
lean_inc(x_2);
x_12 = lean_metavar_ctx_get_expr_assignment(x_2, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_13 = l_Lean_MetavarContext_getDecl(x_2, x_11);
lean_dec(x_11);
lean_dec(x_2);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_PersistentArray_anyM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__22(x_1, x_15);
lean_dec(x_15);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_11);
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
lean_inc(x_19);
x_20 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_19, x_4);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
if (x_22 == 0)
{
uint8_t x_23; 
lean_dec(x_19);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_20, 0);
lean_dec(x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; 
lean_dec(x_21);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_dec(x_20);
x_3 = x_19;
x_4 = x_27;
goto _start;
}
}
}
case 5:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_3, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_3, 1);
lean_inc(x_30);
lean_dec(x_3);
lean_inc(x_30);
x_31 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_30, x_4);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
lean_dec(x_30);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = l_Lean_Expr_isApp(x_29);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_inc(x_29);
x_36 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_29, x_34);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
if (x_38 == 0)
{
uint8_t x_39; 
lean_dec(x_29);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_36, 0);
lean_dec(x_40);
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_dec(x_36);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_object* x_43; 
lean_dec(x_37);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
lean_dec(x_36);
x_3 = x_29;
x_4 = x_43;
goto _start;
}
}
else
{
x_3 = x_29;
x_4 = x_34;
goto _start;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_31, 1);
lean_inc(x_46);
lean_dec(x_31);
lean_inc(x_2);
x_47 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__21(x_1, x_2, x_30, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_unbox(x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
lean_dec(x_48);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = l_Lean_Expr_isApp(x_29);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_inc(x_29);
x_52 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_29, x_50);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
if (x_54 == 0)
{
uint8_t x_55; 
lean_dec(x_29);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_52);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_52, 0);
lean_dec(x_56);
return x_52;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_52, 1);
lean_inc(x_57);
lean_dec(x_52);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
else
{
lean_object* x_59; 
lean_dec(x_53);
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_dec(x_52);
x_3 = x_29;
x_4 = x_59;
goto _start;
}
}
else
{
x_3 = x_29;
x_4 = x_50;
goto _start;
}
}
else
{
uint8_t x_62; 
lean_dec(x_29);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_47);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_47, 0);
lean_dec(x_63);
return x_47;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_47, 1);
lean_inc(x_64);
lean_dec(x_47);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_48);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
case 6:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_66 = lean_ctor_get(x_3, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_3, 2);
lean_inc(x_67);
lean_dec(x_3);
lean_inc(x_66);
x_68 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_66, x_4);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_unbox(x_69);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_dec(x_66);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
lean_inc(x_67);
x_72 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_67, x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
if (x_74 == 0)
{
uint8_t x_75; 
lean_dec(x_67);
lean_dec(x_2);
x_75 = !lean_is_exclusive(x_72);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_72, 0);
lean_dec(x_76);
return x_72;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
lean_dec(x_72);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_73);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
else
{
lean_object* x_79; 
lean_dec(x_73);
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
lean_dec(x_72);
x_3 = x_67;
x_4 = x_79;
goto _start;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_81 = lean_ctor_get(x_68, 1);
lean_inc(x_81);
lean_dec(x_68);
lean_inc(x_2);
x_82 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__21(x_1, x_2, x_66, x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_unbox(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
lean_dec(x_83);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
lean_inc(x_67);
x_86 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_67, x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_unbox(x_87);
if (x_88 == 0)
{
uint8_t x_89; 
lean_dec(x_67);
lean_dec(x_2);
x_89 = !lean_is_exclusive(x_86);
if (x_89 == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_86, 0);
lean_dec(x_90);
return x_86;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_86, 1);
lean_inc(x_91);
lean_dec(x_86);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_87);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
else
{
lean_object* x_93; 
lean_dec(x_87);
x_93 = lean_ctor_get(x_86, 1);
lean_inc(x_93);
lean_dec(x_86);
x_3 = x_67;
x_4 = x_93;
goto _start;
}
}
else
{
uint8_t x_95; 
lean_dec(x_67);
lean_dec(x_2);
x_95 = !lean_is_exclusive(x_82);
if (x_95 == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_82, 0);
lean_dec(x_96);
return x_82;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_82, 1);
lean_inc(x_97);
lean_dec(x_82);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_83);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
case 7:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_99 = lean_ctor_get(x_3, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_3, 2);
lean_inc(x_100);
lean_dec(x_3);
lean_inc(x_99);
x_101 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_99, x_4);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_unbox(x_102);
lean_dec(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
lean_dec(x_99);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
lean_dec(x_101);
lean_inc(x_100);
x_105 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_100, x_104);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_unbox(x_106);
if (x_107 == 0)
{
uint8_t x_108; 
lean_dec(x_100);
lean_dec(x_2);
x_108 = !lean_is_exclusive(x_105);
if (x_108 == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_105, 0);
lean_dec(x_109);
return x_105;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_105, 1);
lean_inc(x_110);
lean_dec(x_105);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_106);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
else
{
lean_object* x_112; 
lean_dec(x_106);
x_112 = lean_ctor_get(x_105, 1);
lean_inc(x_112);
lean_dec(x_105);
x_3 = x_100;
x_4 = x_112;
goto _start;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_114 = lean_ctor_get(x_101, 1);
lean_inc(x_114);
lean_dec(x_101);
lean_inc(x_2);
x_115 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__21(x_1, x_2, x_99, x_114);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_unbox(x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
lean_dec(x_116);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec(x_115);
lean_inc(x_100);
x_119 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_100, x_118);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_unbox(x_120);
if (x_121 == 0)
{
uint8_t x_122; 
lean_dec(x_100);
lean_dec(x_2);
x_122 = !lean_is_exclusive(x_119);
if (x_122 == 0)
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_119, 0);
lean_dec(x_123);
return x_119;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_119, 1);
lean_inc(x_124);
lean_dec(x_119);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_120);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
else
{
lean_object* x_126; 
lean_dec(x_120);
x_126 = lean_ctor_get(x_119, 1);
lean_inc(x_126);
lean_dec(x_119);
x_3 = x_100;
x_4 = x_126;
goto _start;
}
}
else
{
uint8_t x_128; 
lean_dec(x_100);
lean_dec(x_2);
x_128 = !lean_is_exclusive(x_115);
if (x_128 == 0)
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_115, 0);
lean_dec(x_129);
return x_115;
}
else
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_115, 1);
lean_inc(x_130);
lean_dec(x_115);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_116);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
}
case 8:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_132 = lean_ctor_get(x_3, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_3, 2);
lean_inc(x_133);
x_134 = lean_ctor_get(x_3, 3);
lean_inc(x_134);
lean_dec(x_3);
lean_inc(x_132);
x_171 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_132, x_4);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_unbox(x_172);
if (x_173 == 0)
{
lean_object* x_174; uint8_t x_175; 
lean_dec(x_132);
x_174 = lean_ctor_get(x_171, 1);
lean_inc(x_174);
lean_dec(x_171);
x_175 = lean_unbox(x_172);
lean_dec(x_172);
x_135 = x_175;
x_136 = x_174;
goto block_170;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
lean_dec(x_172);
x_176 = lean_ctor_get(x_171, 1);
lean_inc(x_176);
lean_dec(x_171);
lean_inc(x_2);
x_177 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__21(x_1, x_2, x_132, x_176);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = lean_unbox(x_178);
lean_dec(x_178);
x_135 = x_180;
x_136 = x_179;
goto block_170;
}
block_170:
{
if (x_135 == 0)
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; 
lean_inc(x_133);
x_137 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_133, x_136);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_unbox(x_138);
lean_dec(x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
lean_dec(x_133);
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
lean_dec(x_137);
lean_inc(x_134);
x_141 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_134, x_140);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_unbox(x_142);
if (x_143 == 0)
{
uint8_t x_144; 
lean_dec(x_134);
lean_dec(x_2);
x_144 = !lean_is_exclusive(x_141);
if (x_144 == 0)
{
lean_object* x_145; 
x_145 = lean_ctor_get(x_141, 0);
lean_dec(x_145);
return x_141;
}
else
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_141, 1);
lean_inc(x_146);
lean_dec(x_141);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_142);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
else
{
lean_object* x_148; 
lean_dec(x_142);
x_148 = lean_ctor_get(x_141, 1);
lean_inc(x_148);
lean_dec(x_141);
x_3 = x_134;
x_4 = x_148;
goto _start;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_150 = lean_ctor_get(x_137, 1);
lean_inc(x_150);
lean_dec(x_137);
lean_inc(x_2);
x_151 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__21(x_1, x_2, x_133, x_150);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_unbox(x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
lean_dec(x_152);
x_154 = lean_ctor_get(x_151, 1);
lean_inc(x_154);
lean_dec(x_151);
lean_inc(x_134);
x_155 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_134, x_154);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_unbox(x_156);
if (x_157 == 0)
{
uint8_t x_158; 
lean_dec(x_134);
lean_dec(x_2);
x_158 = !lean_is_exclusive(x_155);
if (x_158 == 0)
{
lean_object* x_159; 
x_159 = lean_ctor_get(x_155, 0);
lean_dec(x_159);
return x_155;
}
else
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_155, 1);
lean_inc(x_160);
lean_dec(x_155);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_156);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
else
{
lean_object* x_162; 
lean_dec(x_156);
x_162 = lean_ctor_get(x_155, 1);
lean_inc(x_162);
lean_dec(x_155);
x_3 = x_134;
x_4 = x_162;
goto _start;
}
}
else
{
uint8_t x_164; 
lean_dec(x_134);
lean_dec(x_2);
x_164 = !lean_is_exclusive(x_151);
if (x_164 == 0)
{
lean_object* x_165; 
x_165 = lean_ctor_get(x_151, 0);
lean_dec(x_165);
return x_151;
}
else
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_151, 1);
lean_inc(x_166);
lean_dec(x_151);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_152);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
}
else
{
lean_object* x_168; lean_object* x_169; 
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_2);
x_168 = lean_box(x_135);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_136);
return x_169;
}
}
}
case 10:
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_181 = lean_ctor_get(x_3, 1);
lean_inc(x_181);
lean_dec(x_3);
lean_inc(x_181);
x_182 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_181, x_4);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_unbox(x_183);
if (x_184 == 0)
{
uint8_t x_185; 
lean_dec(x_181);
lean_dec(x_2);
x_185 = !lean_is_exclusive(x_182);
if (x_185 == 0)
{
lean_object* x_186; 
x_186 = lean_ctor_get(x_182, 0);
lean_dec(x_186);
return x_182;
}
else
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_ctor_get(x_182, 1);
lean_inc(x_187);
lean_dec(x_182);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_183);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
else
{
lean_object* x_189; 
lean_dec(x_183);
x_189 = lean_ctor_get(x_182, 1);
lean_inc(x_189);
lean_dec(x_182);
x_3 = x_181;
x_4 = x_189;
goto _start;
}
}
case 11:
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_191 = lean_ctor_get(x_3, 2);
lean_inc(x_191);
lean_dec(x_3);
lean_inc(x_191);
x_192 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_191, x_4);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_unbox(x_193);
if (x_194 == 0)
{
uint8_t x_195; 
lean_dec(x_191);
lean_dec(x_2);
x_195 = !lean_is_exclusive(x_192);
if (x_195 == 0)
{
lean_object* x_196; 
x_196 = lean_ctor_get(x_192, 0);
lean_dec(x_196);
return x_192;
}
else
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_192, 1);
lean_inc(x_197);
lean_dec(x_192);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_193);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
else
{
lean_object* x_199; 
lean_dec(x_193);
x_199 = lean_ctor_get(x_192, 1);
lean_inc(x_199);
lean_dec(x_192);
x_3 = x_191;
x_4 = x_199;
goto _start;
}
}
default: 
{
uint8_t x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_3);
lean_dec(x_2);
x_201 = 0;
x_202 = lean_box(x_201);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_4);
return x_203;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__30(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__29(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_5, x_10);
lean_dec(x_5);
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_5);
return x_9;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__31(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_array_fget(x_3, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_5, x_9);
lean_dec(x_5);
x_5 = x_10;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = l_Lean_LocalDecl_fvarId(x_12);
lean_dec(x_12);
x_14 = lean_array_get_size(x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__2(x_1, x_13, x_1, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_5, x_17);
lean_dec(x_5);
x_5 = x_18;
goto _start;
}
else
{
lean_dec(x_5);
return x_16;
}
}
}
}
}
uint8_t l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__29(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__30(x_1, x_3, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__31(x_1, x_7, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__32(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_array_fget(x_3, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_5, x_9);
lean_dec(x_5);
x_5 = x_10;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = l_Lean_LocalDecl_fvarId(x_12);
lean_dec(x_12);
x_14 = lean_array_get_size(x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__2(x_1, x_13, x_1, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_5, x_17);
lean_dec(x_5);
x_5 = x_18;
goto _start;
}
else
{
lean_dec(x_5);
return x_16;
}
}
}
}
}
uint8_t l_PersistentArray_anyM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__28(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__29(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__32(x_1, x_2, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
else
{
return x_4;
}
}
}
lean_object* l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_array_get_size(x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__2(x_1, x_5, x_1, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
lean_inc(x_11);
lean_inc(x_2);
x_12 = lean_metavar_ctx_get_expr_assignment(x_2, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_13 = l_Lean_MetavarContext_getDecl(x_2, x_11);
lean_dec(x_11);
lean_dec(x_2);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_PersistentArray_anyM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__28(x_1, x_15);
lean_dec(x_15);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_11);
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
lean_inc(x_19);
x_20 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_19, x_4);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
if (x_22 == 0)
{
uint8_t x_23; 
lean_dec(x_19);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_20, 0);
lean_dec(x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; 
lean_dec(x_21);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_dec(x_20);
x_3 = x_19;
x_4 = x_27;
goto _start;
}
}
}
case 5:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_3, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_3, 1);
lean_inc(x_30);
lean_dec(x_3);
lean_inc(x_30);
x_31 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_30, x_4);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
lean_dec(x_30);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = l_Lean_Expr_isApp(x_29);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_inc(x_29);
x_36 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_29, x_34);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
if (x_38 == 0)
{
uint8_t x_39; 
lean_dec(x_29);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_36, 0);
lean_dec(x_40);
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_dec(x_36);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_object* x_43; 
lean_dec(x_37);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
lean_dec(x_36);
x_3 = x_29;
x_4 = x_43;
goto _start;
}
}
else
{
x_3 = x_29;
x_4 = x_34;
goto _start;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_31, 1);
lean_inc(x_46);
lean_dec(x_31);
lean_inc(x_2);
x_47 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__27(x_1, x_2, x_30, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_unbox(x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
lean_dec(x_48);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = l_Lean_Expr_isApp(x_29);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_inc(x_29);
x_52 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_29, x_50);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
if (x_54 == 0)
{
uint8_t x_55; 
lean_dec(x_29);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_52);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_52, 0);
lean_dec(x_56);
return x_52;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_52, 1);
lean_inc(x_57);
lean_dec(x_52);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
else
{
lean_object* x_59; 
lean_dec(x_53);
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_dec(x_52);
x_3 = x_29;
x_4 = x_59;
goto _start;
}
}
else
{
x_3 = x_29;
x_4 = x_50;
goto _start;
}
}
else
{
uint8_t x_62; 
lean_dec(x_29);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_47);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_47, 0);
lean_dec(x_63);
return x_47;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_47, 1);
lean_inc(x_64);
lean_dec(x_47);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_48);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
case 6:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_66 = lean_ctor_get(x_3, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_3, 2);
lean_inc(x_67);
lean_dec(x_3);
lean_inc(x_66);
x_68 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_66, x_4);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_unbox(x_69);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_dec(x_66);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
lean_inc(x_67);
x_72 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_67, x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
if (x_74 == 0)
{
uint8_t x_75; 
lean_dec(x_67);
lean_dec(x_2);
x_75 = !lean_is_exclusive(x_72);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_72, 0);
lean_dec(x_76);
return x_72;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
lean_dec(x_72);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_73);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
else
{
lean_object* x_79; 
lean_dec(x_73);
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
lean_dec(x_72);
x_3 = x_67;
x_4 = x_79;
goto _start;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_81 = lean_ctor_get(x_68, 1);
lean_inc(x_81);
lean_dec(x_68);
lean_inc(x_2);
x_82 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__27(x_1, x_2, x_66, x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_unbox(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
lean_dec(x_83);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
lean_inc(x_67);
x_86 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_67, x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_unbox(x_87);
if (x_88 == 0)
{
uint8_t x_89; 
lean_dec(x_67);
lean_dec(x_2);
x_89 = !lean_is_exclusive(x_86);
if (x_89 == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_86, 0);
lean_dec(x_90);
return x_86;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_86, 1);
lean_inc(x_91);
lean_dec(x_86);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_87);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
else
{
lean_object* x_93; 
lean_dec(x_87);
x_93 = lean_ctor_get(x_86, 1);
lean_inc(x_93);
lean_dec(x_86);
x_3 = x_67;
x_4 = x_93;
goto _start;
}
}
else
{
uint8_t x_95; 
lean_dec(x_67);
lean_dec(x_2);
x_95 = !lean_is_exclusive(x_82);
if (x_95 == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_82, 0);
lean_dec(x_96);
return x_82;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_82, 1);
lean_inc(x_97);
lean_dec(x_82);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_83);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
case 7:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_99 = lean_ctor_get(x_3, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_3, 2);
lean_inc(x_100);
lean_dec(x_3);
lean_inc(x_99);
x_101 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_99, x_4);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_unbox(x_102);
lean_dec(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
lean_dec(x_99);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
lean_dec(x_101);
lean_inc(x_100);
x_105 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_100, x_104);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_unbox(x_106);
if (x_107 == 0)
{
uint8_t x_108; 
lean_dec(x_100);
lean_dec(x_2);
x_108 = !lean_is_exclusive(x_105);
if (x_108 == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_105, 0);
lean_dec(x_109);
return x_105;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_105, 1);
lean_inc(x_110);
lean_dec(x_105);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_106);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
else
{
lean_object* x_112; 
lean_dec(x_106);
x_112 = lean_ctor_get(x_105, 1);
lean_inc(x_112);
lean_dec(x_105);
x_3 = x_100;
x_4 = x_112;
goto _start;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_114 = lean_ctor_get(x_101, 1);
lean_inc(x_114);
lean_dec(x_101);
lean_inc(x_2);
x_115 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__27(x_1, x_2, x_99, x_114);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_unbox(x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
lean_dec(x_116);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec(x_115);
lean_inc(x_100);
x_119 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_100, x_118);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_unbox(x_120);
if (x_121 == 0)
{
uint8_t x_122; 
lean_dec(x_100);
lean_dec(x_2);
x_122 = !lean_is_exclusive(x_119);
if (x_122 == 0)
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_119, 0);
lean_dec(x_123);
return x_119;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_119, 1);
lean_inc(x_124);
lean_dec(x_119);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_120);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
else
{
lean_object* x_126; 
lean_dec(x_120);
x_126 = lean_ctor_get(x_119, 1);
lean_inc(x_126);
lean_dec(x_119);
x_3 = x_100;
x_4 = x_126;
goto _start;
}
}
else
{
uint8_t x_128; 
lean_dec(x_100);
lean_dec(x_2);
x_128 = !lean_is_exclusive(x_115);
if (x_128 == 0)
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_115, 0);
lean_dec(x_129);
return x_115;
}
else
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_115, 1);
lean_inc(x_130);
lean_dec(x_115);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_116);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
}
case 8:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_132 = lean_ctor_get(x_3, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_3, 2);
lean_inc(x_133);
x_134 = lean_ctor_get(x_3, 3);
lean_inc(x_134);
lean_dec(x_3);
lean_inc(x_132);
x_171 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_132, x_4);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_unbox(x_172);
if (x_173 == 0)
{
lean_object* x_174; uint8_t x_175; 
lean_dec(x_132);
x_174 = lean_ctor_get(x_171, 1);
lean_inc(x_174);
lean_dec(x_171);
x_175 = lean_unbox(x_172);
lean_dec(x_172);
x_135 = x_175;
x_136 = x_174;
goto block_170;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
lean_dec(x_172);
x_176 = lean_ctor_get(x_171, 1);
lean_inc(x_176);
lean_dec(x_171);
lean_inc(x_2);
x_177 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__27(x_1, x_2, x_132, x_176);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = lean_unbox(x_178);
lean_dec(x_178);
x_135 = x_180;
x_136 = x_179;
goto block_170;
}
block_170:
{
if (x_135 == 0)
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; 
lean_inc(x_133);
x_137 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_133, x_136);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_unbox(x_138);
lean_dec(x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
lean_dec(x_133);
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
lean_dec(x_137);
lean_inc(x_134);
x_141 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_134, x_140);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_unbox(x_142);
if (x_143 == 0)
{
uint8_t x_144; 
lean_dec(x_134);
lean_dec(x_2);
x_144 = !lean_is_exclusive(x_141);
if (x_144 == 0)
{
lean_object* x_145; 
x_145 = lean_ctor_get(x_141, 0);
lean_dec(x_145);
return x_141;
}
else
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_141, 1);
lean_inc(x_146);
lean_dec(x_141);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_142);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
else
{
lean_object* x_148; 
lean_dec(x_142);
x_148 = lean_ctor_get(x_141, 1);
lean_inc(x_148);
lean_dec(x_141);
x_3 = x_134;
x_4 = x_148;
goto _start;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_150 = lean_ctor_get(x_137, 1);
lean_inc(x_150);
lean_dec(x_137);
lean_inc(x_2);
x_151 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__27(x_1, x_2, x_133, x_150);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_unbox(x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
lean_dec(x_152);
x_154 = lean_ctor_get(x_151, 1);
lean_inc(x_154);
lean_dec(x_151);
lean_inc(x_134);
x_155 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_134, x_154);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_unbox(x_156);
if (x_157 == 0)
{
uint8_t x_158; 
lean_dec(x_134);
lean_dec(x_2);
x_158 = !lean_is_exclusive(x_155);
if (x_158 == 0)
{
lean_object* x_159; 
x_159 = lean_ctor_get(x_155, 0);
lean_dec(x_159);
return x_155;
}
else
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_155, 1);
lean_inc(x_160);
lean_dec(x_155);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_156);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
else
{
lean_object* x_162; 
lean_dec(x_156);
x_162 = lean_ctor_get(x_155, 1);
lean_inc(x_162);
lean_dec(x_155);
x_3 = x_134;
x_4 = x_162;
goto _start;
}
}
else
{
uint8_t x_164; 
lean_dec(x_134);
lean_dec(x_2);
x_164 = !lean_is_exclusive(x_151);
if (x_164 == 0)
{
lean_object* x_165; 
x_165 = lean_ctor_get(x_151, 0);
lean_dec(x_165);
return x_151;
}
else
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_151, 1);
lean_inc(x_166);
lean_dec(x_151);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_152);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
}
else
{
lean_object* x_168; lean_object* x_169; 
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_2);
x_168 = lean_box(x_135);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_136);
return x_169;
}
}
}
case 10:
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_181 = lean_ctor_get(x_3, 1);
lean_inc(x_181);
lean_dec(x_3);
lean_inc(x_181);
x_182 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_181, x_4);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_unbox(x_183);
if (x_184 == 0)
{
uint8_t x_185; 
lean_dec(x_181);
lean_dec(x_2);
x_185 = !lean_is_exclusive(x_182);
if (x_185 == 0)
{
lean_object* x_186; 
x_186 = lean_ctor_get(x_182, 0);
lean_dec(x_186);
return x_182;
}
else
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_ctor_get(x_182, 1);
lean_inc(x_187);
lean_dec(x_182);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_183);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
else
{
lean_object* x_189; 
lean_dec(x_183);
x_189 = lean_ctor_get(x_182, 1);
lean_inc(x_189);
lean_dec(x_182);
x_3 = x_181;
x_4 = x_189;
goto _start;
}
}
case 11:
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_191 = lean_ctor_get(x_3, 2);
lean_inc(x_191);
lean_dec(x_3);
lean_inc(x_191);
x_192 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_191, x_4);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_unbox(x_193);
if (x_194 == 0)
{
uint8_t x_195; 
lean_dec(x_191);
lean_dec(x_2);
x_195 = !lean_is_exclusive(x_192);
if (x_195 == 0)
{
lean_object* x_196; 
x_196 = lean_ctor_get(x_192, 0);
lean_dec(x_196);
return x_192;
}
else
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_192, 1);
lean_inc(x_197);
lean_dec(x_192);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_193);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
else
{
lean_object* x_199; 
lean_dec(x_193);
x_199 = lean_ctor_get(x_192, 1);
lean_inc(x_199);
lean_dec(x_192);
x_3 = x_191;
x_4 = x_199;
goto _start;
}
}
default: 
{
uint8_t x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_3);
lean_dec(x_2);
x_201 = 0;
x_202 = lean_box(x_201);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_4);
return x_203;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__36(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__35(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_5, x_10);
lean_dec(x_5);
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_5);
return x_9;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__37(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_array_fget(x_3, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_5, x_9);
lean_dec(x_5);
x_5 = x_10;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = l_Lean_LocalDecl_fvarId(x_12);
lean_dec(x_12);
x_14 = lean_array_get_size(x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__2(x_1, x_13, x_1, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_5, x_17);
lean_dec(x_5);
x_5 = x_18;
goto _start;
}
else
{
lean_dec(x_5);
return x_16;
}
}
}
}
}
uint8_t l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__35(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__36(x_1, x_3, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__37(x_1, x_7, x_7, x_8, x_9);
lean_dec(x_8);
return x_10;
}
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__38(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_array_fget(x_3, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_5, x_9);
lean_dec(x_5);
x_5 = x_10;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = l_Lean_LocalDecl_fvarId(x_12);
lean_dec(x_12);
x_14 = lean_array_get_size(x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__2(x_1, x_13, x_1, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_5, x_17);
lean_dec(x_5);
x_5 = x_18;
goto _start;
}
else
{
lean_dec(x_5);
return x_16;
}
}
}
}
}
uint8_t l_PersistentArray_anyM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__34(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__35(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__38(x_1, x_2, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
else
{
return x_4;
}
}
}
lean_object* l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__33(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_array_get_size(x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__2(x_1, x_5, x_1, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
lean_inc(x_11);
lean_inc(x_2);
x_12 = lean_metavar_ctx_get_expr_assignment(x_2, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_13 = l_Lean_MetavarContext_getDecl(x_2, x_11);
lean_dec(x_11);
lean_dec(x_2);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_PersistentArray_anyM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__34(x_1, x_15);
lean_dec(x_15);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_11);
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
lean_inc(x_19);
x_20 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_19, x_4);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
if (x_22 == 0)
{
uint8_t x_23; 
lean_dec(x_19);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_20, 0);
lean_dec(x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_27; 
lean_dec(x_21);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_dec(x_20);
x_3 = x_19;
x_4 = x_27;
goto _start;
}
}
}
case 5:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_3, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_3, 1);
lean_inc(x_30);
lean_dec(x_3);
lean_inc(x_30);
x_31 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_30, x_4);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
lean_dec(x_30);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = l_Lean_Expr_isApp(x_29);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_inc(x_29);
x_36 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_29, x_34);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
if (x_38 == 0)
{
uint8_t x_39; 
lean_dec(x_29);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_36, 0);
lean_dec(x_40);
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_dec(x_36);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_object* x_43; 
lean_dec(x_37);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
lean_dec(x_36);
x_3 = x_29;
x_4 = x_43;
goto _start;
}
}
else
{
x_3 = x_29;
x_4 = x_34;
goto _start;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_31, 1);
lean_inc(x_46);
lean_dec(x_31);
lean_inc(x_2);
x_47 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__33(x_1, x_2, x_30, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_unbox(x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
lean_dec(x_48);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = l_Lean_Expr_isApp(x_29);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_inc(x_29);
x_52 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_29, x_50);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
if (x_54 == 0)
{
uint8_t x_55; 
lean_dec(x_29);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_52);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_52, 0);
lean_dec(x_56);
return x_52;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_52, 1);
lean_inc(x_57);
lean_dec(x_52);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
else
{
lean_object* x_59; 
lean_dec(x_53);
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_dec(x_52);
x_3 = x_29;
x_4 = x_59;
goto _start;
}
}
else
{
x_3 = x_29;
x_4 = x_50;
goto _start;
}
}
else
{
uint8_t x_62; 
lean_dec(x_29);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_47);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_47, 0);
lean_dec(x_63);
return x_47;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_47, 1);
lean_inc(x_64);
lean_dec(x_47);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_48);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
case 6:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_66 = lean_ctor_get(x_3, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_3, 2);
lean_inc(x_67);
lean_dec(x_3);
lean_inc(x_66);
x_68 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_66, x_4);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_unbox(x_69);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_dec(x_66);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
lean_inc(x_67);
x_72 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_67, x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
if (x_74 == 0)
{
uint8_t x_75; 
lean_dec(x_67);
lean_dec(x_2);
x_75 = !lean_is_exclusive(x_72);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_72, 0);
lean_dec(x_76);
return x_72;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
lean_dec(x_72);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_73);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
else
{
lean_object* x_79; 
lean_dec(x_73);
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
lean_dec(x_72);
x_3 = x_67;
x_4 = x_79;
goto _start;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_81 = lean_ctor_get(x_68, 1);
lean_inc(x_81);
lean_dec(x_68);
lean_inc(x_2);
x_82 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__33(x_1, x_2, x_66, x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_unbox(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
lean_dec(x_83);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
lean_inc(x_67);
x_86 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_67, x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_unbox(x_87);
if (x_88 == 0)
{
uint8_t x_89; 
lean_dec(x_67);
lean_dec(x_2);
x_89 = !lean_is_exclusive(x_86);
if (x_89 == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_86, 0);
lean_dec(x_90);
return x_86;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_86, 1);
lean_inc(x_91);
lean_dec(x_86);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_87);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
else
{
lean_object* x_93; 
lean_dec(x_87);
x_93 = lean_ctor_get(x_86, 1);
lean_inc(x_93);
lean_dec(x_86);
x_3 = x_67;
x_4 = x_93;
goto _start;
}
}
else
{
uint8_t x_95; 
lean_dec(x_67);
lean_dec(x_2);
x_95 = !lean_is_exclusive(x_82);
if (x_95 == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_82, 0);
lean_dec(x_96);
return x_82;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_82, 1);
lean_inc(x_97);
lean_dec(x_82);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_83);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
case 7:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_99 = lean_ctor_get(x_3, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_3, 2);
lean_inc(x_100);
lean_dec(x_3);
lean_inc(x_99);
x_101 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_99, x_4);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_unbox(x_102);
lean_dec(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
lean_dec(x_99);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
lean_dec(x_101);
lean_inc(x_100);
x_105 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_100, x_104);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_unbox(x_106);
if (x_107 == 0)
{
uint8_t x_108; 
lean_dec(x_100);
lean_dec(x_2);
x_108 = !lean_is_exclusive(x_105);
if (x_108 == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_105, 0);
lean_dec(x_109);
return x_105;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_105, 1);
lean_inc(x_110);
lean_dec(x_105);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_106);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
else
{
lean_object* x_112; 
lean_dec(x_106);
x_112 = lean_ctor_get(x_105, 1);
lean_inc(x_112);
lean_dec(x_105);
x_3 = x_100;
x_4 = x_112;
goto _start;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_114 = lean_ctor_get(x_101, 1);
lean_inc(x_114);
lean_dec(x_101);
lean_inc(x_2);
x_115 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__33(x_1, x_2, x_99, x_114);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_unbox(x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
lean_dec(x_116);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec(x_115);
lean_inc(x_100);
x_119 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_100, x_118);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_unbox(x_120);
if (x_121 == 0)
{
uint8_t x_122; 
lean_dec(x_100);
lean_dec(x_2);
x_122 = !lean_is_exclusive(x_119);
if (x_122 == 0)
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_119, 0);
lean_dec(x_123);
return x_119;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_119, 1);
lean_inc(x_124);
lean_dec(x_119);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_120);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
else
{
lean_object* x_126; 
lean_dec(x_120);
x_126 = lean_ctor_get(x_119, 1);
lean_inc(x_126);
lean_dec(x_119);
x_3 = x_100;
x_4 = x_126;
goto _start;
}
}
else
{
uint8_t x_128; 
lean_dec(x_100);
lean_dec(x_2);
x_128 = !lean_is_exclusive(x_115);
if (x_128 == 0)
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_115, 0);
lean_dec(x_129);
return x_115;
}
else
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_115, 1);
lean_inc(x_130);
lean_dec(x_115);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_116);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
}
case 8:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_132 = lean_ctor_get(x_3, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_3, 2);
lean_inc(x_133);
x_134 = lean_ctor_get(x_3, 3);
lean_inc(x_134);
lean_dec(x_3);
lean_inc(x_132);
x_171 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_132, x_4);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_unbox(x_172);
if (x_173 == 0)
{
lean_object* x_174; uint8_t x_175; 
lean_dec(x_132);
x_174 = lean_ctor_get(x_171, 1);
lean_inc(x_174);
lean_dec(x_171);
x_175 = lean_unbox(x_172);
lean_dec(x_172);
x_135 = x_175;
x_136 = x_174;
goto block_170;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
lean_dec(x_172);
x_176 = lean_ctor_get(x_171, 1);
lean_inc(x_176);
lean_dec(x_171);
lean_inc(x_2);
x_177 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__33(x_1, x_2, x_132, x_176);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = lean_unbox(x_178);
lean_dec(x_178);
x_135 = x_180;
x_136 = x_179;
goto block_170;
}
block_170:
{
if (x_135 == 0)
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; 
lean_inc(x_133);
x_137 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_133, x_136);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_unbox(x_138);
lean_dec(x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
lean_dec(x_133);
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
lean_dec(x_137);
lean_inc(x_134);
x_141 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_134, x_140);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_unbox(x_142);
if (x_143 == 0)
{
uint8_t x_144; 
lean_dec(x_134);
lean_dec(x_2);
x_144 = !lean_is_exclusive(x_141);
if (x_144 == 0)
{
lean_object* x_145; 
x_145 = lean_ctor_get(x_141, 0);
lean_dec(x_145);
return x_141;
}
else
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_141, 1);
lean_inc(x_146);
lean_dec(x_141);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_142);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
else
{
lean_object* x_148; 
lean_dec(x_142);
x_148 = lean_ctor_get(x_141, 1);
lean_inc(x_148);
lean_dec(x_141);
x_3 = x_134;
x_4 = x_148;
goto _start;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_150 = lean_ctor_get(x_137, 1);
lean_inc(x_150);
lean_dec(x_137);
lean_inc(x_2);
x_151 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__33(x_1, x_2, x_133, x_150);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_unbox(x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
lean_dec(x_152);
x_154 = lean_ctor_get(x_151, 1);
lean_inc(x_154);
lean_dec(x_151);
lean_inc(x_134);
x_155 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_134, x_154);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_unbox(x_156);
if (x_157 == 0)
{
uint8_t x_158; 
lean_dec(x_134);
lean_dec(x_2);
x_158 = !lean_is_exclusive(x_155);
if (x_158 == 0)
{
lean_object* x_159; 
x_159 = lean_ctor_get(x_155, 0);
lean_dec(x_159);
return x_155;
}
else
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_155, 1);
lean_inc(x_160);
lean_dec(x_155);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_156);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
else
{
lean_object* x_162; 
lean_dec(x_156);
x_162 = lean_ctor_get(x_155, 1);
lean_inc(x_162);
lean_dec(x_155);
x_3 = x_134;
x_4 = x_162;
goto _start;
}
}
else
{
uint8_t x_164; 
lean_dec(x_134);
lean_dec(x_2);
x_164 = !lean_is_exclusive(x_151);
if (x_164 == 0)
{
lean_object* x_165; 
x_165 = lean_ctor_get(x_151, 0);
lean_dec(x_165);
return x_151;
}
else
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_151, 1);
lean_inc(x_166);
lean_dec(x_151);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_152);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
}
else
{
lean_object* x_168; lean_object* x_169; 
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_2);
x_168 = lean_box(x_135);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_136);
return x_169;
}
}
}
case 10:
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_181 = lean_ctor_get(x_3, 1);
lean_inc(x_181);
lean_dec(x_3);
lean_inc(x_181);
x_182 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_181, x_4);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_unbox(x_183);
if (x_184 == 0)
{
uint8_t x_185; 
lean_dec(x_181);
lean_dec(x_2);
x_185 = !lean_is_exclusive(x_182);
if (x_185 == 0)
{
lean_object* x_186; 
x_186 = lean_ctor_get(x_182, 0);
lean_dec(x_186);
return x_182;
}
else
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_ctor_get(x_182, 1);
lean_inc(x_187);
lean_dec(x_182);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_183);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
else
{
lean_object* x_189; 
lean_dec(x_183);
x_189 = lean_ctor_get(x_182, 1);
lean_inc(x_189);
lean_dec(x_182);
x_3 = x_181;
x_4 = x_189;
goto _start;
}
}
case 11:
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_191 = lean_ctor_get(x_3, 2);
lean_inc(x_191);
lean_dec(x_3);
lean_inc(x_191);
x_192 = l___private_Init_Lean_MetavarContext_8__visit_x3f(x_191, x_4);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_unbox(x_193);
if (x_194 == 0)
{
uint8_t x_195; 
lean_dec(x_191);
lean_dec(x_2);
x_195 = !lean_is_exclusive(x_192);
if (x_195 == 0)
{
lean_object* x_196; 
x_196 = lean_ctor_get(x_192, 0);
lean_dec(x_196);
return x_192;
}
else
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_192, 1);
lean_inc(x_197);
lean_dec(x_192);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_193);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
else
{
lean_object* x_199; 
lean_dec(x_193);
x_199 = lean_ctor_get(x_192, 1);
lean_inc(x_199);
lean_dec(x_192);
x_3 = x_191;
x_4 = x_199;
goto _start;
}
}
default: 
{
uint8_t x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_3);
lean_dec(x_2);
x_201 = 0;
x_202 = lean_box(x_201);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_4);
return x_203;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__43___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_10 = l_PersistentArray_foldlMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__42___rarg(x_1, x_9, x_5);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_4);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_4, x_15);
lean_dec(x_4);
x_4 = x_16;
x_5 = x_14;
goto _start;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__43(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__43___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__44___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_10 = lean_apply_2(x_1, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_4);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_4, x_15);
lean_dec(x_4);
x_4 = x_16;
x_5 = x_14;
goto _start;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__44(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__44___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_PersistentArray_foldlMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__42___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__43___rarg(x_1, x_4, x_4, x_5, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__44___rarg(x_1, x_7, x_7, x_8, x_3);
return x_9;
}
}
}
lean_object* l_PersistentArray_foldlMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__42(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentArray_foldlMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__42___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__45___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_10 = l_PersistentArray_foldlMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__42___rarg(x_1, x_9, x_5);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_4);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_4, x_15);
lean_dec(x_4);
x_4 = x_16;
x_5 = x_14;
goto _start;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__45(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__45___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__46___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_10 = lean_apply_2(x_1, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_4);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_4, x_15);
lean_dec(x_4);
x_4 = x_16;
x_5 = x_14;
goto _start;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__46(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__46___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_PersistentArray_foldlFromMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__41___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = x_3 >> x_4;
x_8 = lean_usize_to_nat(x_7);
x_9 = l_PersistentArray_getAux___main___rarg___closed__1;
x_10 = lean_array_get(x_9, x_6, x_8);
x_11 = 1;
x_12 = x_11 << x_4;
x_13 = x_12 - x_11;
x_14 = x_3 & x_13;
x_15 = 5;
x_16 = x_4 - x_15;
lean_inc(x_1);
x_17 = l_PersistentArray_foldlFromMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__41___rarg(x_1, x_10, x_14, x_16, x_5);
lean_dec(x_10);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_8);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_8, x_22);
lean_dec(x_8);
x_24 = l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__45___rarg(x_1, x_6, x_6, x_23, x_21);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_usize_to_nat(x_3);
x_27 = l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__46___rarg(x_1, x_25, x_25, x_26, x_5);
return x_27;
}
}
}
lean_object* l_PersistentArray_foldlFromMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__41(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentArray_foldlFromMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__41___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__47___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_fget(x_3, x_4);
lean_inc(x_2);
x_10 = lean_apply_2(x_2, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_4);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_4, x_15);
lean_dec(x_4);
x_4 = x_16;
x_5 = x_14;
goto _start;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__47(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__47___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__48___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_fget(x_3, x_4);
lean_inc(x_2);
x_10 = lean_apply_2(x_2, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_4);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_4, x_15);
lean_dec(x_4);
x_4 = x_16;
x_5 = x_14;
goto _start;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__48(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__48___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_PersistentArray_foldlFromM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__40___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_nat_dec_le(x_5, x_4);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_usize_of_nat(x_4);
x_9 = lean_ctor_get_usize(x_1, 4);
lean_inc(x_2);
x_10 = l_PersistentArray_foldlFromMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__41___rarg(x_2, x_7, x_8, x_9, x_3);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__47___rarg(x_1, x_2, x_15, x_16, x_14);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_1, 1);
x_19 = lean_nat_sub(x_4, x_5);
x_20 = l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__48___rarg(x_1, x_2, x_18, x_19, x_3);
return x_20;
}
}
}
lean_object* l_PersistentArray_foldlFromM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__40(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentArray_foldlFromM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__40___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_LocalContext_foldlFromM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__39___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_18; uint8_t x_19; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__1(x_3, x_8, x_3, x_4, x_18);
if (x_19 == 0)
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_8, 3);
lean_inc(x_20);
x_21 = l_Lean_Expr_hasFVar(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Expr_hasMVar(x_20);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_5);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = l_HashMap_Inhabited___closed__1;
lean_inc(x_1);
x_25 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__3(x_5, x_1, x_20, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_5);
return x_28;
}
else
{
lean_object* x_29; 
x_29 = lean_box(0);
x_9 = x_29;
goto block_17;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = l_HashMap_Inhabited___closed__1;
lean_inc(x_1);
x_31 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__9(x_5, x_1, x_20, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_5);
return x_34;
}
else
{
lean_object* x_35; 
x_35 = lean_box(0);
x_9 = x_35;
goto block_17;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; uint8_t x_55; 
x_36 = lean_ctor_get(x_8, 3);
lean_inc(x_36);
x_37 = lean_ctor_get(x_8, 4);
lean_inc(x_37);
x_55 = l_Lean_Expr_hasFVar(x_36);
if (x_55 == 0)
{
uint8_t x_56; 
x_56 = l_Lean_Expr_hasMVar(x_36);
if (x_56 == 0)
{
uint8_t x_57; lean_object* x_58; 
lean_dec(x_36);
x_57 = 0;
x_58 = l_HashMap_Inhabited___closed__1;
x_38 = x_57;
x_39 = x_58;
goto block_54;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = l_HashMap_Inhabited___closed__1;
lean_inc(x_1);
x_60 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__27(x_5, x_1, x_36, x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_unbox(x_61);
lean_dec(x_61);
x_38 = x_63;
x_39 = x_62;
goto block_54;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_64 = l_HashMap_Inhabited___closed__1;
lean_inc(x_1);
x_65 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__33(x_5, x_1, x_36, x_64);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_unbox(x_66);
lean_dec(x_66);
x_38 = x_68;
x_39 = x_67;
goto block_54;
}
block_54:
{
if (x_38 == 0)
{
uint8_t x_40; 
x_40 = l_Lean_Expr_hasFVar(x_37);
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = l_Lean_Expr_hasMVar(x_37);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_5);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_inc(x_1);
x_43 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__15(x_5, x_1, x_37, x_39);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_unbox(x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_5);
return x_46;
}
else
{
lean_object* x_47; 
x_47 = lean_box(0);
x_9 = x_47;
goto block_17;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_inc(x_1);
x_48 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__21(x_5, x_1, x_37, x_39);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_5);
return x_51;
}
else
{
lean_object* x_52; 
x_52 = lean_box(0);
x_9 = x_52;
goto block_17;
}
}
}
else
{
lean_object* x_53; 
lean_dec(x_39);
lean_dec(x_37);
x_53 = lean_box(0);
x_9 = x_53;
goto block_17;
}
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = l_Lean_LocalDecl_toExpr(x_8);
lean_dec(x_8);
x_70 = lean_array_push(x_5, x_69);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
block_17:
{
uint8_t x_10; uint8_t x_11; 
lean_dec(x_9);
x_10 = l_Lean_LocalDecl_binderInfo(x_8);
x_11 = l_Lean_BinderInfo_isAuxDecl(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_LocalDecl_toExpr(x_8);
lean_dec(x_8);
x_13 = lean_array_push(x_5, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 2, x_3);
lean_ctor_set(x_15, 3, x_8);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
}
lean_object* l_Lean_LocalContext_foldlFromM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__39(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_alloc_closure((void*)(l_Lean_LocalContext_foldlFromM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__39___lambda__1___boxed), 6, 4);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_4);
x_10 = l_Lean_LocalDecl_index(x_7);
x_11 = l_PersistentArray_foldlFromM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__40___rarg(x_8, x_9, x_6, x_10);
lean_dec(x_10);
return x_11;
}
}
lean_object* l___private_Init_Lean_MetavarContext_13__collectDeps(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_2);
x_7 = l___private_Init_Lean_MetavarContext_12__getLocalDeclWithSmallestIdx(x_2, x_3);
x_8 = lean_mk_empty_array_with_capacity(x_4);
lean_inc(x_2);
x_9 = l_Lean_LocalContext_foldlFromM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__39(x_1, x_2, x_3, x_4, x_2, x_8, x_7);
lean_dec(x_7);
lean_dec(x_2);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_3);
return x_10;
}
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__6(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__7(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__8(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_PersistentArray_anyM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_PersistentArray_anyM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__12(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__13(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__11___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__11(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__14(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_PersistentArray_anyM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__10___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_PersistentArray_anyM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__10(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__9(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__18(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__19(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__17___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__17(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__20(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_PersistentArray_anyM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__16___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_PersistentArray_anyM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__16(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__15(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__24___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__24(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__25(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__23___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__23(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__26(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_PersistentArray_anyM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__22___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_PersistentArray_anyM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__22(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__21(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__30___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__30(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__31___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__31(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__29___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__29(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__32___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__32(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_PersistentArray_anyM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__28___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_PersistentArray_anyM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__28(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__27(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__36___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__36(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__37___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__37(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__35___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_PersistentArray_anyMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__35(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__38___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__38(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_PersistentArray_anyM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__34___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_PersistentArray_anyM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__34(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__33___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_MetavarContext_10__dep___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__33(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__43___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__43___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__44___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__44___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_PersistentArray_foldlMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__42___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_PersistentArray_foldlMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__42___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__45___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__45___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__46___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__46___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_PersistentArray_foldlFromMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__41___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_PersistentArray_foldlFromMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__41___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__47___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__47___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__48___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__48___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_PersistentArray_foldlFromM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__40___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentArray_foldlFromM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__40___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_LocalContext_foldlFromM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__39___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_LocalContext_foldlFromM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__39___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
lean_object* l_Lean_LocalContext_foldlFromM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__39___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_LocalContext_foldlFromM___at___private_Init_Lean_MetavarContext_13__collectDeps___spec__39(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_5);
return x_8;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Init_Lean_MetavarContext_14__reduceLocalContext___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_3, x_8);
lean_dec(x_3);
x_10 = lean_array_fget(x_2, x_9);
x_11 = l_Lean_Expr_fvarId_x21(x_10);
lean_dec(x_10);
x_12 = lean_local_ctx_erase(x_5, x_11);
x_3 = x_9;
x_4 = lean_box(0);
x_5 = x_12;
goto _start;
}
else
{
lean_dec(x_3);
return x_5;
}
}
}
lean_object* l___private_Init_Lean_MetavarContext_14__reduceLocalContext(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Init_Lean_MetavarContext_14__reduceLocalContext___spec__1(x_2, x_2, x_3, lean_box(0), x_1);
return x_4;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Init_Lean_MetavarContext_14__reduceLocalContext___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at___private_Init_Lean_MetavarContext_14__reduceLocalContext___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Init_Lean_MetavarContext_14__reduceLocalContext___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_MetavarContext_14__reduceLocalContext(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_MetavarContext_15__visit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_2);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_6, x_2);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_inc(x_2);
x_8 = lean_apply_2(x_1, x_2, x_3);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 1);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_10, 2);
lean_inc(x_12);
x_14 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_13, x_2, x_12);
lean_ctor_set(x_10, 2, x_14);
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
x_18 = lean_ctor_get(x_10, 2);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
lean_inc(x_15);
x_19 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_18, x_2, x_15);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set(x_8, 1, x_20);
return x_8;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_8, 1);
x_22 = lean_ctor_get(x_8, 0);
lean_inc(x_21);
lean_inc(x_22);
lean_dec(x_8);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 2);
lean_inc(x_25);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 x_26 = x_21;
} else {
 lean_dec_ref(x_21);
 x_26 = lean_box(0);
}
lean_inc(x_22);
x_27 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_25, x_2, x_22);
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(0, 3, 0);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_8);
if (x_30 == 0)
{
return x_8;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_8, 0);
x_32 = lean_ctor_get(x_8, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_8);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_ctor_get(x_7, 0);
lean_inc(x_34);
lean_dec(x_7);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_3);
return x_35;
}
}
}
}
lean_object* l___private_Init_Lean_MetavarContext_16__getMCtx(lean_object* x_1) {
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
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_17__getInScope___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = l_Lean_Expr_fvarId_x21(x_8);
x_10 = l_Lean_LocalContext_contains(x_1, x_9);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
if (x_10 == 0)
{
lean_dec(x_8);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; 
x_14 = lean_array_push(x_5, x_8);
x_4 = x_12;
x_5 = x_14;
goto _start;
}
}
}
}
lean_object* l___private_Init_Lean_MetavarContext_17__getInScope(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_empty___closed__1;
x_5 = l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_17__getInScope___spec__1(x_1, x_2, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_17__getInScope___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_17__getInScope___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Init_Lean_MetavarContext_17__getInScope___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Lean_MetavarContext_17__getInScope(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_MetavarContext_18__withFreshCache___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = l_HashMap_Inhabited___closed__1;
lean_ctor_set(x_2, 2, x_5);
x_6 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 2);
lean_dec(x_10);
lean_ctor_set(x_8, 2, x_4);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_8);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_13, 2, x_4);
lean_ctor_set(x_6, 1, x_13);
return x_6;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_6, 1);
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 x_18 = x_14;
} else {
 lean_dec_ref(x_14);
 x_18 = lean_box(0);
}
if (lean_is_scalar(x_18)) {
 x_19 = lean_alloc_ctor(0, 3, 0);
} else {
 x_19 = x_18;
}
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_4);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_6);
if (x_21 == 0)
{
return x_6;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_6, 0);
x_23 = lean_ctor_get(x_6, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_6);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get(x_2, 2);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_2);
x_28 = l_HashMap_Inhabited___closed__1;
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_apply_1(x_1, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 lean_ctor_release(x_31, 2);
 x_36 = x_31;
} else {
 lean_dec_ref(x_31);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 3, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set(x_37, 2, x_27);
if (lean_is_scalar(x_33)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_33;
}
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_27);
x_39 = lean_ctor_get(x_30, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_30, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_41 = x_30;
} else {
 lean_dec_ref(x_30);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
}
lean_object* l___private_Init_Lean_MetavarContext_18__withFreshCache(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_MetavarContext_18__withFreshCache___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Nat_foldRevMAux___main___at___private_Init_Lean_MetavarContext_19__mkForallAux___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_Expr_Inhabited;
x_10 = lean_array_get(x_9, x_1, x_2);
x_11 = l_Lean_LocalContext_findFVar(x_3, x_10);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_12 = l_monadInhabited___rarg(x_4, x_9);
x_13 = l_Lean_MetavarContext_MkBinding_mkBinding___lambda__1___closed__1;
x_14 = lean_panic_fn(x_13);
x_15 = lean_apply_1(x_14, x_8);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_4);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 3);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_16, sizeof(void*)*4);
lean_dec(x_16);
x_20 = l_Lean_Expr_hasMVar(x_18);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_7);
x_21 = lean_expr_abstract_range(x_18, x_2, x_1);
lean_dec(x_1);
lean_dec(x_18);
if (x_5 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_mkForall(x_17, x_19, x_21, x_6);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_8);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_mkLambda(x_17, x_19, x_21, x_6);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_8);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_8);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_8, 2);
x_28 = l_HashMap_Inhabited___closed__1;
lean_ctor_set(x_8, 2, x_28);
lean_inc(x_1);
x_29 = lean_apply_3(x_7, x_1, x_18, x_8);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_29, 1);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 0);
x_34 = lean_ctor_get(x_31, 2);
lean_dec(x_34);
lean_ctor_set(x_31, 2, x_27);
x_35 = lean_expr_abstract_range(x_33, x_2, x_1);
lean_dec(x_1);
lean_dec(x_33);
if (x_5 == 0)
{
lean_object* x_36; 
x_36 = l_Lean_mkForall(x_17, x_19, x_35, x_6);
lean_ctor_set(x_29, 0, x_36);
return x_29;
}
else
{
lean_object* x_37; 
x_37 = l_Lean_mkLambda(x_17, x_19, x_35, x_6);
lean_ctor_set(x_29, 0, x_37);
return x_29;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_29, 0);
x_39 = lean_ctor_get(x_31, 0);
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_31);
x_41 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_27);
x_42 = lean_expr_abstract_range(x_38, x_2, x_1);
lean_dec(x_1);
lean_dec(x_38);
if (x_5 == 0)
{
lean_object* x_43; 
x_43 = l_Lean_mkForall(x_17, x_19, x_42, x_6);
lean_ctor_set(x_29, 1, x_41);
lean_ctor_set(x_29, 0, x_43);
return x_29;
}
else
{
lean_object* x_44; 
x_44 = l_Lean_mkLambda(x_17, x_19, x_42, x_6);
lean_ctor_set(x_29, 1, x_41);
lean_ctor_set(x_29, 0, x_44);
return x_29;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_29, 1);
x_46 = lean_ctor_get(x_29, 0);
lean_inc(x_45);
lean_inc(x_46);
lean_dec(x_29);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 lean_ctor_release(x_45, 2);
 x_49 = x_45;
} else {
 lean_dec_ref(x_45);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 3, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
lean_ctor_set(x_50, 2, x_27);
x_51 = lean_expr_abstract_range(x_46, x_2, x_1);
lean_dec(x_1);
lean_dec(x_46);
if (x_5 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = l_Lean_mkForall(x_17, x_19, x_51, x_6);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = l_Lean_mkLambda(x_17, x_19, x_51, x_6);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_50);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_27);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_29);
if (x_56 == 0)
{
return x_29;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_29, 0);
x_58 = lean_ctor_get(x_29, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_29);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_8, 0);
x_61 = lean_ctor_get(x_8, 1);
x_62 = lean_ctor_get(x_8, 2);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_8);
x_63 = l_HashMap_Inhabited___closed__1;
x_64 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_64, 0, x_60);
lean_ctor_set(x_64, 1, x_61);
lean_ctor_set(x_64, 2, x_63);
lean_inc(x_1);
x_65 = lean_apply_3(x_7, x_1, x_18, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_68 = x_65;
} else {
 lean_dec_ref(x_65);
 x_68 = lean_box(0);
}
x_69 = lean_ctor_get(x_66, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_66, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 lean_ctor_release(x_66, 2);
 x_71 = x_66;
} else {
 lean_dec_ref(x_66);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(0, 3, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
lean_ctor_set(x_72, 2, x_62);
x_73 = lean_expr_abstract_range(x_67, x_2, x_1);
lean_dec(x_1);
lean_dec(x_67);
if (x_5 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = l_Lean_mkForall(x_17, x_19, x_73, x_6);
if (lean_is_scalar(x_68)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_68;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_72);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = l_Lean_mkLambda(x_17, x_19, x_73, x_6);
if (lean_is_scalar(x_68)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_68;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_72);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_62);
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_1);
x_78 = lean_ctor_get(x_65, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_65, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_80 = x_65;
} else {
 lean_dec_ref(x_65);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_148; uint8_t x_149; 
x_82 = lean_ctor_get(x_16, 2);
lean_inc(x_82);
x_83 = lean_ctor_get(x_16, 3);
lean_inc(x_83);
x_84 = lean_ctor_get(x_16, 4);
lean_inc(x_84);
lean_dec(x_16);
x_148 = lean_unsigned_to_nat(0u);
x_149 = lean_expr_has_loose_bvar(x_6, x_148);
if (x_149 == 0)
{
lean_object* x_150; 
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_7);
lean_dec(x_1);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_6);
lean_ctor_set(x_150, 1, x_8);
return x_150;
}
else
{
uint8_t x_151; 
x_151 = l_Lean_Expr_hasMVar(x_83);
if (x_151 == 0)
{
x_85 = x_83;
x_86 = x_8;
goto block_147;
}
else
{
uint8_t x_152; 
x_152 = !lean_is_exclusive(x_8);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_8, 2);
x_154 = l_HashMap_Inhabited___closed__1;
lean_ctor_set(x_8, 2, x_154);
lean_inc(x_7);
lean_inc(x_1);
x_155 = lean_apply_3(x_7, x_1, x_83, x_8);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 0);
lean_inc(x_157);
lean_dec(x_155);
x_158 = !lean_is_exclusive(x_156);
if (x_158 == 0)
{
lean_object* x_159; 
x_159 = lean_ctor_get(x_156, 2);
lean_dec(x_159);
lean_ctor_set(x_156, 2, x_153);
x_85 = x_157;
x_86 = x_156;
goto block_147;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_156, 0);
x_161 = lean_ctor_get(x_156, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_156);
x_162 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
lean_ctor_set(x_162, 2, x_153);
x_85 = x_157;
x_86 = x_162;
goto block_147;
}
}
else
{
uint8_t x_163; 
lean_dec(x_153);
lean_dec(x_84);
lean_dec(x_82);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_163 = !lean_is_exclusive(x_155);
if (x_163 == 0)
{
return x_155;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_155, 0);
x_165 = lean_ctor_get(x_155, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_155);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_167 = lean_ctor_get(x_8, 0);
x_168 = lean_ctor_get(x_8, 1);
x_169 = lean_ctor_get(x_8, 2);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_8);
x_170 = l_HashMap_Inhabited___closed__1;
x_171 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_171, 0, x_167);
lean_ctor_set(x_171, 1, x_168);
lean_ctor_set(x_171, 2, x_170);
lean_inc(x_7);
lean_inc(x_1);
x_172 = lean_apply_3(x_7, x_1, x_83, x_171);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_173 = lean_ctor_get(x_172, 1);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 0);
lean_inc(x_174);
lean_dec(x_172);
x_175 = lean_ctor_get(x_173, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_173, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 lean_ctor_release(x_173, 2);
 x_177 = x_173;
} else {
 lean_dec_ref(x_173);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(0, 3, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_176);
lean_ctor_set(x_178, 2, x_169);
x_85 = x_174;
x_86 = x_178;
goto block_147;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_169);
lean_dec(x_84);
lean_dec(x_82);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_179 = lean_ctor_get(x_172, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_172, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_181 = x_172;
} else {
 lean_dec_ref(x_172);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_179);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
}
}
}
block_147:
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_expr_abstract_range(x_85, x_2, x_1);
lean_dec(x_85);
x_88 = l_Lean_Expr_hasMVar(x_84);
if (x_88 == 0)
{
lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_7);
x_89 = lean_expr_abstract_range(x_84, x_2, x_1);
lean_dec(x_1);
lean_dec(x_84);
x_90 = 0;
x_91 = l_Lean_mkLet(x_82, x_87, x_89, x_6, x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_86);
return x_92;
}
else
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_86);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_86, 2);
x_95 = l_HashMap_Inhabited___closed__1;
lean_ctor_set(x_86, 2, x_95);
lean_inc(x_1);
x_96 = lean_apply_3(x_7, x_1, x_84, x_86);
if (lean_obj_tag(x_96) == 0)
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_96, 1);
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_96, 0);
x_101 = lean_ctor_get(x_98, 2);
lean_dec(x_101);
lean_ctor_set(x_98, 2, x_94);
x_102 = lean_expr_abstract_range(x_100, x_2, x_1);
lean_dec(x_1);
lean_dec(x_100);
x_103 = 0;
x_104 = l_Lean_mkLet(x_82, x_87, x_102, x_6, x_103);
lean_ctor_set(x_96, 0, x_104);
return x_96;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; 
x_105 = lean_ctor_get(x_96, 0);
x_106 = lean_ctor_get(x_98, 0);
x_107 = lean_ctor_get(x_98, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_98);
x_108 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
lean_ctor_set(x_108, 2, x_94);
x_109 = lean_expr_abstract_range(x_105, x_2, x_1);
lean_dec(x_1);
lean_dec(x_105);
x_110 = 0;
x_111 = l_Lean_mkLet(x_82, x_87, x_109, x_6, x_110);
lean_ctor_set(x_96, 1, x_108);
lean_ctor_set(x_96, 0, x_111);
return x_96;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; 
x_112 = lean_ctor_get(x_96, 1);
x_113 = lean_ctor_get(x_96, 0);
lean_inc(x_112);
lean_inc(x_113);
lean_dec(x_96);
x_114 = lean_ctor_get(x_112, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_112, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 lean_ctor_release(x_112, 2);
 x_116 = x_112;
} else {
 lean_dec_ref(x_112);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(0, 3, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
lean_ctor_set(x_117, 2, x_94);
x_118 = lean_expr_abstract_range(x_113, x_2, x_1);
lean_dec(x_1);
lean_dec(x_113);
x_119 = 0;
x_120 = l_Lean_mkLet(x_82, x_87, x_118, x_6, x_119);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_117);
return x_121;
}
}
else
{
uint8_t x_122; 
lean_dec(x_94);
lean_dec(x_87);
lean_dec(x_82);
lean_dec(x_6);
lean_dec(x_1);
x_122 = !lean_is_exclusive(x_96);
if (x_122 == 0)
{
return x_96;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_96, 0);
x_124 = lean_ctor_get(x_96, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_96);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_126 = lean_ctor_get(x_86, 0);
x_127 = lean_ctor_get(x_86, 1);
x_128 = lean_ctor_get(x_86, 2);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_86);
x_129 = l_HashMap_Inhabited___closed__1;
x_130 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_130, 0, x_126);
lean_ctor_set(x_130, 1, x_127);
lean_ctor_set(x_130, 2, x_129);
lean_inc(x_1);
x_131 = lean_apply_3(x_7, x_1, x_84, x_130);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; 
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 0);
lean_inc(x_133);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_134 = x_131;
} else {
 lean_dec_ref(x_131);
 x_134 = lean_box(0);
}
x_135 = lean_ctor_get(x_132, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_132, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 lean_ctor_release(x_132, 2);
 x_137 = x_132;
} else {
 lean_dec_ref(x_132);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(0, 3, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
lean_ctor_set(x_138, 2, x_128);
x_139 = lean_expr_abstract_range(x_133, x_2, x_1);
lean_dec(x_1);
lean_dec(x_133);
x_140 = 0;
x_141 = l_Lean_mkLet(x_82, x_87, x_139, x_6, x_140);
if (lean_is_scalar(x_134)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_134;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_138);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_128);
lean_dec(x_87);
lean_dec(x_82);
lean_dec(x_6);
lean_dec(x_1);
x_143 = lean_ctor_get(x_131, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_131, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_145 = x_131;
} else {
 lean_dec_ref(x_131);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
}
}
}
}
}
}
}
lean_object* l_Nat_foldRevMAux___main___at___private_Init_Lean_MetavarContext_19__mkForallAux___spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_6, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_6, x_11);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
x_14 = lean_box(x_2);
lean_inc(x_1);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_12);
lean_inc(x_4);
x_15 = lean_alloc_closure((void*)(l_Nat_foldRevMAux___main___at___private_Init_Lean_MetavarContext_19__mkForallAux___spec__2___lambda__1___boxed), 8, 7);
lean_closure_set(x_15, 0, x_4);
lean_closure_set(x_15, 1, x_12);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_5);
lean_closure_set(x_15, 4, x_14);
lean_closure_set(x_15, 5, x_7);
lean_closure_set(x_15, 6, x_1);
x_16 = lean_box(x_2);
x_17 = lean_alloc_closure((void*)(l_Nat_foldRevMAux___main___at___private_Init_Lean_MetavarContext_19__mkForallAux___spec__2___boxed), 8, 6);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_16);
lean_closure_set(x_17, 2, x_3);
lean_closure_set(x_17, 3, x_4);
lean_closure_set(x_17, 4, x_5);
lean_closure_set(x_17, 5, x_12);
x_18 = lean_apply_5(x_13, lean_box(0), lean_box(0), x_15, x_17, x_8);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
lean_dec(x_5);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_apply_3(x_20, lean_box(0), x_7, x_8);
return x_21;
}
}
}
lean_object* l_Lean_MetavarContext_MkBinding_mkBinding___at___private_Init_Lean_MetavarContext_19__mkForallAux___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = l_Lean_Expr_hasMVar(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_expr_abstract_range(x_5, x_7, x_4);
lean_dec(x_5);
x_10 = l_EIO_Monad___closed__1;
x_11 = l_Nat_foldRevMAux___main___at___private_Init_Lean_MetavarContext_19__mkForallAux___spec__2(x_1, x_2, x_3, x_4, x_10, x_7, x_9, x_6);
lean_dec(x_7);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_6, 2);
x_14 = l_HashMap_Inhabited___closed__1;
lean_ctor_set(x_6, 2, x_14);
lean_inc(x_1);
lean_inc(x_4);
x_15 = lean_apply_3(x_1, x_4, x_5, x_6);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_16, 2);
lean_dec(x_19);
lean_ctor_set(x_16, 2, x_13);
x_20 = lean_expr_abstract_range(x_17, x_7, x_4);
lean_dec(x_17);
x_21 = l_EIO_Monad___closed__1;
x_22 = l_Nat_foldRevMAux___main___at___private_Init_Lean_MetavarContext_19__mkForallAux___spec__2(x_1, x_2, x_3, x_4, x_21, x_7, x_20, x_16);
lean_dec(x_7);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_13);
x_26 = lean_expr_abstract_range(x_17, x_7, x_4);
lean_dec(x_17);
x_27 = l_EIO_Monad___closed__1;
x_28 = l_Nat_foldRevMAux___main___at___private_Init_Lean_MetavarContext_19__mkForallAux___spec__2(x_1, x_2, x_3, x_4, x_27, x_7, x_26, x_25);
lean_dec(x_7);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_15);
if (x_29 == 0)
{
return x_15;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_15, 0);
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_15);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_6, 0);
x_34 = lean_ctor_get(x_6, 1);
x_35 = lean_ctor_get(x_6, 2);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_6);
x_36 = l_HashMap_Inhabited___closed__1;
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_34);
lean_ctor_set(x_37, 2, x_36);
lean_inc(x_1);
lean_inc(x_4);
x_38 = lean_apply_3(x_1, x_4, x_5, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 x_43 = x_39;
} else {
 lean_dec_ref(x_39);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 3, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set(x_44, 2, x_35);
x_45 = lean_expr_abstract_range(x_40, x_7, x_4);
lean_dec(x_40);
x_46 = l_EIO_Monad___closed__1;
x_47 = l_Nat_foldRevMAux___main___at___private_Init_Lean_MetavarContext_19__mkForallAux___spec__2(x_1, x_2, x_3, x_4, x_46, x_7, x_45, x_44);
lean_dec(x_7);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_35);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_48 = lean_ctor_get(x_38, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_38, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_50 = x_38;
} else {
 lean_dec_ref(x_38);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
}
}
lean_object* l___private_Init_Lean_MetavarContext_19__mkForallAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = 0;
x_7 = l_Lean_MetavarContext_MkBinding_mkBinding___at___private_Init_Lean_MetavarContext_19__mkForallAux___spec__1(x_1, x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Nat_foldRevMAux___main___at___private_Init_Lean_MetavarContext_19__mkForallAux___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l_Nat_foldRevMAux___main___at___private_Init_Lean_MetavarContext_19__mkForallAux___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_9, x_6, x_7, x_8);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Nat_foldRevMAux___main___at___private_Init_Lean_MetavarContext_19__mkForallAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Nat_foldRevMAux___main___at___private_Init_Lean_MetavarContext_19__mkForallAux___spec__2(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
return x_10;
}
}
lean_object* l_Lean_MetavarContext_MkBinding_mkBinding___at___private_Init_Lean_MetavarContext_19__mkForallAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l_Lean_MetavarContext_MkBinding_mkBinding___at___private_Init_Lean_MetavarContext_19__mkForallAux___spec__1(x_1, x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_20__mkMVarApp___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_array_fget(x_3, x_4);
lean_inc(x_1);
x_9 = l_Lean_LocalContext_findFVar(x_1, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = l_Lean_LocalDecl_Inhabited;
x_13 = l_Option_get_x21___rarg___closed__3;
x_14 = lean_panic_fn(x_13);
x_15 = l_Lean_LocalDecl_isLet(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = l_Lean_mkApp(x_5, x_8);
x_4 = x_11;
x_5 = x_16;
goto _start;
}
else
{
lean_dec(x_8);
x_4 = x_11;
goto _start;
}
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_9, 0);
lean_inc(x_19);
lean_dec(x_9);
x_20 = l_Lean_LocalDecl_isLet(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = l_Lean_mkApp(x_5, x_8);
x_4 = x_11;
x_5 = x_21;
goto _start;
}
else
{
lean_dec(x_8);
x_4 = x_11;
goto _start;
}
}
}
}
}
lean_object* l___private_Init_Lean_MetavarContext_20__mkMVarApp(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_20__mkMVarApp___spec__1(x_1, x_3, x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_20__mkMVarApp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_20__mkMVarApp___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l___private_Init_Lean_MetavarContext_20__mkMVarApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_MetavarContext_20__mkMVarApp(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_MetavarContext_21__mkAuxMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_inc(x_10);
x_12 = lean_name_mk_numeral(x_10, x_11);
x_13 = lean_box(0);
lean_inc(x_12);
x_14 = lean_metavar_ctx_mk_decl(x_9, x_12, x_13, x_1, x_2, x_3, x_4);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_11, x_15);
lean_dec(x_11);
lean_ctor_set(x_7, 1, x_16);
lean_ctor_set(x_5, 0, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_5);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_7, 0);
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_7);
lean_inc(x_20);
lean_inc(x_19);
x_21 = lean_name_mk_numeral(x_19, x_20);
x_22 = lean_box(0);
lean_inc(x_21);
x_23 = lean_metavar_ctx_mk_decl(x_18, x_21, x_22, x_1, x_2, x_3, x_4);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_20, x_24);
lean_dec(x_20);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_19);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_5, 1, x_26);
lean_ctor_set(x_5, 0, x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_5);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_28 = lean_ctor_get(x_5, 1);
x_29 = lean_ctor_get(x_5, 0);
x_30 = lean_ctor_get(x_5, 2);
lean_inc(x_30);
lean_inc(x_28);
lean_inc(x_29);
lean_dec(x_5);
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_33 = x_28;
} else {
 lean_dec_ref(x_28);
 x_33 = lean_box(0);
}
lean_inc(x_32);
lean_inc(x_31);
x_34 = lean_name_mk_numeral(x_31, x_32);
x_35 = lean_box(0);
lean_inc(x_34);
x_36 = lean_metavar_ctx_mk_decl(x_29, x_34, x_35, x_1, x_2, x_3, x_4);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_32, x_37);
lean_dec(x_32);
if (lean_is_scalar(x_33)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_33;
}
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_30);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_34);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
lean_object* l___private_Init_Lean_MetavarContext_21__mkAuxMVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l___private_Init_Lean_MetavarContext_21__mkAuxMVar(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_expr_eqv(x_9, x_8);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_5, x_11);
lean_dec(x_5);
x_5 = x_12;
goto _start;
}
else
{
uint8_t x_14; 
lean_dec(x_5);
x_14 = 1;
return x_14;
}
}
}
}
lean_object* l_Array_filterAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = l_Array_shrink___main___rarg(x_2, x_4);
lean_dec(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_array_fget(x_2, x_3);
x_9 = lean_array_get_size(x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__1(x_1, x_8, x_1, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = lean_nat_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_3, x_13);
lean_dec(x_3);
x_15 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
x_3 = x_14;
x_4 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_array_fswap(x_2, x_3, x_4);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_3, x_18);
lean_dec(x_3);
x_20 = lean_nat_add(x_4, x_18);
lean_dec(x_4);
x_2 = x_17;
x_3 = x_19;
x_4 = x_20;
goto _start;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_3, x_22);
lean_dec(x_3);
x_3 = x_23;
goto _start;
}
}
}
}
lean_object* l_Nat_foldRevMAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Expr_Inhabited;
x_9 = lean_array_get(x_8, x_1, x_2);
x_10 = l_Lean_LocalContext_findFVar(x_3, x_9);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
x_11 = l_monadInhabited___rarg(x_4, x_8);
x_12 = l_Lean_MetavarContext_MkBinding_mkBinding___lambda__1___closed__1;
x_13 = lean_panic_fn(x_12);
x_14 = lean_apply_1(x_13, x_7);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_4);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_15, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 3);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_15, sizeof(void*)*4);
lean_dec(x_15);
x_19 = l_Lean_Expr_hasMVar(x_17);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_expr_abstract_range(x_17, x_2, x_1);
lean_dec(x_17);
if (x_5 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_mkForall(x_16, x_18, x_20, x_6);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_7);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_mkLambda(x_16, x_18, x_20, x_6);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_7);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_7);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_7, 2);
x_27 = l_HashMap_Inhabited___closed__1;
lean_ctor_set(x_7, 2, x_27);
x_28 = l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main(x_1, x_17, x_7);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
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
x_33 = lean_ctor_get(x_30, 2);
lean_dec(x_33);
lean_ctor_set(x_30, 2, x_26);
x_34 = lean_expr_abstract_range(x_32, x_2, x_1);
lean_dec(x_32);
if (x_5 == 0)
{
lean_object* x_35; 
x_35 = l_Lean_mkForall(x_16, x_18, x_34, x_6);
lean_ctor_set(x_28, 0, x_35);
return x_28;
}
else
{
lean_object* x_36; 
x_36 = l_Lean_mkLambda(x_16, x_18, x_34, x_6);
lean_ctor_set(x_28, 0, x_36);
return x_28;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_28, 0);
x_38 = lean_ctor_get(x_30, 0);
x_39 = lean_ctor_get(x_30, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_30);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_26);
x_41 = lean_expr_abstract_range(x_37, x_2, x_1);
lean_dec(x_37);
if (x_5 == 0)
{
lean_object* x_42; 
x_42 = l_Lean_mkForall(x_16, x_18, x_41, x_6);
lean_ctor_set(x_28, 1, x_40);
lean_ctor_set(x_28, 0, x_42);
return x_28;
}
else
{
lean_object* x_43; 
x_43 = l_Lean_mkLambda(x_16, x_18, x_41, x_6);
lean_ctor_set(x_28, 1, x_40);
lean_ctor_set(x_28, 0, x_43);
return x_28;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = lean_ctor_get(x_28, 1);
x_45 = lean_ctor_get(x_28, 0);
lean_inc(x_44);
lean_inc(x_45);
lean_dec(x_28);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 x_48 = x_44;
} else {
 lean_dec_ref(x_44);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(0, 3, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_49, 2, x_26);
x_50 = lean_expr_abstract_range(x_45, x_2, x_1);
lean_dec(x_45);
if (x_5 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = l_Lean_mkForall(x_16, x_18, x_50, x_6);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = l_Lean_mkLambda(x_16, x_18, x_50, x_6);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_49);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_26);
lean_dec(x_16);
lean_dec(x_6);
x_55 = !lean_is_exclusive(x_28);
if (x_55 == 0)
{
return x_28;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_28, 0);
x_57 = lean_ctor_get(x_28, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_28);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_7, 0);
x_60 = lean_ctor_get(x_7, 1);
x_61 = lean_ctor_get(x_7, 2);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_7);
x_62 = l_HashMap_Inhabited___closed__1;
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_59);
lean_ctor_set(x_63, 1, x_60);
lean_ctor_set(x_63, 2, x_62);
x_64 = l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main(x_1, x_17, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_67 = x_64;
} else {
 lean_dec_ref(x_64);
 x_67 = lean_box(0);
}
x_68 = lean_ctor_get(x_65, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 lean_ctor_release(x_65, 2);
 x_70 = x_65;
} else {
 lean_dec_ref(x_65);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(0, 3, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
lean_ctor_set(x_71, 2, x_61);
x_72 = lean_expr_abstract_range(x_66, x_2, x_1);
lean_dec(x_66);
if (x_5 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = l_Lean_mkForall(x_16, x_18, x_72, x_6);
if (lean_is_scalar(x_67)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_67;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = l_Lean_mkLambda(x_16, x_18, x_72, x_6);
if (lean_is_scalar(x_67)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_67;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_71);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_61);
lean_dec(x_16);
lean_dec(x_6);
x_77 = lean_ctor_get(x_64, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_64, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_79 = x_64;
} else {
 lean_dec_ref(x_64);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_147; uint8_t x_148; 
x_81 = lean_ctor_get(x_15, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_15, 3);
lean_inc(x_82);
x_83 = lean_ctor_get(x_15, 4);
lean_inc(x_83);
lean_dec(x_15);
x_147 = lean_unsigned_to_nat(0u);
x_148 = lean_expr_has_loose_bvar(x_6, x_147);
if (x_148 == 0)
{
lean_object* x_149; 
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_6);
lean_ctor_set(x_149, 1, x_7);
return x_149;
}
else
{
uint8_t x_150; 
x_150 = l_Lean_Expr_hasMVar(x_82);
if (x_150 == 0)
{
x_84 = x_82;
x_85 = x_7;
goto block_146;
}
else
{
uint8_t x_151; 
x_151 = !lean_is_exclusive(x_7);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_7, 2);
x_153 = l_HashMap_Inhabited___closed__1;
lean_ctor_set(x_7, 2, x_153);
x_154 = l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main(x_1, x_82, x_7);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 0);
lean_inc(x_156);
lean_dec(x_154);
x_157 = !lean_is_exclusive(x_155);
if (x_157 == 0)
{
lean_object* x_158; 
x_158 = lean_ctor_get(x_155, 2);
lean_dec(x_158);
lean_ctor_set(x_155, 2, x_152);
x_84 = x_156;
x_85 = x_155;
goto block_146;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_155, 0);
x_160 = lean_ctor_get(x_155, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_155);
x_161 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
lean_ctor_set(x_161, 2, x_152);
x_84 = x_156;
x_85 = x_161;
goto block_146;
}
}
else
{
uint8_t x_162; 
lean_dec(x_152);
lean_dec(x_83);
lean_dec(x_81);
lean_dec(x_6);
x_162 = !lean_is_exclusive(x_154);
if (x_162 == 0)
{
return x_154;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_154, 0);
x_164 = lean_ctor_get(x_154, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_154);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_166 = lean_ctor_get(x_7, 0);
x_167 = lean_ctor_get(x_7, 1);
x_168 = lean_ctor_get(x_7, 2);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_7);
x_169 = l_HashMap_Inhabited___closed__1;
x_170 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_170, 0, x_166);
lean_ctor_set(x_170, 1, x_167);
lean_ctor_set(x_170, 2, x_169);
x_171 = l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main(x_1, x_82, x_170);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_172 = lean_ctor_get(x_171, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 0);
lean_inc(x_173);
lean_dec(x_171);
x_174 = lean_ctor_get(x_172, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_172, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 lean_ctor_release(x_172, 2);
 x_176 = x_172;
} else {
 lean_dec_ref(x_172);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(0, 3, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
lean_ctor_set(x_177, 2, x_168);
x_84 = x_173;
x_85 = x_177;
goto block_146;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_168);
lean_dec(x_83);
lean_dec(x_81);
lean_dec(x_6);
x_178 = lean_ctor_get(x_171, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_171, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_180 = x_171;
} else {
 lean_dec_ref(x_171);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(1, 2, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_178);
lean_ctor_set(x_181, 1, x_179);
return x_181;
}
}
}
}
block_146:
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_expr_abstract_range(x_84, x_2, x_1);
lean_dec(x_84);
x_87 = l_Lean_Expr_hasMVar(x_83);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_expr_abstract_range(x_83, x_2, x_1);
lean_dec(x_83);
x_89 = 0;
x_90 = l_Lean_mkLet(x_81, x_86, x_88, x_6, x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_85);
return x_91;
}
else
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_85);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_85, 2);
x_94 = l_HashMap_Inhabited___closed__1;
lean_ctor_set(x_85, 2, x_94);
x_95 = l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main(x_1, x_83, x_85);
if (lean_obj_tag(x_95) == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_95, 1);
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; 
x_99 = lean_ctor_get(x_95, 0);
x_100 = lean_ctor_get(x_97, 2);
lean_dec(x_100);
lean_ctor_set(x_97, 2, x_93);
x_101 = lean_expr_abstract_range(x_99, x_2, x_1);
lean_dec(x_99);
x_102 = 0;
x_103 = l_Lean_mkLet(x_81, x_86, x_101, x_6, x_102);
lean_ctor_set(x_95, 0, x_103);
return x_95;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; 
x_104 = lean_ctor_get(x_95, 0);
x_105 = lean_ctor_get(x_97, 0);
x_106 = lean_ctor_get(x_97, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_97);
x_107 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
lean_ctor_set(x_107, 2, x_93);
x_108 = lean_expr_abstract_range(x_104, x_2, x_1);
lean_dec(x_104);
x_109 = 0;
x_110 = l_Lean_mkLet(x_81, x_86, x_108, x_6, x_109);
lean_ctor_set(x_95, 1, x_107);
lean_ctor_set(x_95, 0, x_110);
return x_95;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; 
x_111 = lean_ctor_get(x_95, 1);
x_112 = lean_ctor_get(x_95, 0);
lean_inc(x_111);
lean_inc(x_112);
lean_dec(x_95);
x_113 = lean_ctor_get(x_111, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_111, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 lean_ctor_release(x_111, 2);
 x_115 = x_111;
} else {
 lean_dec_ref(x_111);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(0, 3, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
lean_ctor_set(x_116, 2, x_93);
x_117 = lean_expr_abstract_range(x_112, x_2, x_1);
lean_dec(x_112);
x_118 = 0;
x_119 = l_Lean_mkLet(x_81, x_86, x_117, x_6, x_118);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_116);
return x_120;
}
}
else
{
uint8_t x_121; 
lean_dec(x_93);
lean_dec(x_86);
lean_dec(x_81);
lean_dec(x_6);
x_121 = !lean_is_exclusive(x_95);
if (x_121 == 0)
{
return x_95;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_95, 0);
x_123 = lean_ctor_get(x_95, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_95);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_125 = lean_ctor_get(x_85, 0);
x_126 = lean_ctor_get(x_85, 1);
x_127 = lean_ctor_get(x_85, 2);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_85);
x_128 = l_HashMap_Inhabited___closed__1;
x_129 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_129, 0, x_125);
lean_ctor_set(x_129, 1, x_126);
lean_ctor_set(x_129, 2, x_128);
x_130 = l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main(x_1, x_83, x_129);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; 
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 0);
lean_inc(x_132);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_133 = x_130;
} else {
 lean_dec_ref(x_130);
 x_133 = lean_box(0);
}
x_134 = lean_ctor_get(x_131, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_131, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 lean_ctor_release(x_131, 2);
 x_136 = x_131;
} else {
 lean_dec_ref(x_131);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(0, 3, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_135);
lean_ctor_set(x_137, 2, x_127);
x_138 = lean_expr_abstract_range(x_132, x_2, x_1);
lean_dec(x_132);
x_139 = 0;
x_140 = l_Lean_mkLet(x_81, x_86, x_138, x_6, x_139);
if (lean_is_scalar(x_133)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_133;
}
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_137);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_127);
lean_dec(x_86);
lean_dec(x_81);
lean_dec(x_6);
x_142 = lean_ctor_get(x_130, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_130, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_144 = x_130;
} else {
 lean_dec_ref(x_130);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
}
}
}
}
}
}
}
lean_object* l_Nat_foldRevMAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__4(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_5, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_5, x_10);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
x_13 = lean_box(x_1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_11);
lean_inc(x_3);
x_14 = lean_alloc_closure((void*)(l_Nat_foldRevMAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__4___lambda__1___boxed), 7, 6);
lean_closure_set(x_14, 0, x_3);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_2);
lean_closure_set(x_14, 3, x_4);
lean_closure_set(x_14, 4, x_13);
lean_closure_set(x_14, 5, x_6);
x_15 = lean_box(x_1);
x_16 = lean_alloc_closure((void*)(l_Nat_foldRevMAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__4___boxed), 7, 5);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_3);
lean_closure_set(x_16, 3, x_4);
lean_closure_set(x_16, 4, x_11);
x_17 = lean_apply_5(x_12, lean_box(0), lean_box(0), x_14, x_16, x_7);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_ctor_get(x_4, 0);
lean_inc(x_18);
lean_dec(x_4);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_apply_3(x_19, lean_box(0), x_6, x_7);
return x_20;
}
}
}
lean_object* l_Lean_MetavarContext_MkBinding_mkBinding___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = l_Lean_Expr_hasMVar(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_expr_abstract_range(x_4, x_6, x_3);
lean_dec(x_4);
x_9 = l_EIO_Monad___closed__1;
x_10 = l_Nat_foldRevMAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__4(x_1, x_2, x_3, x_9, x_6, x_8, x_5);
lean_dec(x_6);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_5);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_5, 2);
x_13 = l_HashMap_Inhabited___closed__1;
lean_ctor_set(x_5, 2, x_13);
x_14 = l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main(x_3, x_4, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_15, 2);
lean_dec(x_18);
lean_ctor_set(x_15, 2, x_12);
x_19 = lean_expr_abstract_range(x_16, x_6, x_3);
lean_dec(x_16);
x_20 = l_EIO_Monad___closed__1;
x_21 = l_Nat_foldRevMAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__4(x_1, x_2, x_3, x_20, x_6, x_19, x_15);
lean_dec(x_6);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_12);
x_25 = lean_expr_abstract_range(x_16, x_6, x_3);
lean_dec(x_16);
x_26 = l_EIO_Monad___closed__1;
x_27 = l_Nat_foldRevMAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__4(x_1, x_2, x_3, x_26, x_6, x_25, x_24);
lean_dec(x_6);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_14);
if (x_28 == 0)
{
return x_14;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_14, 0);
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_14);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_5, 0);
x_33 = lean_ctor_get(x_5, 1);
x_34 = lean_ctor_get(x_5, 2);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_5);
x_35 = l_HashMap_Inhabited___closed__1;
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set(x_36, 2, x_35);
x_37 = l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main(x_3, x_4, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 x_42 = x_38;
} else {
 lean_dec_ref(x_38);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(0, 3, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
lean_ctor_set(x_43, 2, x_34);
x_44 = lean_expr_abstract_range(x_39, x_6, x_3);
lean_dec(x_39);
x_45 = l_EIO_Monad___closed__1;
x_46 = l_Nat_foldRevMAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__4(x_1, x_2, x_3, x_45, x_6, x_44, x_43);
lean_dec(x_6);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_34);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_47 = lean_ctor_get(x_37, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_37, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_49 = x_37;
} else {
 lean_dec_ref(x_37);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_14 = l_Lean_Expr_hasMVar(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_2, x_15);
lean_inc(x_10);
x_17 = x_10;
x_18 = lean_array_fset(x_13, x_2, x_17);
lean_dec(x_2);
x_2 = x_16;
x_3 = x_18;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_4, 2);
lean_inc(x_20);
x_21 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_20, x_10);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
lean_inc(x_10);
x_22 = l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main(x_1, x_10, x_4);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_23, 2);
lean_inc(x_24);
lean_inc(x_10);
x_27 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_26, x_10, x_24);
lean_ctor_set(x_23, 2, x_27);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_2, x_28);
x_30 = x_24;
x_31 = lean_array_fset(x_13, x_2, x_30);
lean_dec(x_2);
x_2 = x_29;
x_3 = x_31;
x_4 = x_23;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_23, 0);
x_34 = lean_ctor_get(x_23, 1);
x_35 = lean_ctor_get(x_23, 2);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_23);
lean_inc(x_24);
lean_inc(x_10);
x_36 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_35, x_10, x_24);
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_34);
lean_ctor_set(x_37, 2, x_36);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_2, x_38);
x_40 = x_24;
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
uint8_t x_43; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_22);
if (x_43 == 0)
{
return x_22;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_22, 0);
x_45 = lean_ctor_get(x_22, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_22);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_21, 0);
lean_inc(x_47);
lean_dec(x_21);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_add(x_2, x_48);
x_50 = x_47;
x_51 = lean_array_fset(x_13, x_2, x_50);
lean_dec(x_2);
x_2 = x_49;
x_3 = x_51;
goto _start;
}
}
}
}
}
lean_object* l___private_Init_Lean_Expr_5__withAppRevAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; uint8_t x_34; 
x_5 = l_Lean_Expr_isMVar(x_2);
x_34 = l_Lean_Expr_hasMVar(x_2);
if (x_34 == 0)
{
x_6 = x_2;
x_7 = x_4;
goto block_33;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_4, 2);
lean_inc(x_35);
x_36 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_35, x_2);
lean_dec(x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
lean_inc(x_2);
x_37 = l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main(x_1, x_2, x_4);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
x_40 = !lean_is_exclusive(x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 2);
lean_inc(x_39);
x_42 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_41, x_2, x_39);
lean_ctor_set(x_38, 2, x_42);
x_6 = x_39;
x_7 = x_38;
goto block_33;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_38, 0);
x_44 = lean_ctor_get(x_38, 1);
x_45 = lean_ctor_get(x_38, 2);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_38);
lean_inc(x_39);
x_46 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_45, x_2, x_39);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_44);
lean_ctor_set(x_47, 2, x_46);
x_6 = x_39;
x_7 = x_47;
goto block_33;
}
}
else
{
uint8_t x_48; 
lean_dec(x_3);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_37);
if (x_48 == 0)
{
return x_37;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_37, 0);
x_50 = lean_ctor_get(x_37, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_37);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; 
lean_dec(x_2);
x_52 = lean_ctor_get(x_36, 0);
lean_inc(x_52);
lean_dec(x_36);
x_6 = x_52;
x_7 = x_4;
goto block_33;
}
}
block_33:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_umapMAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__5(x_1, x_8, x_3, x_7);
if (lean_obj_tag(x_9) == 0)
{
if (x_5 == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_mkAppRev(x_6, x_11);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_12);
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
x_15 = l_Lean_mkAppRev(x_6, x_13);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = l_Lean_Expr_isLambda(x_6);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = l_Lean_mkAppRev(x_6, x_18);
lean_dec(x_18);
lean_ctor_set(x_9, 0, x_20);
return x_9;
}
else
{
lean_object* x_21; 
x_21 = l_Lean_Expr_betaRev(x_6, x_18);
lean_dec(x_6);
lean_ctor_set(x_9, 0, x_21);
return x_9;
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
x_24 = l_Lean_Expr_isLambda(x_6);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_mkAppRev(x_6, x_22);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Lean_Expr_betaRev(x_6, x_22);
lean_dec(x_6);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
return x_28;
}
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_6);
x_29 = !lean_is_exclusive(x_9);
if (x_29 == 0)
{
return x_9;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_9, 0);
x_31 = lean_ctor_get(x_9, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_9);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
case 1:
{
uint8_t x_53; lean_object* x_54; lean_object* x_55; uint8_t x_82; 
x_53 = l_Lean_Expr_isMVar(x_2);
x_82 = l_Lean_Expr_hasMVar(x_2);
if (x_82 == 0)
{
x_54 = x_2;
x_55 = x_4;
goto block_81;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_4, 2);
lean_inc(x_83);
x_84 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_83, x_2);
lean_dec(x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; 
lean_inc(x_2);
x_85 = l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main(x_1, x_2, x_4);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
lean_dec(x_85);
x_88 = !lean_is_exclusive(x_86);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_86, 2);
lean_inc(x_87);
x_90 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_89, x_2, x_87);
lean_ctor_set(x_86, 2, x_90);
x_54 = x_87;
x_55 = x_86;
goto block_81;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_91 = lean_ctor_get(x_86, 0);
x_92 = lean_ctor_get(x_86, 1);
x_93 = lean_ctor_get(x_86, 2);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_86);
lean_inc(x_87);
x_94 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_93, x_2, x_87);
x_95 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_95, 0, x_91);
lean_ctor_set(x_95, 1, x_92);
lean_ctor_set(x_95, 2, x_94);
x_54 = x_87;
x_55 = x_95;
goto block_81;
}
}
else
{
uint8_t x_96; 
lean_dec(x_3);
lean_dec(x_2);
x_96 = !lean_is_exclusive(x_85);
if (x_96 == 0)
{
return x_85;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_85, 0);
x_98 = lean_ctor_get(x_85, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_85);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
lean_object* x_100; 
lean_dec(x_2);
x_100 = lean_ctor_get(x_84, 0);
lean_inc(x_100);
lean_dec(x_84);
x_54 = x_100;
x_55 = x_4;
goto block_81;
}
}
block_81:
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_unsigned_to_nat(0u);
x_57 = l_Array_umapMAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__5(x_1, x_56, x_3, x_55);
if (lean_obj_tag(x_57) == 0)
{
if (x_53 == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = l_Lean_mkAppRev(x_54, x_59);
lean_dec(x_59);
lean_ctor_set(x_57, 0, x_60);
return x_57;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_57, 0);
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_57);
x_63 = l_Lean_mkAppRev(x_54, x_61);
lean_dec(x_61);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_57);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_57, 0);
x_67 = l_Lean_Expr_isLambda(x_54);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = l_Lean_mkAppRev(x_54, x_66);
lean_dec(x_66);
lean_ctor_set(x_57, 0, x_68);
return x_57;
}
else
{
lean_object* x_69; 
x_69 = l_Lean_Expr_betaRev(x_54, x_66);
lean_dec(x_54);
lean_ctor_set(x_57, 0, x_69);
return x_57;
}
}
else
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_70 = lean_ctor_get(x_57, 0);
x_71 = lean_ctor_get(x_57, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_57);
x_72 = l_Lean_Expr_isLambda(x_54);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = l_Lean_mkAppRev(x_54, x_70);
lean_dec(x_70);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = l_Lean_Expr_betaRev(x_54, x_70);
lean_dec(x_54);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_71);
return x_76;
}
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_54);
x_77 = !lean_is_exclusive(x_57);
if (x_77 == 0)
{
return x_57;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_57, 0);
x_79 = lean_ctor_get(x_57, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_57);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
case 2:
{
uint8_t x_101; lean_object* x_102; lean_object* x_103; uint8_t x_130; 
x_101 = l_Lean_Expr_isMVar(x_2);
x_130 = l_Lean_Expr_hasMVar(x_2);
if (x_130 == 0)
{
x_102 = x_2;
x_103 = x_4;
goto block_129;
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_4, 2);
lean_inc(x_131);
x_132 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_131, x_2);
lean_dec(x_131);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; 
lean_inc(x_2);
x_133 = l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main(x_1, x_2, x_4);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
lean_dec(x_133);
x_136 = !lean_is_exclusive(x_134);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_134, 2);
lean_inc(x_135);
x_138 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_137, x_2, x_135);
lean_ctor_set(x_134, 2, x_138);
x_102 = x_135;
x_103 = x_134;
goto block_129;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_139 = lean_ctor_get(x_134, 0);
x_140 = lean_ctor_get(x_134, 1);
x_141 = lean_ctor_get(x_134, 2);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_134);
lean_inc(x_135);
x_142 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_141, x_2, x_135);
x_143 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_143, 0, x_139);
lean_ctor_set(x_143, 1, x_140);
lean_ctor_set(x_143, 2, x_142);
x_102 = x_135;
x_103 = x_143;
goto block_129;
}
}
else
{
uint8_t x_144; 
lean_dec(x_3);
lean_dec(x_2);
x_144 = !lean_is_exclusive(x_133);
if (x_144 == 0)
{
return x_133;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_133, 0);
x_146 = lean_ctor_get(x_133, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_133);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
else
{
lean_object* x_148; 
lean_dec(x_2);
x_148 = lean_ctor_get(x_132, 0);
lean_inc(x_148);
lean_dec(x_132);
x_102 = x_148;
x_103 = x_4;
goto block_129;
}
}
block_129:
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_unsigned_to_nat(0u);
x_105 = l_Array_umapMAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__5(x_1, x_104, x_3, x_103);
if (lean_obj_tag(x_105) == 0)
{
if (x_101 == 0)
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_105, 0);
x_108 = l_Lean_mkAppRev(x_102, x_107);
lean_dec(x_107);
lean_ctor_set(x_105, 0, x_108);
return x_105;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_105, 0);
x_110 = lean_ctor_get(x_105, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_105);
x_111 = l_Lean_mkAppRev(x_102, x_109);
lean_dec(x_109);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
else
{
uint8_t x_113; 
x_113 = !lean_is_exclusive(x_105);
if (x_113 == 0)
{
lean_object* x_114; uint8_t x_115; 
x_114 = lean_ctor_get(x_105, 0);
x_115 = l_Lean_Expr_isLambda(x_102);
if (x_115 == 0)
{
lean_object* x_116; 
x_116 = l_Lean_mkAppRev(x_102, x_114);
lean_dec(x_114);
lean_ctor_set(x_105, 0, x_116);
return x_105;
}
else
{
lean_object* x_117; 
x_117 = l_Lean_Expr_betaRev(x_102, x_114);
lean_dec(x_102);
lean_ctor_set(x_105, 0, x_117);
return x_105;
}
}
else
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_118 = lean_ctor_get(x_105, 0);
x_119 = lean_ctor_get(x_105, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_105);
x_120 = l_Lean_Expr_isLambda(x_102);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = l_Lean_mkAppRev(x_102, x_118);
lean_dec(x_118);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_119);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; 
x_123 = l_Lean_Expr_betaRev(x_102, x_118);
lean_dec(x_102);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_119);
return x_124;
}
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_102);
x_125 = !lean_is_exclusive(x_105);
if (x_125 == 0)
{
return x_105;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_105, 0);
x_127 = lean_ctor_get(x_105, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_105);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
}
case 3:
{
uint8_t x_149; lean_object* x_150; lean_object* x_151; uint8_t x_178; 
x_149 = l_Lean_Expr_isMVar(x_2);
x_178 = l_Lean_Expr_hasMVar(x_2);
if (x_178 == 0)
{
x_150 = x_2;
x_151 = x_4;
goto block_177;
}
else
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_4, 2);
lean_inc(x_179);
x_180 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_179, x_2);
lean_dec(x_179);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; 
lean_inc(x_2);
x_181 = l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main(x_1, x_2, x_4);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 0);
lean_inc(x_183);
lean_dec(x_181);
x_184 = !lean_is_exclusive(x_182);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_ctor_get(x_182, 2);
lean_inc(x_183);
x_186 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_185, x_2, x_183);
lean_ctor_set(x_182, 2, x_186);
x_150 = x_183;
x_151 = x_182;
goto block_177;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_187 = lean_ctor_get(x_182, 0);
x_188 = lean_ctor_get(x_182, 1);
x_189 = lean_ctor_get(x_182, 2);
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_182);
lean_inc(x_183);
x_190 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_189, x_2, x_183);
x_191 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_191, 0, x_187);
lean_ctor_set(x_191, 1, x_188);
lean_ctor_set(x_191, 2, x_190);
x_150 = x_183;
x_151 = x_191;
goto block_177;
}
}
else
{
uint8_t x_192; 
lean_dec(x_3);
lean_dec(x_2);
x_192 = !lean_is_exclusive(x_181);
if (x_192 == 0)
{
return x_181;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_181, 0);
x_194 = lean_ctor_get(x_181, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_181);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
else
{
lean_object* x_196; 
lean_dec(x_2);
x_196 = lean_ctor_get(x_180, 0);
lean_inc(x_196);
lean_dec(x_180);
x_150 = x_196;
x_151 = x_4;
goto block_177;
}
}
block_177:
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_unsigned_to_nat(0u);
x_153 = l_Array_umapMAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__5(x_1, x_152, x_3, x_151);
if (lean_obj_tag(x_153) == 0)
{
if (x_149 == 0)
{
uint8_t x_154; 
x_154 = !lean_is_exclusive(x_153);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_153, 0);
x_156 = l_Lean_mkAppRev(x_150, x_155);
lean_dec(x_155);
lean_ctor_set(x_153, 0, x_156);
return x_153;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_157 = lean_ctor_get(x_153, 0);
x_158 = lean_ctor_get(x_153, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_153);
x_159 = l_Lean_mkAppRev(x_150, x_157);
lean_dec(x_157);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
else
{
uint8_t x_161; 
x_161 = !lean_is_exclusive(x_153);
if (x_161 == 0)
{
lean_object* x_162; uint8_t x_163; 
x_162 = lean_ctor_get(x_153, 0);
x_163 = l_Lean_Expr_isLambda(x_150);
if (x_163 == 0)
{
lean_object* x_164; 
x_164 = l_Lean_mkAppRev(x_150, x_162);
lean_dec(x_162);
lean_ctor_set(x_153, 0, x_164);
return x_153;
}
else
{
lean_object* x_165; 
x_165 = l_Lean_Expr_betaRev(x_150, x_162);
lean_dec(x_150);
lean_ctor_set(x_153, 0, x_165);
return x_153;
}
}
else
{
lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_166 = lean_ctor_get(x_153, 0);
x_167 = lean_ctor_get(x_153, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_153);
x_168 = l_Lean_Expr_isLambda(x_150);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; 
x_169 = l_Lean_mkAppRev(x_150, x_166);
lean_dec(x_166);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_167);
return x_170;
}
else
{
lean_object* x_171; lean_object* x_172; 
x_171 = l_Lean_Expr_betaRev(x_150, x_166);
lean_dec(x_150);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_167);
return x_172;
}
}
}
}
else
{
uint8_t x_173; 
lean_dec(x_150);
x_173 = !lean_is_exclusive(x_153);
if (x_173 == 0)
{
return x_153;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_153, 0);
x_175 = lean_ctor_get(x_153, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_153);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
}
}
case 4:
{
uint8_t x_197; lean_object* x_198; lean_object* x_199; uint8_t x_226; 
x_197 = l_Lean_Expr_isMVar(x_2);
x_226 = l_Lean_Expr_hasMVar(x_2);
if (x_226 == 0)
{
x_198 = x_2;
x_199 = x_4;
goto block_225;
}
else
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_ctor_get(x_4, 2);
lean_inc(x_227);
x_228 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_227, x_2);
lean_dec(x_227);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; 
lean_inc(x_2);
x_229 = l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main(x_1, x_2, x_4);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; uint8_t x_232; 
x_230 = lean_ctor_get(x_229, 1);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 0);
lean_inc(x_231);
lean_dec(x_229);
x_232 = !lean_is_exclusive(x_230);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; 
x_233 = lean_ctor_get(x_230, 2);
lean_inc(x_231);
x_234 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_233, x_2, x_231);
lean_ctor_set(x_230, 2, x_234);
x_198 = x_231;
x_199 = x_230;
goto block_225;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_235 = lean_ctor_get(x_230, 0);
x_236 = lean_ctor_get(x_230, 1);
x_237 = lean_ctor_get(x_230, 2);
lean_inc(x_237);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_230);
lean_inc(x_231);
x_238 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_237, x_2, x_231);
x_239 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_239, 0, x_235);
lean_ctor_set(x_239, 1, x_236);
lean_ctor_set(x_239, 2, x_238);
x_198 = x_231;
x_199 = x_239;
goto block_225;
}
}
else
{
uint8_t x_240; 
lean_dec(x_3);
lean_dec(x_2);
x_240 = !lean_is_exclusive(x_229);
if (x_240 == 0)
{
return x_229;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_241 = lean_ctor_get(x_229, 0);
x_242 = lean_ctor_get(x_229, 1);
lean_inc(x_242);
lean_inc(x_241);
lean_dec(x_229);
x_243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_243, 0, x_241);
lean_ctor_set(x_243, 1, x_242);
return x_243;
}
}
}
else
{
lean_object* x_244; 
lean_dec(x_2);
x_244 = lean_ctor_get(x_228, 0);
lean_inc(x_244);
lean_dec(x_228);
x_198 = x_244;
x_199 = x_4;
goto block_225;
}
}
block_225:
{
lean_object* x_200; lean_object* x_201; 
x_200 = lean_unsigned_to_nat(0u);
x_201 = l_Array_umapMAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__5(x_1, x_200, x_3, x_199);
if (lean_obj_tag(x_201) == 0)
{
if (x_197 == 0)
{
uint8_t x_202; 
x_202 = !lean_is_exclusive(x_201);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_201, 0);
x_204 = l_Lean_mkAppRev(x_198, x_203);
lean_dec(x_203);
lean_ctor_set(x_201, 0, x_204);
return x_201;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_205 = lean_ctor_get(x_201, 0);
x_206 = lean_ctor_get(x_201, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_201);
x_207 = l_Lean_mkAppRev(x_198, x_205);
lean_dec(x_205);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
}
else
{
uint8_t x_209; 
x_209 = !lean_is_exclusive(x_201);
if (x_209 == 0)
{
lean_object* x_210; uint8_t x_211; 
x_210 = lean_ctor_get(x_201, 0);
x_211 = l_Lean_Expr_isLambda(x_198);
if (x_211 == 0)
{
lean_object* x_212; 
x_212 = l_Lean_mkAppRev(x_198, x_210);
lean_dec(x_210);
lean_ctor_set(x_201, 0, x_212);
return x_201;
}
else
{
lean_object* x_213; 
x_213 = l_Lean_Expr_betaRev(x_198, x_210);
lean_dec(x_198);
lean_ctor_set(x_201, 0, x_213);
return x_201;
}
}
else
{
lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_214 = lean_ctor_get(x_201, 0);
x_215 = lean_ctor_get(x_201, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_201);
x_216 = l_Lean_Expr_isLambda(x_198);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; 
x_217 = l_Lean_mkAppRev(x_198, x_214);
lean_dec(x_214);
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_215);
return x_218;
}
else
{
lean_object* x_219; lean_object* x_220; 
x_219 = l_Lean_Expr_betaRev(x_198, x_214);
lean_dec(x_198);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_215);
return x_220;
}
}
}
}
else
{
uint8_t x_221; 
lean_dec(x_198);
x_221 = !lean_is_exclusive(x_201);
if (x_221 == 0)
{
return x_201;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_201, 0);
x_223 = lean_ctor_get(x_201, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_201);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
return x_224;
}
}
}
}
case 5:
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_245 = lean_ctor_get(x_2, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_2, 1);
lean_inc(x_246);
lean_dec(x_2);
x_247 = lean_array_push(x_3, x_246);
x_2 = x_245;
x_3 = x_247;
goto _start;
}
case 6:
{
uint8_t x_249; lean_object* x_250; lean_object* x_251; uint8_t x_278; 
x_249 = l_Lean_Expr_isMVar(x_2);
x_278 = l_Lean_Expr_hasMVar(x_2);
if (x_278 == 0)
{
x_250 = x_2;
x_251 = x_4;
goto block_277;
}
else
{
lean_object* x_279; lean_object* x_280; 
x_279 = lean_ctor_get(x_4, 2);
lean_inc(x_279);
x_280 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_279, x_2);
lean_dec(x_279);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; 
lean_inc(x_2);
x_281 = l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main(x_1, x_2, x_4);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; lean_object* x_283; uint8_t x_284; 
x_282 = lean_ctor_get(x_281, 1);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 0);
lean_inc(x_283);
lean_dec(x_281);
x_284 = !lean_is_exclusive(x_282);
if (x_284 == 0)
{
lean_object* x_285; lean_object* x_286; 
x_285 = lean_ctor_get(x_282, 2);
lean_inc(x_283);
x_286 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_285, x_2, x_283);
lean_ctor_set(x_282, 2, x_286);
x_250 = x_283;
x_251 = x_282;
goto block_277;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_287 = lean_ctor_get(x_282, 0);
x_288 = lean_ctor_get(x_282, 1);
x_289 = lean_ctor_get(x_282, 2);
lean_inc(x_289);
lean_inc(x_288);
lean_inc(x_287);
lean_dec(x_282);
lean_inc(x_283);
x_290 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_289, x_2, x_283);
x_291 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_291, 0, x_287);
lean_ctor_set(x_291, 1, x_288);
lean_ctor_set(x_291, 2, x_290);
x_250 = x_283;
x_251 = x_291;
goto block_277;
}
}
else
{
uint8_t x_292; 
lean_dec(x_3);
lean_dec(x_2);
x_292 = !lean_is_exclusive(x_281);
if (x_292 == 0)
{
return x_281;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = lean_ctor_get(x_281, 0);
x_294 = lean_ctor_get(x_281, 1);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_281);
x_295 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_295, 0, x_293);
lean_ctor_set(x_295, 1, x_294);
return x_295;
}
}
}
else
{
lean_object* x_296; 
lean_dec(x_2);
x_296 = lean_ctor_get(x_280, 0);
lean_inc(x_296);
lean_dec(x_280);
x_250 = x_296;
x_251 = x_4;
goto block_277;
}
}
block_277:
{
lean_object* x_252; lean_object* x_253; 
x_252 = lean_unsigned_to_nat(0u);
x_253 = l_Array_umapMAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__5(x_1, x_252, x_3, x_251);
if (lean_obj_tag(x_253) == 0)
{
if (x_249 == 0)
{
uint8_t x_254; 
x_254 = !lean_is_exclusive(x_253);
if (x_254 == 0)
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_ctor_get(x_253, 0);
x_256 = l_Lean_mkAppRev(x_250, x_255);
lean_dec(x_255);
lean_ctor_set(x_253, 0, x_256);
return x_253;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_257 = lean_ctor_get(x_253, 0);
x_258 = lean_ctor_get(x_253, 1);
lean_inc(x_258);
lean_inc(x_257);
lean_dec(x_253);
x_259 = l_Lean_mkAppRev(x_250, x_257);
lean_dec(x_257);
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_258);
return x_260;
}
}
else
{
uint8_t x_261; 
x_261 = !lean_is_exclusive(x_253);
if (x_261 == 0)
{
lean_object* x_262; uint8_t x_263; 
x_262 = lean_ctor_get(x_253, 0);
x_263 = l_Lean_Expr_isLambda(x_250);
if (x_263 == 0)
{
lean_object* x_264; 
x_264 = l_Lean_mkAppRev(x_250, x_262);
lean_dec(x_262);
lean_ctor_set(x_253, 0, x_264);
return x_253;
}
else
{
lean_object* x_265; 
x_265 = l_Lean_Expr_betaRev(x_250, x_262);
lean_dec(x_250);
lean_ctor_set(x_253, 0, x_265);
return x_253;
}
}
else
{
lean_object* x_266; lean_object* x_267; uint8_t x_268; 
x_266 = lean_ctor_get(x_253, 0);
x_267 = lean_ctor_get(x_253, 1);
lean_inc(x_267);
lean_inc(x_266);
lean_dec(x_253);
x_268 = l_Lean_Expr_isLambda(x_250);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; 
x_269 = l_Lean_mkAppRev(x_250, x_266);
lean_dec(x_266);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_267);
return x_270;
}
else
{
lean_object* x_271; lean_object* x_272; 
x_271 = l_Lean_Expr_betaRev(x_250, x_266);
lean_dec(x_250);
x_272 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_267);
return x_272;
}
}
}
}
else
{
uint8_t x_273; 
lean_dec(x_250);
x_273 = !lean_is_exclusive(x_253);
if (x_273 == 0)
{
return x_253;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_274 = lean_ctor_get(x_253, 0);
x_275 = lean_ctor_get(x_253, 1);
lean_inc(x_275);
lean_inc(x_274);
lean_dec(x_253);
x_276 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_275);
return x_276;
}
}
}
}
case 7:
{
uint8_t x_297; lean_object* x_298; lean_object* x_299; uint8_t x_326; 
x_297 = l_Lean_Expr_isMVar(x_2);
x_326 = l_Lean_Expr_hasMVar(x_2);
if (x_326 == 0)
{
x_298 = x_2;
x_299 = x_4;
goto block_325;
}
else
{
lean_object* x_327; lean_object* x_328; 
x_327 = lean_ctor_get(x_4, 2);
lean_inc(x_327);
x_328 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_327, x_2);
lean_dec(x_327);
if (lean_obj_tag(x_328) == 0)
{
lean_object* x_329; 
lean_inc(x_2);
x_329 = l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main(x_1, x_2, x_4);
if (lean_obj_tag(x_329) == 0)
{
lean_object* x_330; lean_object* x_331; uint8_t x_332; 
x_330 = lean_ctor_get(x_329, 1);
lean_inc(x_330);
x_331 = lean_ctor_get(x_329, 0);
lean_inc(x_331);
lean_dec(x_329);
x_332 = !lean_is_exclusive(x_330);
if (x_332 == 0)
{
lean_object* x_333; lean_object* x_334; 
x_333 = lean_ctor_get(x_330, 2);
lean_inc(x_331);
x_334 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_333, x_2, x_331);
lean_ctor_set(x_330, 2, x_334);
x_298 = x_331;
x_299 = x_330;
goto block_325;
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_335 = lean_ctor_get(x_330, 0);
x_336 = lean_ctor_get(x_330, 1);
x_337 = lean_ctor_get(x_330, 2);
lean_inc(x_337);
lean_inc(x_336);
lean_inc(x_335);
lean_dec(x_330);
lean_inc(x_331);
x_338 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_337, x_2, x_331);
x_339 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_339, 0, x_335);
lean_ctor_set(x_339, 1, x_336);
lean_ctor_set(x_339, 2, x_338);
x_298 = x_331;
x_299 = x_339;
goto block_325;
}
}
else
{
uint8_t x_340; 
lean_dec(x_3);
lean_dec(x_2);
x_340 = !lean_is_exclusive(x_329);
if (x_340 == 0)
{
return x_329;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_341 = lean_ctor_get(x_329, 0);
x_342 = lean_ctor_get(x_329, 1);
lean_inc(x_342);
lean_inc(x_341);
lean_dec(x_329);
x_343 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_343, 0, x_341);
lean_ctor_set(x_343, 1, x_342);
return x_343;
}
}
}
else
{
lean_object* x_344; 
lean_dec(x_2);
x_344 = lean_ctor_get(x_328, 0);
lean_inc(x_344);
lean_dec(x_328);
x_298 = x_344;
x_299 = x_4;
goto block_325;
}
}
block_325:
{
lean_object* x_300; lean_object* x_301; 
x_300 = lean_unsigned_to_nat(0u);
x_301 = l_Array_umapMAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__5(x_1, x_300, x_3, x_299);
if (lean_obj_tag(x_301) == 0)
{
if (x_297 == 0)
{
uint8_t x_302; 
x_302 = !lean_is_exclusive(x_301);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; 
x_303 = lean_ctor_get(x_301, 0);
x_304 = l_Lean_mkAppRev(x_298, x_303);
lean_dec(x_303);
lean_ctor_set(x_301, 0, x_304);
return x_301;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_305 = lean_ctor_get(x_301, 0);
x_306 = lean_ctor_get(x_301, 1);
lean_inc(x_306);
lean_inc(x_305);
lean_dec(x_301);
x_307 = l_Lean_mkAppRev(x_298, x_305);
lean_dec(x_305);
x_308 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_306);
return x_308;
}
}
else
{
uint8_t x_309; 
x_309 = !lean_is_exclusive(x_301);
if (x_309 == 0)
{
lean_object* x_310; uint8_t x_311; 
x_310 = lean_ctor_get(x_301, 0);
x_311 = l_Lean_Expr_isLambda(x_298);
if (x_311 == 0)
{
lean_object* x_312; 
x_312 = l_Lean_mkAppRev(x_298, x_310);
lean_dec(x_310);
lean_ctor_set(x_301, 0, x_312);
return x_301;
}
else
{
lean_object* x_313; 
x_313 = l_Lean_Expr_betaRev(x_298, x_310);
lean_dec(x_298);
lean_ctor_set(x_301, 0, x_313);
return x_301;
}
}
else
{
lean_object* x_314; lean_object* x_315; uint8_t x_316; 
x_314 = lean_ctor_get(x_301, 0);
x_315 = lean_ctor_get(x_301, 1);
lean_inc(x_315);
lean_inc(x_314);
lean_dec(x_301);
x_316 = l_Lean_Expr_isLambda(x_298);
if (x_316 == 0)
{
lean_object* x_317; lean_object* x_318; 
x_317 = l_Lean_mkAppRev(x_298, x_314);
lean_dec(x_314);
x_318 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_315);
return x_318;
}
else
{
lean_object* x_319; lean_object* x_320; 
x_319 = l_Lean_Expr_betaRev(x_298, x_314);
lean_dec(x_298);
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_315);
return x_320;
}
}
}
}
else
{
uint8_t x_321; 
lean_dec(x_298);
x_321 = !lean_is_exclusive(x_301);
if (x_321 == 0)
{
return x_301;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_ctor_get(x_301, 0);
x_323 = lean_ctor_get(x_301, 1);
lean_inc(x_323);
lean_inc(x_322);
lean_dec(x_301);
x_324 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_324, 0, x_322);
lean_ctor_set(x_324, 1, x_323);
return x_324;
}
}
}
}
case 8:
{
uint8_t x_345; lean_object* x_346; lean_object* x_347; uint8_t x_374; 
x_345 = l_Lean_Expr_isMVar(x_2);
x_374 = l_Lean_Expr_hasMVar(x_2);
if (x_374 == 0)
{
x_346 = x_2;
x_347 = x_4;
goto block_373;
}
else
{
lean_object* x_375; lean_object* x_376; 
x_375 = lean_ctor_get(x_4, 2);
lean_inc(x_375);
x_376 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_375, x_2);
lean_dec(x_375);
if (lean_obj_tag(x_376) == 0)
{
lean_object* x_377; 
lean_inc(x_2);
x_377 = l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main(x_1, x_2, x_4);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; uint8_t x_380; 
x_378 = lean_ctor_get(x_377, 1);
lean_inc(x_378);
x_379 = lean_ctor_get(x_377, 0);
lean_inc(x_379);
lean_dec(x_377);
x_380 = !lean_is_exclusive(x_378);
if (x_380 == 0)
{
lean_object* x_381; lean_object* x_382; 
x_381 = lean_ctor_get(x_378, 2);
lean_inc(x_379);
x_382 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_381, x_2, x_379);
lean_ctor_set(x_378, 2, x_382);
x_346 = x_379;
x_347 = x_378;
goto block_373;
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_383 = lean_ctor_get(x_378, 0);
x_384 = lean_ctor_get(x_378, 1);
x_385 = lean_ctor_get(x_378, 2);
lean_inc(x_385);
lean_inc(x_384);
lean_inc(x_383);
lean_dec(x_378);
lean_inc(x_379);
x_386 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_385, x_2, x_379);
x_387 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_387, 0, x_383);
lean_ctor_set(x_387, 1, x_384);
lean_ctor_set(x_387, 2, x_386);
x_346 = x_379;
x_347 = x_387;
goto block_373;
}
}
else
{
uint8_t x_388; 
lean_dec(x_3);
lean_dec(x_2);
x_388 = !lean_is_exclusive(x_377);
if (x_388 == 0)
{
return x_377;
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_389 = lean_ctor_get(x_377, 0);
x_390 = lean_ctor_get(x_377, 1);
lean_inc(x_390);
lean_inc(x_389);
lean_dec(x_377);
x_391 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_391, 0, x_389);
lean_ctor_set(x_391, 1, x_390);
return x_391;
}
}
}
else
{
lean_object* x_392; 
lean_dec(x_2);
x_392 = lean_ctor_get(x_376, 0);
lean_inc(x_392);
lean_dec(x_376);
x_346 = x_392;
x_347 = x_4;
goto block_373;
}
}
block_373:
{
lean_object* x_348; lean_object* x_349; 
x_348 = lean_unsigned_to_nat(0u);
x_349 = l_Array_umapMAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__5(x_1, x_348, x_3, x_347);
if (lean_obj_tag(x_349) == 0)
{
if (x_345 == 0)
{
uint8_t x_350; 
x_350 = !lean_is_exclusive(x_349);
if (x_350 == 0)
{
lean_object* x_351; lean_object* x_352; 
x_351 = lean_ctor_get(x_349, 0);
x_352 = l_Lean_mkAppRev(x_346, x_351);
lean_dec(x_351);
lean_ctor_set(x_349, 0, x_352);
return x_349;
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_353 = lean_ctor_get(x_349, 0);
x_354 = lean_ctor_get(x_349, 1);
lean_inc(x_354);
lean_inc(x_353);
lean_dec(x_349);
x_355 = l_Lean_mkAppRev(x_346, x_353);
lean_dec(x_353);
x_356 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_356, 0, x_355);
lean_ctor_set(x_356, 1, x_354);
return x_356;
}
}
else
{
uint8_t x_357; 
x_357 = !lean_is_exclusive(x_349);
if (x_357 == 0)
{
lean_object* x_358; uint8_t x_359; 
x_358 = lean_ctor_get(x_349, 0);
x_359 = l_Lean_Expr_isLambda(x_346);
if (x_359 == 0)
{
lean_object* x_360; 
x_360 = l_Lean_mkAppRev(x_346, x_358);
lean_dec(x_358);
lean_ctor_set(x_349, 0, x_360);
return x_349;
}
else
{
lean_object* x_361; 
x_361 = l_Lean_Expr_betaRev(x_346, x_358);
lean_dec(x_346);
lean_ctor_set(x_349, 0, x_361);
return x_349;
}
}
else
{
lean_object* x_362; lean_object* x_363; uint8_t x_364; 
x_362 = lean_ctor_get(x_349, 0);
x_363 = lean_ctor_get(x_349, 1);
lean_inc(x_363);
lean_inc(x_362);
lean_dec(x_349);
x_364 = l_Lean_Expr_isLambda(x_346);
if (x_364 == 0)
{
lean_object* x_365; lean_object* x_366; 
x_365 = l_Lean_mkAppRev(x_346, x_362);
lean_dec(x_362);
x_366 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_363);
return x_366;
}
else
{
lean_object* x_367; lean_object* x_368; 
x_367 = l_Lean_Expr_betaRev(x_346, x_362);
lean_dec(x_346);
x_368 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set(x_368, 1, x_363);
return x_368;
}
}
}
}
else
{
uint8_t x_369; 
lean_dec(x_346);
x_369 = !lean_is_exclusive(x_349);
if (x_369 == 0)
{
return x_349;
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_370 = lean_ctor_get(x_349, 0);
x_371 = lean_ctor_get(x_349, 1);
lean_inc(x_371);
lean_inc(x_370);
lean_dec(x_349);
x_372 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_372, 0, x_370);
lean_ctor_set(x_372, 1, x_371);
return x_372;
}
}
}
}
case 9:
{
uint8_t x_393; lean_object* x_394; lean_object* x_395; uint8_t x_422; 
x_393 = l_Lean_Expr_isMVar(x_2);
x_422 = l_Lean_Expr_hasMVar(x_2);
if (x_422 == 0)
{
x_394 = x_2;
x_395 = x_4;
goto block_421;
}
else
{
lean_object* x_423; lean_object* x_424; 
x_423 = lean_ctor_get(x_4, 2);
lean_inc(x_423);
x_424 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_423, x_2);
lean_dec(x_423);
if (lean_obj_tag(x_424) == 0)
{
lean_object* x_425; 
lean_inc(x_2);
x_425 = l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main(x_1, x_2, x_4);
if (lean_obj_tag(x_425) == 0)
{
lean_object* x_426; lean_object* x_427; uint8_t x_428; 
x_426 = lean_ctor_get(x_425, 1);
lean_inc(x_426);
x_427 = lean_ctor_get(x_425, 0);
lean_inc(x_427);
lean_dec(x_425);
x_428 = !lean_is_exclusive(x_426);
if (x_428 == 0)
{
lean_object* x_429; lean_object* x_430; 
x_429 = lean_ctor_get(x_426, 2);
lean_inc(x_427);
x_430 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_429, x_2, x_427);
lean_ctor_set(x_426, 2, x_430);
x_394 = x_427;
x_395 = x_426;
goto block_421;
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_431 = lean_ctor_get(x_426, 0);
x_432 = lean_ctor_get(x_426, 1);
x_433 = lean_ctor_get(x_426, 2);
lean_inc(x_433);
lean_inc(x_432);
lean_inc(x_431);
lean_dec(x_426);
lean_inc(x_427);
x_434 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_433, x_2, x_427);
x_435 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_435, 0, x_431);
lean_ctor_set(x_435, 1, x_432);
lean_ctor_set(x_435, 2, x_434);
x_394 = x_427;
x_395 = x_435;
goto block_421;
}
}
else
{
uint8_t x_436; 
lean_dec(x_3);
lean_dec(x_2);
x_436 = !lean_is_exclusive(x_425);
if (x_436 == 0)
{
return x_425;
}
else
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_437 = lean_ctor_get(x_425, 0);
x_438 = lean_ctor_get(x_425, 1);
lean_inc(x_438);
lean_inc(x_437);
lean_dec(x_425);
x_439 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_439, 0, x_437);
lean_ctor_set(x_439, 1, x_438);
return x_439;
}
}
}
else
{
lean_object* x_440; 
lean_dec(x_2);
x_440 = lean_ctor_get(x_424, 0);
lean_inc(x_440);
lean_dec(x_424);
x_394 = x_440;
x_395 = x_4;
goto block_421;
}
}
block_421:
{
lean_object* x_396; lean_object* x_397; 
x_396 = lean_unsigned_to_nat(0u);
x_397 = l_Array_umapMAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__5(x_1, x_396, x_3, x_395);
if (lean_obj_tag(x_397) == 0)
{
if (x_393 == 0)
{
uint8_t x_398; 
x_398 = !lean_is_exclusive(x_397);
if (x_398 == 0)
{
lean_object* x_399; lean_object* x_400; 
x_399 = lean_ctor_get(x_397, 0);
x_400 = l_Lean_mkAppRev(x_394, x_399);
lean_dec(x_399);
lean_ctor_set(x_397, 0, x_400);
return x_397;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_401 = lean_ctor_get(x_397, 0);
x_402 = lean_ctor_get(x_397, 1);
lean_inc(x_402);
lean_inc(x_401);
lean_dec(x_397);
x_403 = l_Lean_mkAppRev(x_394, x_401);
lean_dec(x_401);
x_404 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_404, 0, x_403);
lean_ctor_set(x_404, 1, x_402);
return x_404;
}
}
else
{
uint8_t x_405; 
x_405 = !lean_is_exclusive(x_397);
if (x_405 == 0)
{
lean_object* x_406; uint8_t x_407; 
x_406 = lean_ctor_get(x_397, 0);
x_407 = l_Lean_Expr_isLambda(x_394);
if (x_407 == 0)
{
lean_object* x_408; 
x_408 = l_Lean_mkAppRev(x_394, x_406);
lean_dec(x_406);
lean_ctor_set(x_397, 0, x_408);
return x_397;
}
else
{
lean_object* x_409; 
x_409 = l_Lean_Expr_betaRev(x_394, x_406);
lean_dec(x_394);
lean_ctor_set(x_397, 0, x_409);
return x_397;
}
}
else
{
lean_object* x_410; lean_object* x_411; uint8_t x_412; 
x_410 = lean_ctor_get(x_397, 0);
x_411 = lean_ctor_get(x_397, 1);
lean_inc(x_411);
lean_inc(x_410);
lean_dec(x_397);
x_412 = l_Lean_Expr_isLambda(x_394);
if (x_412 == 0)
{
lean_object* x_413; lean_object* x_414; 
x_413 = l_Lean_mkAppRev(x_394, x_410);
lean_dec(x_410);
x_414 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_414, 0, x_413);
lean_ctor_set(x_414, 1, x_411);
return x_414;
}
else
{
lean_object* x_415; lean_object* x_416; 
x_415 = l_Lean_Expr_betaRev(x_394, x_410);
lean_dec(x_394);
x_416 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_416, 0, x_415);
lean_ctor_set(x_416, 1, x_411);
return x_416;
}
}
}
}
else
{
uint8_t x_417; 
lean_dec(x_394);
x_417 = !lean_is_exclusive(x_397);
if (x_417 == 0)
{
return x_397;
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_418 = lean_ctor_get(x_397, 0);
x_419 = lean_ctor_get(x_397, 1);
lean_inc(x_419);
lean_inc(x_418);
lean_dec(x_397);
x_420 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_420, 0, x_418);
lean_ctor_set(x_420, 1, x_419);
return x_420;
}
}
}
}
case 10:
{
uint8_t x_441; lean_object* x_442; lean_object* x_443; uint8_t x_470; 
x_441 = l_Lean_Expr_isMVar(x_2);
x_470 = l_Lean_Expr_hasMVar(x_2);
if (x_470 == 0)
{
x_442 = x_2;
x_443 = x_4;
goto block_469;
}
else
{
lean_object* x_471; lean_object* x_472; 
x_471 = lean_ctor_get(x_4, 2);
lean_inc(x_471);
x_472 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_471, x_2);
lean_dec(x_471);
if (lean_obj_tag(x_472) == 0)
{
lean_object* x_473; 
lean_inc(x_2);
x_473 = l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main(x_1, x_2, x_4);
if (lean_obj_tag(x_473) == 0)
{
lean_object* x_474; lean_object* x_475; uint8_t x_476; 
x_474 = lean_ctor_get(x_473, 1);
lean_inc(x_474);
x_475 = lean_ctor_get(x_473, 0);
lean_inc(x_475);
lean_dec(x_473);
x_476 = !lean_is_exclusive(x_474);
if (x_476 == 0)
{
lean_object* x_477; lean_object* x_478; 
x_477 = lean_ctor_get(x_474, 2);
lean_inc(x_475);
x_478 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_477, x_2, x_475);
lean_ctor_set(x_474, 2, x_478);
x_442 = x_475;
x_443 = x_474;
goto block_469;
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_479 = lean_ctor_get(x_474, 0);
x_480 = lean_ctor_get(x_474, 1);
x_481 = lean_ctor_get(x_474, 2);
lean_inc(x_481);
lean_inc(x_480);
lean_inc(x_479);
lean_dec(x_474);
lean_inc(x_475);
x_482 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_481, x_2, x_475);
x_483 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_483, 0, x_479);
lean_ctor_set(x_483, 1, x_480);
lean_ctor_set(x_483, 2, x_482);
x_442 = x_475;
x_443 = x_483;
goto block_469;
}
}
else
{
uint8_t x_484; 
lean_dec(x_3);
lean_dec(x_2);
x_484 = !lean_is_exclusive(x_473);
if (x_484 == 0)
{
return x_473;
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; 
x_485 = lean_ctor_get(x_473, 0);
x_486 = lean_ctor_get(x_473, 1);
lean_inc(x_486);
lean_inc(x_485);
lean_dec(x_473);
x_487 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_487, 0, x_485);
lean_ctor_set(x_487, 1, x_486);
return x_487;
}
}
}
else
{
lean_object* x_488; 
lean_dec(x_2);
x_488 = lean_ctor_get(x_472, 0);
lean_inc(x_488);
lean_dec(x_472);
x_442 = x_488;
x_443 = x_4;
goto block_469;
}
}
block_469:
{
lean_object* x_444; lean_object* x_445; 
x_444 = lean_unsigned_to_nat(0u);
x_445 = l_Array_umapMAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__5(x_1, x_444, x_3, x_443);
if (lean_obj_tag(x_445) == 0)
{
if (x_441 == 0)
{
uint8_t x_446; 
x_446 = !lean_is_exclusive(x_445);
if (x_446 == 0)
{
lean_object* x_447; lean_object* x_448; 
x_447 = lean_ctor_get(x_445, 0);
x_448 = l_Lean_mkAppRev(x_442, x_447);
lean_dec(x_447);
lean_ctor_set(x_445, 0, x_448);
return x_445;
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; 
x_449 = lean_ctor_get(x_445, 0);
x_450 = lean_ctor_get(x_445, 1);
lean_inc(x_450);
lean_inc(x_449);
lean_dec(x_445);
x_451 = l_Lean_mkAppRev(x_442, x_449);
lean_dec(x_449);
x_452 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_452, 0, x_451);
lean_ctor_set(x_452, 1, x_450);
return x_452;
}
}
else
{
uint8_t x_453; 
x_453 = !lean_is_exclusive(x_445);
if (x_453 == 0)
{
lean_object* x_454; uint8_t x_455; 
x_454 = lean_ctor_get(x_445, 0);
x_455 = l_Lean_Expr_isLambda(x_442);
if (x_455 == 0)
{
lean_object* x_456; 
x_456 = l_Lean_mkAppRev(x_442, x_454);
lean_dec(x_454);
lean_ctor_set(x_445, 0, x_456);
return x_445;
}
else
{
lean_object* x_457; 
x_457 = l_Lean_Expr_betaRev(x_442, x_454);
lean_dec(x_442);
lean_ctor_set(x_445, 0, x_457);
return x_445;
}
}
else
{
lean_object* x_458; lean_object* x_459; uint8_t x_460; 
x_458 = lean_ctor_get(x_445, 0);
x_459 = lean_ctor_get(x_445, 1);
lean_inc(x_459);
lean_inc(x_458);
lean_dec(x_445);
x_460 = l_Lean_Expr_isLambda(x_442);
if (x_460 == 0)
{
lean_object* x_461; lean_object* x_462; 
x_461 = l_Lean_mkAppRev(x_442, x_458);
lean_dec(x_458);
x_462 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_462, 0, x_461);
lean_ctor_set(x_462, 1, x_459);
return x_462;
}
else
{
lean_object* x_463; lean_object* x_464; 
x_463 = l_Lean_Expr_betaRev(x_442, x_458);
lean_dec(x_442);
x_464 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_464, 0, x_463);
lean_ctor_set(x_464, 1, x_459);
return x_464;
}
}
}
}
else
{
uint8_t x_465; 
lean_dec(x_442);
x_465 = !lean_is_exclusive(x_445);
if (x_465 == 0)
{
return x_445;
}
else
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; 
x_466 = lean_ctor_get(x_445, 0);
x_467 = lean_ctor_get(x_445, 1);
lean_inc(x_467);
lean_inc(x_466);
lean_dec(x_445);
x_468 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_468, 0, x_466);
lean_ctor_set(x_468, 1, x_467);
return x_468;
}
}
}
}
case 11:
{
uint8_t x_489; lean_object* x_490; lean_object* x_491; uint8_t x_518; 
x_489 = l_Lean_Expr_isMVar(x_2);
x_518 = l_Lean_Expr_hasMVar(x_2);
if (x_518 == 0)
{
x_490 = x_2;
x_491 = x_4;
goto block_517;
}
else
{
lean_object* x_519; lean_object* x_520; 
x_519 = lean_ctor_get(x_4, 2);
lean_inc(x_519);
x_520 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_519, x_2);
lean_dec(x_519);
if (lean_obj_tag(x_520) == 0)
{
lean_object* x_521; 
lean_inc(x_2);
x_521 = l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main(x_1, x_2, x_4);
if (lean_obj_tag(x_521) == 0)
{
lean_object* x_522; lean_object* x_523; uint8_t x_524; 
x_522 = lean_ctor_get(x_521, 1);
lean_inc(x_522);
x_523 = lean_ctor_get(x_521, 0);
lean_inc(x_523);
lean_dec(x_521);
x_524 = !lean_is_exclusive(x_522);
if (x_524 == 0)
{
lean_object* x_525; lean_object* x_526; 
x_525 = lean_ctor_get(x_522, 2);
lean_inc(x_523);
x_526 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_525, x_2, x_523);
lean_ctor_set(x_522, 2, x_526);
x_490 = x_523;
x_491 = x_522;
goto block_517;
}
else
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; 
x_527 = lean_ctor_get(x_522, 0);
x_528 = lean_ctor_get(x_522, 1);
x_529 = lean_ctor_get(x_522, 2);
lean_inc(x_529);
lean_inc(x_528);
lean_inc(x_527);
lean_dec(x_522);
lean_inc(x_523);
x_530 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_529, x_2, x_523);
x_531 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_531, 0, x_527);
lean_ctor_set(x_531, 1, x_528);
lean_ctor_set(x_531, 2, x_530);
x_490 = x_523;
x_491 = x_531;
goto block_517;
}
}
else
{
uint8_t x_532; 
lean_dec(x_3);
lean_dec(x_2);
x_532 = !lean_is_exclusive(x_521);
if (x_532 == 0)
{
return x_521;
}
else
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; 
x_533 = lean_ctor_get(x_521, 0);
x_534 = lean_ctor_get(x_521, 1);
lean_inc(x_534);
lean_inc(x_533);
lean_dec(x_521);
x_535 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_535, 0, x_533);
lean_ctor_set(x_535, 1, x_534);
return x_535;
}
}
}
else
{
lean_object* x_536; 
lean_dec(x_2);
x_536 = lean_ctor_get(x_520, 0);
lean_inc(x_536);
lean_dec(x_520);
x_490 = x_536;
x_491 = x_4;
goto block_517;
}
}
block_517:
{
lean_object* x_492; lean_object* x_493; 
x_492 = lean_unsigned_to_nat(0u);
x_493 = l_Array_umapMAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__5(x_1, x_492, x_3, x_491);
if (lean_obj_tag(x_493) == 0)
{
if (x_489 == 0)
{
uint8_t x_494; 
x_494 = !lean_is_exclusive(x_493);
if (x_494 == 0)
{
lean_object* x_495; lean_object* x_496; 
x_495 = lean_ctor_get(x_493, 0);
x_496 = l_Lean_mkAppRev(x_490, x_495);
lean_dec(x_495);
lean_ctor_set(x_493, 0, x_496);
return x_493;
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
x_497 = lean_ctor_get(x_493, 0);
x_498 = lean_ctor_get(x_493, 1);
lean_inc(x_498);
lean_inc(x_497);
lean_dec(x_493);
x_499 = l_Lean_mkAppRev(x_490, x_497);
lean_dec(x_497);
x_500 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_500, 0, x_499);
lean_ctor_set(x_500, 1, x_498);
return x_500;
}
}
else
{
uint8_t x_501; 
x_501 = !lean_is_exclusive(x_493);
if (x_501 == 0)
{
lean_object* x_502; uint8_t x_503; 
x_502 = lean_ctor_get(x_493, 0);
x_503 = l_Lean_Expr_isLambda(x_490);
if (x_503 == 0)
{
lean_object* x_504; 
x_504 = l_Lean_mkAppRev(x_490, x_502);
lean_dec(x_502);
lean_ctor_set(x_493, 0, x_504);
return x_493;
}
else
{
lean_object* x_505; 
x_505 = l_Lean_Expr_betaRev(x_490, x_502);
lean_dec(x_490);
lean_ctor_set(x_493, 0, x_505);
return x_493;
}
}
else
{
lean_object* x_506; lean_object* x_507; uint8_t x_508; 
x_506 = lean_ctor_get(x_493, 0);
x_507 = lean_ctor_get(x_493, 1);
lean_inc(x_507);
lean_inc(x_506);
lean_dec(x_493);
x_508 = l_Lean_Expr_isLambda(x_490);
if (x_508 == 0)
{
lean_object* x_509; lean_object* x_510; 
x_509 = l_Lean_mkAppRev(x_490, x_506);
lean_dec(x_506);
x_510 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_510, 0, x_509);
lean_ctor_set(x_510, 1, x_507);
return x_510;
}
else
{
lean_object* x_511; lean_object* x_512; 
x_511 = l_Lean_Expr_betaRev(x_490, x_506);
lean_dec(x_490);
x_512 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_512, 0, x_511);
lean_ctor_set(x_512, 1, x_507);
return x_512;
}
}
}
}
else
{
uint8_t x_513; 
lean_dec(x_490);
x_513 = !lean_is_exclusive(x_493);
if (x_513 == 0)
{
return x_493;
}
else
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; 
x_514 = lean_ctor_get(x_493, 0);
x_515 = lean_ctor_get(x_493, 1);
lean_inc(x_515);
lean_inc(x_514);
lean_dec(x_493);
x_516 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_516, 0, x_514);
lean_ctor_set(x_516, 1, x_515);
return x_516;
}
}
}
}
default: 
{
uint8_t x_537; lean_object* x_538; lean_object* x_539; uint8_t x_566; 
x_537 = l_Lean_Expr_isMVar(x_2);
x_566 = l_Lean_Expr_hasMVar(x_2);
if (x_566 == 0)
{
x_538 = x_2;
x_539 = x_4;
goto block_565;
}
else
{
lean_object* x_567; lean_object* x_568; 
x_567 = lean_ctor_get(x_4, 2);
lean_inc(x_567);
x_568 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_567, x_2);
lean_dec(x_567);
if (lean_obj_tag(x_568) == 0)
{
lean_object* x_569; 
lean_inc(x_2);
x_569 = l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main(x_1, x_2, x_4);
if (lean_obj_tag(x_569) == 0)
{
lean_object* x_570; lean_object* x_571; uint8_t x_572; 
x_570 = lean_ctor_get(x_569, 1);
lean_inc(x_570);
x_571 = lean_ctor_get(x_569, 0);
lean_inc(x_571);
lean_dec(x_569);
x_572 = !lean_is_exclusive(x_570);
if (x_572 == 0)
{
lean_object* x_573; lean_object* x_574; 
x_573 = lean_ctor_get(x_570, 2);
lean_inc(x_571);
x_574 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_573, x_2, x_571);
lean_ctor_set(x_570, 2, x_574);
x_538 = x_571;
x_539 = x_570;
goto block_565;
}
else
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; 
x_575 = lean_ctor_get(x_570, 0);
x_576 = lean_ctor_get(x_570, 1);
x_577 = lean_ctor_get(x_570, 2);
lean_inc(x_577);
lean_inc(x_576);
lean_inc(x_575);
lean_dec(x_570);
lean_inc(x_571);
x_578 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_577, x_2, x_571);
x_579 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_579, 0, x_575);
lean_ctor_set(x_579, 1, x_576);
lean_ctor_set(x_579, 2, x_578);
x_538 = x_571;
x_539 = x_579;
goto block_565;
}
}
else
{
uint8_t x_580; 
lean_dec(x_3);
lean_dec(x_2);
x_580 = !lean_is_exclusive(x_569);
if (x_580 == 0)
{
return x_569;
}
else
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; 
x_581 = lean_ctor_get(x_569, 0);
x_582 = lean_ctor_get(x_569, 1);
lean_inc(x_582);
lean_inc(x_581);
lean_dec(x_569);
x_583 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_583, 0, x_581);
lean_ctor_set(x_583, 1, x_582);
return x_583;
}
}
}
else
{
lean_object* x_584; 
lean_dec(x_2);
x_584 = lean_ctor_get(x_568, 0);
lean_inc(x_584);
lean_dec(x_568);
x_538 = x_584;
x_539 = x_4;
goto block_565;
}
}
block_565:
{
lean_object* x_540; lean_object* x_541; 
x_540 = lean_unsigned_to_nat(0u);
x_541 = l_Array_umapMAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__5(x_1, x_540, x_3, x_539);
if (lean_obj_tag(x_541) == 0)
{
if (x_537 == 0)
{
uint8_t x_542; 
x_542 = !lean_is_exclusive(x_541);
if (x_542 == 0)
{
lean_object* x_543; lean_object* x_544; 
x_543 = lean_ctor_get(x_541, 0);
x_544 = l_Lean_mkAppRev(x_538, x_543);
lean_dec(x_543);
lean_ctor_set(x_541, 0, x_544);
return x_541;
}
else
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; 
x_545 = lean_ctor_get(x_541, 0);
x_546 = lean_ctor_get(x_541, 1);
lean_inc(x_546);
lean_inc(x_545);
lean_dec(x_541);
x_547 = l_Lean_mkAppRev(x_538, x_545);
lean_dec(x_545);
x_548 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_548, 0, x_547);
lean_ctor_set(x_548, 1, x_546);
return x_548;
}
}
else
{
uint8_t x_549; 
x_549 = !lean_is_exclusive(x_541);
if (x_549 == 0)
{
lean_object* x_550; uint8_t x_551; 
x_550 = lean_ctor_get(x_541, 0);
x_551 = l_Lean_Expr_isLambda(x_538);
if (x_551 == 0)
{
lean_object* x_552; 
x_552 = l_Lean_mkAppRev(x_538, x_550);
lean_dec(x_550);
lean_ctor_set(x_541, 0, x_552);
return x_541;
}
else
{
lean_object* x_553; 
x_553 = l_Lean_Expr_betaRev(x_538, x_550);
lean_dec(x_538);
lean_ctor_set(x_541, 0, x_553);
return x_541;
}
}
else
{
lean_object* x_554; lean_object* x_555; uint8_t x_556; 
x_554 = lean_ctor_get(x_541, 0);
x_555 = lean_ctor_get(x_541, 1);
lean_inc(x_555);
lean_inc(x_554);
lean_dec(x_541);
x_556 = l_Lean_Expr_isLambda(x_538);
if (x_556 == 0)
{
lean_object* x_557; lean_object* x_558; 
x_557 = l_Lean_mkAppRev(x_538, x_554);
lean_dec(x_554);
x_558 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_558, 0, x_557);
lean_ctor_set(x_558, 1, x_555);
return x_558;
}
else
{
lean_object* x_559; lean_object* x_560; 
x_559 = l_Lean_Expr_betaRev(x_538, x_554);
lean_dec(x_538);
x_560 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_560, 0, x_559);
lean_ctor_set(x_560, 1, x_555);
return x_560;
}
}
}
}
else
{
uint8_t x_561; 
lean_dec(x_538);
x_561 = !lean_is_exclusive(x_541);
if (x_561 == 0)
{
return x_541;
}
else
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; 
x_562 = lean_ctor_get(x_541, 0);
x_563 = lean_ctor_get(x_541, 1);
lean_inc(x_563);
lean_inc(x_562);
lean_dec(x_541);
x_564 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_564, 0, x_562);
lean_ctor_set(x_564, 1, x_563);
return x_564;
}
}
}
}
}
}
}
lean_object* l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_13; lean_object* x_14; 
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_3, 2);
lean_inc(x_24);
lean_inc(x_22);
lean_inc(x_23);
x_25 = lean_metavar_ctx_get_expr_assignment(x_23, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_24);
x_26 = l_Lean_MetavarContext_getDecl(x_23, x_22);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
x_28 = l___private_Init_Lean_MetavarContext_17__getInScope(x_27, x_1);
x_29 = lean_array_get_size(x_28);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_nat_dec_eq(x_29, x_30);
lean_dec(x_29);
if (x_31 == 0)
{
uint8_t x_32; 
x_32 = l_Lean_MetavarContext_isExprAssignable(x_23, x_22);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_2);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_23);
lean_ctor_set(x_33, 1, x_22);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_3);
return x_34;
}
else
{
lean_object* x_35; 
lean_inc(x_27);
x_35 = l___private_Init_Lean_MetavarContext_13__collectDeps(x_23, x_27, x_28);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_2);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_3);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
lean_dec(x_35);
lean_inc(x_27);
x_39 = l___private_Init_Lean_MetavarContext_14__reduceLocalContext(x_27, x_38);
x_40 = lean_ctor_get(x_26, 4);
lean_inc(x_40);
x_41 = l_Array_filterAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__2(x_38, x_40, x_30, x_30);
x_42 = lean_ctor_get(x_26, 2);
lean_inc(x_42);
x_43 = 0;
lean_inc(x_38);
lean_inc(x_27);
x_44 = l_Lean_MetavarContext_MkBinding_mkBinding___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__3(x_43, x_27, x_38, x_42, x_3);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_ctor_get_uint8(x_26, sizeof(void*)*5);
lean_dec(x_26);
x_48 = l___private_Init_Lean_MetavarContext_21__mkAuxMVar(x_39, x_41, x_45, x_47, x_46);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
x_52 = l_Lean_mkMVar(x_50);
lean_inc(x_27);
x_53 = l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_20__mkMVarApp___spec__1(x_27, x_38, x_38, x_30, x_52);
if (x_47 == 0)
{
uint8_t x_54; 
lean_dec(x_50);
lean_dec(x_38);
lean_dec(x_27);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_51);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
x_56 = lean_metavar_ctx_assign_expr(x_55, x_22, x_53);
lean_ctor_set(x_51, 0, x_56);
lean_ctor_set(x_48, 0, x_53);
return x_48;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_51, 0);
x_58 = lean_ctor_get(x_51, 1);
x_59 = lean_ctor_get(x_51, 2);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_51);
lean_inc(x_53);
x_60 = lean_metavar_ctx_assign_expr(x_57, x_22, x_53);
x_61 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
lean_ctor_set(x_61, 2, x_59);
lean_ctor_set(x_48, 1, x_61);
lean_ctor_set(x_48, 0, x_53);
return x_48;
}
}
else
{
uint8_t x_62; 
lean_dec(x_22);
x_62 = !lean_is_exclusive(x_51);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_51, 0);
x_64 = lean_metavar_ctx_assign_delayed(x_63, x_50, x_27, x_38, x_2);
lean_ctor_set(x_51, 0, x_64);
lean_ctor_set(x_48, 0, x_53);
return x_48;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_51, 0);
x_66 = lean_ctor_get(x_51, 1);
x_67 = lean_ctor_get(x_51, 2);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_51);
x_68 = lean_metavar_ctx_assign_delayed(x_65, x_50, x_27, x_38, x_2);
x_69 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
lean_ctor_set(x_69, 2, x_67);
lean_ctor_set(x_48, 1, x_69);
lean_ctor_set(x_48, 0, x_53);
return x_48;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_48, 0);
x_71 = lean_ctor_get(x_48, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_48);
lean_inc(x_70);
x_72 = l_Lean_mkMVar(x_70);
lean_inc(x_27);
x_73 = l_Array_iterateMAux___main___at___private_Init_Lean_MetavarContext_20__mkMVarApp___spec__1(x_27, x_38, x_38, x_30, x_72);
if (x_47 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_70);
lean_dec(x_38);
lean_dec(x_27);
lean_dec(x_2);
x_74 = lean_ctor_get(x_71, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_71, 2);
lean_inc(x_76);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 lean_ctor_release(x_71, 2);
 x_77 = x_71;
} else {
 lean_dec_ref(x_71);
 x_77 = lean_box(0);
}
lean_inc(x_73);
x_78 = lean_metavar_ctx_assign_expr(x_74, x_22, x_73);
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(0, 3, 0);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_75);
lean_ctor_set(x_79, 2, x_76);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_73);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_22);
x_81 = lean_ctor_get(x_71, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_71, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_71, 2);
lean_inc(x_83);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 lean_ctor_release(x_71, 2);
 x_84 = x_71;
} else {
 lean_dec_ref(x_71);
 x_84 = lean_box(0);
}
x_85 = lean_metavar_ctx_assign_delayed(x_81, x_70, x_27, x_38, x_2);
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(0, 3, 0);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_82);
lean_ctor_set(x_86, 2, x_83);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_73);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_2);
x_88 = !lean_is_exclusive(x_44);
if (x_88 == 0)
{
return x_44;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_44, 0);
x_90 = lean_ctor_get(x_44, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_44);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
}
else
{
lean_object* x_92; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_22);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_2);
lean_ctor_set(x_92, 1, x_3);
return x_92;
}
}
else
{
lean_object* x_93; uint8_t x_94; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_2);
x_93 = lean_ctor_get(x_25, 0);
lean_inc(x_93);
lean_dec(x_25);
x_94 = l_Lean_Expr_hasMVar(x_93);
if (x_94 == 0)
{
lean_object* x_95; 
lean_dec(x_24);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_3);
return x_95;
}
else
{
lean_object* x_96; 
x_96 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_24, x_93);
lean_dec(x_24);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; 
lean_inc(x_93);
x_97 = l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main(x_1, x_93, x_3);
if (lean_obj_tag(x_97) == 0)
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; uint8_t x_100; 
x_99 = lean_ctor_get(x_97, 1);
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_97, 0);
x_102 = lean_ctor_get(x_99, 2);
lean_inc(x_101);
x_103 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_102, x_93, x_101);
lean_ctor_set(x_99, 2, x_103);
return x_97;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_104 = lean_ctor_get(x_97, 0);
x_105 = lean_ctor_get(x_99, 0);
x_106 = lean_ctor_get(x_99, 1);
x_107 = lean_ctor_get(x_99, 2);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_99);
lean_inc(x_104);
x_108 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_107, x_93, x_104);
x_109 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_109, 0, x_105);
lean_ctor_set(x_109, 1, x_106);
lean_ctor_set(x_109, 2, x_108);
lean_ctor_set(x_97, 1, x_109);
return x_97;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_110 = lean_ctor_get(x_97, 1);
x_111 = lean_ctor_get(x_97, 0);
lean_inc(x_110);
lean_inc(x_111);
lean_dec(x_97);
x_112 = lean_ctor_get(x_110, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_110, 2);
lean_inc(x_114);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 lean_ctor_release(x_110, 2);
 x_115 = x_110;
} else {
 lean_dec_ref(x_110);
 x_115 = lean_box(0);
}
lean_inc(x_111);
x_116 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_114, x_93, x_111);
if (lean_is_scalar(x_115)) {
 x_117 = lean_alloc_ctor(0, 3, 0);
} else {
 x_117 = x_115;
}
lean_ctor_set(x_117, 0, x_112);
lean_ctor_set(x_117, 1, x_113);
lean_ctor_set(x_117, 2, x_116);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_111);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
else
{
uint8_t x_119; 
lean_dec(x_93);
x_119 = !lean_is_exclusive(x_97);
if (x_119 == 0)
{
return x_97;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_97, 0);
x_121 = lean_ctor_get(x_97, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_97);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_93);
x_123 = lean_ctor_get(x_96, 0);
lean_inc(x_123);
lean_dec(x_96);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_3);
return x_124;
}
}
}
}
case 5:
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_125 = lean_unsigned_to_nat(0u);
x_126 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_125);
x_127 = lean_mk_empty_array_with_capacity(x_126);
lean_dec(x_126);
x_128 = l___private_Init_Lean_Expr_5__withAppRevAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__6(x_1, x_2, x_127, x_3);
return x_128;
}
case 6:
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_164; 
x_129 = lean_ctor_get(x_2, 1);
lean_inc(x_129);
x_130 = lean_ctor_get(x_2, 2);
lean_inc(x_130);
x_164 = l_Lean_Expr_hasMVar(x_129);
if (x_164 == 0)
{
x_131 = x_129;
x_132 = x_3;
goto block_163;
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_3, 2);
lean_inc(x_165);
x_166 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_165, x_129);
lean_dec(x_165);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; 
lean_inc(x_129);
x_167 = l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main(x_1, x_129, x_3);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 0);
lean_inc(x_169);
lean_dec(x_167);
x_170 = !lean_is_exclusive(x_168);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_168, 2);
lean_inc(x_169);
x_172 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_171, x_129, x_169);
lean_ctor_set(x_168, 2, x_172);
x_131 = x_169;
x_132 = x_168;
goto block_163;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_173 = lean_ctor_get(x_168, 0);
x_174 = lean_ctor_get(x_168, 1);
x_175 = lean_ctor_get(x_168, 2);
lean_inc(x_175);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_168);
lean_inc(x_169);
x_176 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_175, x_129, x_169);
x_177 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_177, 0, x_173);
lean_ctor_set(x_177, 1, x_174);
lean_ctor_set(x_177, 2, x_176);
x_131 = x_169;
x_132 = x_177;
goto block_163;
}
}
else
{
uint8_t x_178; 
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_2);
x_178 = !lean_is_exclusive(x_167);
if (x_178 == 0)
{
return x_167;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_167, 0);
x_180 = lean_ctor_get(x_167, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_167);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
}
}
else
{
lean_object* x_182; 
lean_dec(x_129);
x_182 = lean_ctor_get(x_166, 0);
lean_inc(x_182);
lean_dec(x_166);
x_131 = x_182;
x_132 = x_3;
goto block_163;
}
}
block_163:
{
lean_object* x_133; lean_object* x_134; uint8_t x_144; 
x_144 = l_Lean_Expr_hasMVar(x_130);
if (x_144 == 0)
{
x_133 = x_130;
x_134 = x_132;
goto block_143;
}
else
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_ctor_get(x_132, 2);
lean_inc(x_145);
x_146 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_145, x_130);
lean_dec(x_145);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; 
lean_inc(x_130);
x_147 = l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main(x_1, x_130, x_132);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 0);
lean_inc(x_149);
lean_dec(x_147);
x_150 = !lean_is_exclusive(x_148);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_148, 2);
lean_inc(x_149);
x_152 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_151, x_130, x_149);
lean_ctor_set(x_148, 2, x_152);
x_133 = x_149;
x_134 = x_148;
goto block_143;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_153 = lean_ctor_get(x_148, 0);
x_154 = lean_ctor_get(x_148, 1);
x_155 = lean_ctor_get(x_148, 2);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_148);
lean_inc(x_149);
x_156 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_155, x_130, x_149);
x_157 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_157, 0, x_153);
lean_ctor_set(x_157, 1, x_154);
lean_ctor_set(x_157, 2, x_156);
x_133 = x_149;
x_134 = x_157;
goto block_143;
}
}
else
{
uint8_t x_158; 
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_2);
x_158 = !lean_is_exclusive(x_147);
if (x_158 == 0)
{
return x_147;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_147, 0);
x_160 = lean_ctor_get(x_147, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_147);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
else
{
lean_object* x_162; 
lean_dec(x_130);
x_162 = lean_ctor_get(x_146, 0);
lean_inc(x_162);
lean_dec(x_146);
x_133 = x_162;
x_134 = x_132;
goto block_143;
}
}
block_143:
{
if (lean_obj_tag(x_2) == 6)
{
uint64_t x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; 
x_135 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
x_136 = (uint8_t)((x_135 << 24) >> 61);
x_137 = lean_expr_update_lambda(x_2, x_136, x_131, x_133);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_134);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_133);
lean_dec(x_131);
lean_dec(x_2);
x_139 = l_Lean_Expr_Inhabited;
x_140 = l_Lean_Expr_updateLambdaE_x21___closed__1;
x_141 = lean_panic_fn(x_140);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_134);
return x_142;
}
}
}
}
case 7:
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_218; 
x_183 = lean_ctor_get(x_2, 1);
lean_inc(x_183);
x_184 = lean_ctor_get(x_2, 2);
lean_inc(x_184);
x_218 = l_Lean_Expr_hasMVar(x_183);
if (x_218 == 0)
{
x_185 = x_183;
x_186 = x_3;
goto block_217;
}
else
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_3, 2);
lean_inc(x_219);
x_220 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_219, x_183);
lean_dec(x_219);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; 
lean_inc(x_183);
x_221 = l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main(x_1, x_183, x_3);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_222 = lean_ctor_get(x_221, 1);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 0);
lean_inc(x_223);
lean_dec(x_221);
x_224 = !lean_is_exclusive(x_222);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; 
x_225 = lean_ctor_get(x_222, 2);
lean_inc(x_223);
x_226 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_225, x_183, x_223);
lean_ctor_set(x_222, 2, x_226);
x_185 = x_223;
x_186 = x_222;
goto block_217;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_227 = lean_ctor_get(x_222, 0);
x_228 = lean_ctor_get(x_222, 1);
x_229 = lean_ctor_get(x_222, 2);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_222);
lean_inc(x_223);
x_230 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_229, x_183, x_223);
x_231 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_231, 0, x_227);
lean_ctor_set(x_231, 1, x_228);
lean_ctor_set(x_231, 2, x_230);
x_185 = x_223;
x_186 = x_231;
goto block_217;
}
}
else
{
uint8_t x_232; 
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_2);
x_232 = !lean_is_exclusive(x_221);
if (x_232 == 0)
{
return x_221;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_233 = lean_ctor_get(x_221, 0);
x_234 = lean_ctor_get(x_221, 1);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_221);
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_234);
return x_235;
}
}
}
else
{
lean_object* x_236; 
lean_dec(x_183);
x_236 = lean_ctor_get(x_220, 0);
lean_inc(x_236);
lean_dec(x_220);
x_185 = x_236;
x_186 = x_3;
goto block_217;
}
}
block_217:
{
lean_object* x_187; lean_object* x_188; uint8_t x_198; 
x_198 = l_Lean_Expr_hasMVar(x_184);
if (x_198 == 0)
{
x_187 = x_184;
x_188 = x_186;
goto block_197;
}
else
{
lean_object* x_199; lean_object* x_200; 
x_199 = lean_ctor_get(x_186, 2);
lean_inc(x_199);
x_200 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_199, x_184);
lean_dec(x_199);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; 
lean_inc(x_184);
x_201 = l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main(x_1, x_184, x_186);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_202 = lean_ctor_get(x_201, 1);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 0);
lean_inc(x_203);
lean_dec(x_201);
x_204 = !lean_is_exclusive(x_202);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_202, 2);
lean_inc(x_203);
x_206 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_205, x_184, x_203);
lean_ctor_set(x_202, 2, x_206);
x_187 = x_203;
x_188 = x_202;
goto block_197;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_207 = lean_ctor_get(x_202, 0);
x_208 = lean_ctor_get(x_202, 1);
x_209 = lean_ctor_get(x_202, 2);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_202);
lean_inc(x_203);
x_210 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_209, x_184, x_203);
x_211 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_211, 0, x_207);
lean_ctor_set(x_211, 1, x_208);
lean_ctor_set(x_211, 2, x_210);
x_187 = x_203;
x_188 = x_211;
goto block_197;
}
}
else
{
uint8_t x_212; 
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_2);
x_212 = !lean_is_exclusive(x_201);
if (x_212 == 0)
{
return x_201;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_201, 0);
x_214 = lean_ctor_get(x_201, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_201);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
}
else
{
lean_object* x_216; 
lean_dec(x_184);
x_216 = lean_ctor_get(x_200, 0);
lean_inc(x_216);
lean_dec(x_200);
x_187 = x_216;
x_188 = x_186;
goto block_197;
}
}
block_197:
{
if (lean_obj_tag(x_2) == 7)
{
uint64_t x_189; uint8_t x_190; lean_object* x_191; lean_object* x_192; 
x_189 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
x_190 = (uint8_t)((x_189 << 24) >> 61);
x_191 = lean_expr_update_forall(x_2, x_190, x_185, x_187);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_188);
return x_192;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_187);
lean_dec(x_185);
lean_dec(x_2);
x_193 = l_Lean_Expr_Inhabited;
x_194 = l_Lean_Expr_updateForallE_x21___closed__1;
x_195 = lean_panic_fn(x_194);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_188);
return x_196;
}
}
}
}
case 8:
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_293; 
x_237 = lean_ctor_get(x_2, 1);
lean_inc(x_237);
x_238 = lean_ctor_get(x_2, 2);
lean_inc(x_238);
x_239 = lean_ctor_get(x_2, 3);
lean_inc(x_239);
x_293 = l_Lean_Expr_hasMVar(x_237);
if (x_293 == 0)
{
x_240 = x_237;
x_241 = x_3;
goto block_292;
}
else
{
lean_object* x_294; lean_object* x_295; 
x_294 = lean_ctor_get(x_3, 2);
lean_inc(x_294);
x_295 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_294, x_237);
lean_dec(x_294);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; 
lean_inc(x_237);
x_296 = l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main(x_1, x_237, x_3);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; lean_object* x_298; uint8_t x_299; 
x_297 = lean_ctor_get(x_296, 1);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 0);
lean_inc(x_298);
lean_dec(x_296);
x_299 = !lean_is_exclusive(x_297);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; 
x_300 = lean_ctor_get(x_297, 2);
lean_inc(x_298);
x_301 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_300, x_237, x_298);
lean_ctor_set(x_297, 2, x_301);
x_240 = x_298;
x_241 = x_297;
goto block_292;
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_302 = lean_ctor_get(x_297, 0);
x_303 = lean_ctor_get(x_297, 1);
x_304 = lean_ctor_get(x_297, 2);
lean_inc(x_304);
lean_inc(x_303);
lean_inc(x_302);
lean_dec(x_297);
lean_inc(x_298);
x_305 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_304, x_237, x_298);
x_306 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_306, 0, x_302);
lean_ctor_set(x_306, 1, x_303);
lean_ctor_set(x_306, 2, x_305);
x_240 = x_298;
x_241 = x_306;
goto block_292;
}
}
else
{
uint8_t x_307; 
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_2);
x_307 = !lean_is_exclusive(x_296);
if (x_307 == 0)
{
return x_296;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_308 = lean_ctor_get(x_296, 0);
x_309 = lean_ctor_get(x_296, 1);
lean_inc(x_309);
lean_inc(x_308);
lean_dec(x_296);
x_310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_310, 0, x_308);
lean_ctor_set(x_310, 1, x_309);
return x_310;
}
}
}
else
{
lean_object* x_311; 
lean_dec(x_237);
x_311 = lean_ctor_get(x_295, 0);
lean_inc(x_311);
lean_dec(x_295);
x_240 = x_311;
x_241 = x_3;
goto block_292;
}
}
block_292:
{
lean_object* x_242; lean_object* x_243; uint8_t x_273; 
x_273 = l_Lean_Expr_hasMVar(x_238);
if (x_273 == 0)
{
x_242 = x_238;
x_243 = x_241;
goto block_272;
}
else
{
lean_object* x_274; lean_object* x_275; 
x_274 = lean_ctor_get(x_241, 2);
lean_inc(x_274);
x_275 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_274, x_238);
lean_dec(x_274);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; 
lean_inc(x_238);
x_276 = l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main(x_1, x_238, x_241);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; uint8_t x_279; 
x_277 = lean_ctor_get(x_276, 1);
lean_inc(x_277);
x_278 = lean_ctor_get(x_276, 0);
lean_inc(x_278);
lean_dec(x_276);
x_279 = !lean_is_exclusive(x_277);
if (x_279 == 0)
{
lean_object* x_280; lean_object* x_281; 
x_280 = lean_ctor_get(x_277, 2);
lean_inc(x_278);
x_281 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_280, x_238, x_278);
lean_ctor_set(x_277, 2, x_281);
x_242 = x_278;
x_243 = x_277;
goto block_272;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_282 = lean_ctor_get(x_277, 0);
x_283 = lean_ctor_get(x_277, 1);
x_284 = lean_ctor_get(x_277, 2);
lean_inc(x_284);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_277);
lean_inc(x_278);
x_285 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_284, x_238, x_278);
x_286 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_286, 0, x_282);
lean_ctor_set(x_286, 1, x_283);
lean_ctor_set(x_286, 2, x_285);
x_242 = x_278;
x_243 = x_286;
goto block_272;
}
}
else
{
uint8_t x_287; 
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_2);
x_287 = !lean_is_exclusive(x_276);
if (x_287 == 0)
{
return x_276;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_288 = lean_ctor_get(x_276, 0);
x_289 = lean_ctor_get(x_276, 1);
lean_inc(x_289);
lean_inc(x_288);
lean_dec(x_276);
x_290 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_290, 0, x_288);
lean_ctor_set(x_290, 1, x_289);
return x_290;
}
}
}
else
{
lean_object* x_291; 
lean_dec(x_238);
x_291 = lean_ctor_get(x_275, 0);
lean_inc(x_291);
lean_dec(x_275);
x_242 = x_291;
x_243 = x_241;
goto block_272;
}
}
block_272:
{
lean_object* x_244; lean_object* x_245; uint8_t x_253; 
x_253 = l_Lean_Expr_hasMVar(x_239);
if (x_253 == 0)
{
x_244 = x_239;
x_245 = x_243;
goto block_252;
}
else
{
lean_object* x_254; lean_object* x_255; 
x_254 = lean_ctor_get(x_243, 2);
lean_inc(x_254);
x_255 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_254, x_239);
lean_dec(x_254);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; 
lean_inc(x_239);
x_256 = l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main(x_1, x_239, x_243);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; lean_object* x_258; uint8_t x_259; 
x_257 = lean_ctor_get(x_256, 1);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 0);
lean_inc(x_258);
lean_dec(x_256);
x_259 = !lean_is_exclusive(x_257);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; 
x_260 = lean_ctor_get(x_257, 2);
lean_inc(x_258);
x_261 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_260, x_239, x_258);
lean_ctor_set(x_257, 2, x_261);
x_244 = x_258;
x_245 = x_257;
goto block_252;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_262 = lean_ctor_get(x_257, 0);
x_263 = lean_ctor_get(x_257, 1);
x_264 = lean_ctor_get(x_257, 2);
lean_inc(x_264);
lean_inc(x_263);
lean_inc(x_262);
lean_dec(x_257);
lean_inc(x_258);
x_265 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_264, x_239, x_258);
x_266 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_266, 0, x_262);
lean_ctor_set(x_266, 1, x_263);
lean_ctor_set(x_266, 2, x_265);
x_244 = x_258;
x_245 = x_266;
goto block_252;
}
}
else
{
uint8_t x_267; 
lean_dec(x_242);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_2);
x_267 = !lean_is_exclusive(x_256);
if (x_267 == 0)
{
return x_256;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_256, 0);
x_269 = lean_ctor_get(x_256, 1);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_256);
x_270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_270, 0, x_268);
lean_ctor_set(x_270, 1, x_269);
return x_270;
}
}
}
else
{
lean_object* x_271; 
lean_dec(x_239);
x_271 = lean_ctor_get(x_255, 0);
lean_inc(x_271);
lean_dec(x_255);
x_244 = x_271;
x_245 = x_243;
goto block_252;
}
}
block_252:
{
if (lean_obj_tag(x_2) == 8)
{
lean_object* x_246; lean_object* x_247; 
x_246 = lean_expr_update_let(x_2, x_240, x_242, x_244);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_245);
return x_247;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_244);
lean_dec(x_242);
lean_dec(x_240);
lean_dec(x_2);
x_248 = l_Lean_Expr_Inhabited;
x_249 = l_Lean_Expr_updateLet_x21___closed__1;
x_250 = lean_panic_fn(x_249);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_245);
return x_251;
}
}
}
}
}
case 10:
{
lean_object* x_312; uint8_t x_313; 
x_312 = lean_ctor_get(x_2, 1);
lean_inc(x_312);
x_313 = l_Lean_Expr_hasMVar(x_312);
if (x_313 == 0)
{
x_4 = x_312;
x_5 = x_3;
goto block_12;
}
else
{
lean_object* x_314; lean_object* x_315; 
x_314 = lean_ctor_get(x_3, 2);
lean_inc(x_314);
x_315 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_314, x_312);
lean_dec(x_314);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; 
lean_inc(x_312);
x_316 = l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main(x_1, x_312, x_3);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; lean_object* x_318; uint8_t x_319; 
x_317 = lean_ctor_get(x_316, 1);
lean_inc(x_317);
x_318 = lean_ctor_get(x_316, 0);
lean_inc(x_318);
lean_dec(x_316);
x_319 = !lean_is_exclusive(x_317);
if (x_319 == 0)
{
lean_object* x_320; lean_object* x_321; 
x_320 = lean_ctor_get(x_317, 2);
lean_inc(x_318);
x_321 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_320, x_312, x_318);
lean_ctor_set(x_317, 2, x_321);
x_4 = x_318;
x_5 = x_317;
goto block_12;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_322 = lean_ctor_get(x_317, 0);
x_323 = lean_ctor_get(x_317, 1);
x_324 = lean_ctor_get(x_317, 2);
lean_inc(x_324);
lean_inc(x_323);
lean_inc(x_322);
lean_dec(x_317);
lean_inc(x_318);
x_325 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_324, x_312, x_318);
x_326 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_326, 0, x_322);
lean_ctor_set(x_326, 1, x_323);
lean_ctor_set(x_326, 2, x_325);
x_4 = x_318;
x_5 = x_326;
goto block_12;
}
}
else
{
uint8_t x_327; 
lean_dec(x_312);
lean_dec(x_2);
x_327 = !lean_is_exclusive(x_316);
if (x_327 == 0)
{
return x_316;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_328 = lean_ctor_get(x_316, 0);
x_329 = lean_ctor_get(x_316, 1);
lean_inc(x_329);
lean_inc(x_328);
lean_dec(x_316);
x_330 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_330, 0, x_328);
lean_ctor_set(x_330, 1, x_329);
return x_330;
}
}
}
else
{
lean_object* x_331; 
lean_dec(x_312);
x_331 = lean_ctor_get(x_315, 0);
lean_inc(x_331);
lean_dec(x_315);
x_4 = x_331;
x_5 = x_3;
goto block_12;
}
}
}
case 11:
{
lean_object* x_332; uint8_t x_333; 
x_332 = lean_ctor_get(x_2, 2);
lean_inc(x_332);
x_333 = l_Lean_Expr_hasMVar(x_332);
if (x_333 == 0)
{
x_13 = x_332;
x_14 = x_3;
goto block_21;
}
else
{
lean_object* x_334; lean_object* x_335; 
x_334 = lean_ctor_get(x_3, 2);
lean_inc(x_334);
x_335 = l_HashMapImp_find___at___private_Init_Lean_MetavarContext_2__visit___spec__1(x_334, x_332);
lean_dec(x_334);
if (lean_obj_tag(x_335) == 0)
{
lean_object* x_336; 
lean_inc(x_332);
x_336 = l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main(x_1, x_332, x_3);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; uint8_t x_339; 
x_337 = lean_ctor_get(x_336, 1);
lean_inc(x_337);
x_338 = lean_ctor_get(x_336, 0);
lean_inc(x_338);
lean_dec(x_336);
x_339 = !lean_is_exclusive(x_337);
if (x_339 == 0)
{
lean_object* x_340; lean_object* x_341; 
x_340 = lean_ctor_get(x_337, 2);
lean_inc(x_338);
x_341 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_340, x_332, x_338);
lean_ctor_set(x_337, 2, x_341);
x_13 = x_338;
x_14 = x_337;
goto block_21;
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_342 = lean_ctor_get(x_337, 0);
x_343 = lean_ctor_get(x_337, 1);
x_344 = lean_ctor_get(x_337, 2);
lean_inc(x_344);
lean_inc(x_343);
lean_inc(x_342);
lean_dec(x_337);
lean_inc(x_338);
x_345 = l_HashMapImp_insert___at___private_Init_Lean_MetavarContext_2__visit___spec__3(x_344, x_332, x_338);
x_346 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_346, 0, x_342);
lean_ctor_set(x_346, 1, x_343);
lean_ctor_set(x_346, 2, x_345);
x_13 = x_338;
x_14 = x_346;
goto block_21;
}
}
else
{
uint8_t x_347; 
lean_dec(x_332);
lean_dec(x_2);
x_347 = !lean_is_exclusive(x_336);
if (x_347 == 0)
{
return x_336;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_348 = lean_ctor_get(x_336, 0);
x_349 = lean_ctor_get(x_336, 1);
lean_inc(x_349);
lean_inc(x_348);
lean_dec(x_336);
x_350 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_350, 0, x_348);
lean_ctor_set(x_350, 1, x_349);
return x_350;
}
}
}
else
{
lean_object* x_351; 
lean_dec(x_332);
x_351 = lean_ctor_get(x_335, 0);
lean_inc(x_351);
lean_dec(x_335);
x_13 = x_351;
x_14 = x_3;
goto block_21;
}
}
}
default: 
{
lean_object* x_352; 
x_352 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_352, 0, x_2);
lean_ctor_set(x_352, 1, x_3);
return x_352;
}
}
block_12:
{
if (lean_obj_tag(x_2) == 10)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_expr_update_mdata(x_2, x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = l_Lean_Expr_Inhabited;
x_9 = l_Lean_Expr_updateMData_x21___closed__2;
x_10 = lean_panic_fn(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
}
block_21:
{
if (lean_obj_tag(x_2) == 11)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_expr_update_proj(x_2, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
lean_dec(x_2);
x_17 = l_Lean_Expr_Inhabited;
x_18 = l_Lean_Expr_updateProj_x21___closed__2;
x_19 = lean_panic_fn(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
return x_20;
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_filterAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_filterAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Nat_foldRevMAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Nat_foldRevMAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Nat_foldRevMAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Nat_foldRevMAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__4(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_9;
}
}
lean_object* l_Lean_MetavarContext_MkBinding_mkBinding___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_MetavarContext_MkBinding_mkBinding___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__3(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Array_umapMAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_umapMAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__5(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Expr_5__withAppRevAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Expr_5__withAppRevAux___main___at___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___spec__6(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_MetavarContext_MkBinding_elimMVarDeps(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 2);
x_8 = l_HashMap_Inhabited___closed__1;
lean_ctor_set(x_3, 2, x_8);
x_9 = l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main(x_1, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 1);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 2);
lean_dec(x_13);
lean_ctor_set(x_11, 2, x_7);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_11);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_7);
lean_ctor_set(x_9, 1, x_16);
return x_9;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_9, 1);
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 lean_ctor_release(x_17, 2);
 x_21 = x_17;
} else {
 lean_dec_ref(x_17);
 x_21 = lean_box(0);
}
if (lean_is_scalar(x_21)) {
 x_22 = lean_alloc_ctor(0, 3, 0);
} else {
 x_22 = x_21;
}
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_7);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_7);
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
return x_9;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_9, 0);
x_26 = lean_ctor_get(x_9, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_9);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_3, 0);
x_29 = lean_ctor_get(x_3, 1);
x_30 = lean_ctor_get(x_3, 2);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_3);
x_31 = l_HashMap_Inhabited___closed__1;
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set(x_32, 2, x_31);
x_33 = l___private_Init_Lean_MetavarContext_22__elimMVarDepsAux___main(x_1, x_2, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 lean_ctor_release(x_34, 2);
 x_39 = x_34;
} else {
 lean_dec_ref(x_34);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(0, 3, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_40, 2, x_30);
if (lean_is_scalar(x_36)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_36;
}
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_30);
x_42 = lean_ctor_get(x_33, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_44 = x_33;
} else {
 lean_dec_ref(x_33);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
}
}
lean_object* l_Lean_MetavarContext_MkBinding_elimMVarDeps___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MetavarContext_MkBinding_elimMVarDeps(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Nat_foldRevMAux___main___at_Lean_MetavarContext_mkBinding___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Expr_Inhabited;
x_9 = lean_array_get(x_8, x_1, x_2);
x_10 = l_Lean_LocalContext_findFVar(x_3, x_9);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
x_11 = l_monadInhabited___rarg(x_4, x_8);
x_12 = l_Lean_MetavarContext_MkBinding_mkBinding___lambda__1___closed__1;
x_13 = lean_panic_fn(x_12);
x_14 = lean_apply_1(x_13, x_7);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_4);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 3);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_15, sizeof(void*)*4);
lean_dec(x_15);
x_19 = l_Lean_MetavarContext_MkBinding_elimMVarDeps(x_1, x_17, x_7);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_expr_abstract_range(x_21, x_2, x_1);
lean_dec(x_21);
if (x_5 == 0)
{
lean_object* x_23; 
x_23 = l_Lean_mkForall(x_16, x_18, x_22, x_6);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; 
x_24 = l_Lean_mkLambda(x_16, x_18, x_22, x_6);
lean_ctor_set(x_19, 0, x_24);
return x_19;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = lean_expr_abstract_range(x_25, x_2, x_1);
lean_dec(x_25);
if (x_5 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_Lean_mkForall(x_16, x_18, x_27, x_6);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_mkLambda(x_16, x_18, x_27, x_6);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_16);
lean_dec(x_6);
x_32 = !lean_is_exclusive(x_19);
if (x_32 == 0)
{
return x_19;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_19, 0);
x_34 = lean_ctor_get(x_19, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_19);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_15, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_15, 3);
lean_inc(x_37);
x_38 = lean_ctor_get(x_15, 4);
lean_inc(x_38);
lean_dec(x_15);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_expr_has_loose_bvar(x_6, x_39);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_6);
lean_ctor_set(x_41, 1, x_7);
return x_41;
}
else
{
lean_object* x_42; 
x_42 = l_Lean_MetavarContext_MkBinding_elimMVarDeps(x_1, x_37, x_7);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_expr_abstract_range(x_43, x_2, x_1);
lean_dec(x_43);
x_46 = l_Lean_MetavarContext_MkBinding_elimMVarDeps(x_1, x_38, x_44);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_expr_abstract_range(x_48, x_2, x_1);
lean_dec(x_48);
x_50 = 0;
x_51 = l_Lean_mkLet(x_36, x_45, x_49, x_6, x_50);
lean_ctor_set(x_46, 0, x_51);
return x_46;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_46, 0);
x_53 = lean_ctor_get(x_46, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_46);
x_54 = lean_expr_abstract_range(x_52, x_2, x_1);
lean_dec(x_52);
x_55 = 0;
x_56 = l_Lean_mkLet(x_36, x_45, x_54, x_6, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_53);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_dec(x_45);
lean_dec(x_36);
lean_dec(x_6);
x_58 = !lean_is_exclusive(x_46);
if (x_58 == 0)
{
return x_46;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_46, 0);
x_60 = lean_ctor_get(x_46, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_46);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_6);
x_62 = !lean_is_exclusive(x_42);
if (x_62 == 0)
{
return x_42;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_42, 0);
x_64 = lean_ctor_get(x_42, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_42);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
}
}
}
lean_object* l_Nat_foldRevMAux___main___at_Lean_MetavarContext_mkBinding___spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_5, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_5, x_10);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
x_13 = lean_box(x_1);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_11);
lean_inc(x_3);
x_14 = lean_alloc_closure((void*)(l_Nat_foldRevMAux___main___at_Lean_MetavarContext_mkBinding___spec__2___lambda__1___boxed), 7, 6);
lean_closure_set(x_14, 0, x_3);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_2);
lean_closure_set(x_14, 3, x_4);
lean_closure_set(x_14, 4, x_13);
lean_closure_set(x_14, 5, x_6);
x_15 = lean_box(x_1);
x_16 = lean_alloc_closure((void*)(l_Nat_foldRevMAux___main___at_Lean_MetavarContext_mkBinding___spec__2___boxed), 7, 5);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_3);
lean_closure_set(x_16, 3, x_4);
lean_closure_set(x_16, 4, x_11);
x_17 = lean_apply_5(x_12, lean_box(0), lean_box(0), x_14, x_16, x_7);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_ctor_get(x_4, 0);
lean_inc(x_18);
lean_dec(x_4);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_apply_3(x_19, lean_box(0), x_6, x_7);
return x_20;
}
}
}
lean_object* l_Lean_MetavarContext_MkBinding_mkBinding___at_Lean_MetavarContext_mkBinding___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = l_Lean_MetavarContext_MkBinding_elimMVarDeps(x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_expr_abstract_range(x_8, x_6, x_3);
lean_dec(x_8);
x_11 = l_EIO_Monad___closed__1;
x_12 = l_Nat_foldRevMAux___main___at_Lean_MetavarContext_mkBinding___spec__2(x_1, x_2, x_3, x_11, x_6, x_10, x_9);
lean_dec(x_6);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_Lean_MetavarContext_mkBinding(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_MetavarContext_MkBinding_mkBinding___at_Lean_MetavarContext_mkBinding___spec__1(x_1, x_4, x_2, x_3, x_5);
return x_6;
}
}
lean_object* l_Nat_foldRevMAux___main___at_Lean_MetavarContext_mkBinding___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Nat_foldRevMAux___main___at_Lean_MetavarContext_mkBinding___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Nat_foldRevMAux___main___at_Lean_MetavarContext_mkBinding___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Nat_foldRevMAux___main___at_Lean_MetavarContext_mkBinding___spec__2(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
return x_9;
}
}
lean_object* l_Lean_MetavarContext_MkBinding_mkBinding___at_Lean_MetavarContext_mkBinding___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_MetavarContext_MkBinding_mkBinding___at_Lean_MetavarContext_mkBinding___spec__1(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_MetavarContext_mkBinding___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_MetavarContext_mkBinding(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_MetavarContext_mkLambda(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 1;
x_6 = l_Lean_MetavarContext_MkBinding_mkBinding___at_Lean_MetavarContext_mkBinding___spec__1(x_5, x_3, x_1, x_2, x_4);
return x_6;
}
}
lean_object* l_Lean_MetavarContext_mkForall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 0;
x_6 = l_Lean_MetavarContext_MkBinding_mkBinding___at_Lean_MetavarContext_mkBinding___spec__1(x_5, x_3, x_1, x_2, x_4);
return x_6;
}
}
lean_object* l_Lean_MetavarContext_isWellFormed___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_LocalContext_contains(x_2, x_4);
lean_dec(x_4);
lean_dec(x_2);
x_6 = lean_box(x_5);
return x_6;
}
case 2:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = l_Lean_MetavarContext_getDecl(x_1, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
lean_inc(x_2);
x_10 = l_Lean_LocalContext_isSubPrefixOf(x_9, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_inc(x_1);
x_11 = lean_metavar_ctx_get_expr_assignment(x_1, x_7);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; lean_object* x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = 0;
x_13 = lean_box(x_12);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_3 = x_14;
goto _start;
}
}
else
{
uint8_t x_16; lean_object* x_17; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_16 = 1;
x_17 = lean_box(x_16);
return x_17;
}
}
case 5:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
x_20 = l_Lean_Expr_hasExprMVar(x_3);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = l_Lean_Expr_hasFVar(x_3);
lean_dec(x_3);
if (x_21 == 0)
{
uint8_t x_22; lean_object* x_23; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_22 = 0;
x_23 = lean_box(x_22);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; 
lean_inc(x_2);
lean_inc(x_1);
x_24 = l_Lean_MetavarContext_isWellFormed___main(x_1, x_2, x_18);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
uint8_t x_26; lean_object* x_27; 
lean_dec(x_19);
lean_dec(x_2);
lean_dec(x_1);
x_26 = 0;
x_27 = lean_box(x_26);
return x_27;
}
else
{
x_3 = x_19;
goto _start;
}
}
}
else
{
lean_object* x_29; uint8_t x_30; 
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_29 = l_Lean_MetavarContext_isWellFormed___main(x_1, x_2, x_18);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
uint8_t x_31; lean_object* x_32; 
lean_dec(x_19);
lean_dec(x_2);
lean_dec(x_1);
x_31 = 0;
x_32 = lean_box(x_31);
return x_32;
}
else
{
x_3 = x_19;
goto _start;
}
}
}
case 6:
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_3, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_3, 2);
lean_inc(x_35);
x_36 = l_Lean_Expr_hasExprMVar(x_3);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = l_Lean_Expr_hasFVar(x_3);
lean_dec(x_3);
if (x_37 == 0)
{
uint8_t x_38; lean_object* x_39; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_2);
lean_dec(x_1);
x_38 = 0;
x_39 = lean_box(x_38);
return x_39;
}
else
{
lean_object* x_40; uint8_t x_41; 
lean_inc(x_2);
lean_inc(x_1);
x_40 = l_Lean_MetavarContext_isWellFormed___main(x_1, x_2, x_34);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
uint8_t x_42; lean_object* x_43; 
lean_dec(x_35);
lean_dec(x_2);
lean_dec(x_1);
x_42 = 0;
x_43 = lean_box(x_42);
return x_43;
}
else
{
x_3 = x_35;
goto _start;
}
}
}
else
{
lean_object* x_45; uint8_t x_46; 
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_45 = l_Lean_MetavarContext_isWellFormed___main(x_1, x_2, x_34);
x_46 = lean_unbox(x_45);
lean_dec(x_45);
if (x_46 == 0)
{
uint8_t x_47; lean_object* x_48; 
lean_dec(x_35);
lean_dec(x_2);
lean_dec(x_1);
x_47 = 0;
x_48 = lean_box(x_47);
return x_48;
}
else
{
x_3 = x_35;
goto _start;
}
}
}
case 7:
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_3, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_3, 2);
lean_inc(x_51);
x_52 = l_Lean_Expr_hasExprMVar(x_3);
if (x_52 == 0)
{
uint8_t x_53; 
x_53 = l_Lean_Expr_hasFVar(x_3);
lean_dec(x_3);
if (x_53 == 0)
{
uint8_t x_54; lean_object* x_55; 
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_2);
lean_dec(x_1);
x_54 = 0;
x_55 = lean_box(x_54);
return x_55;
}
else
{
lean_object* x_56; uint8_t x_57; 
lean_inc(x_2);
lean_inc(x_1);
x_56 = l_Lean_MetavarContext_isWellFormed___main(x_1, x_2, x_50);
x_57 = lean_unbox(x_56);
lean_dec(x_56);
if (x_57 == 0)
{
uint8_t x_58; lean_object* x_59; 
lean_dec(x_51);
lean_dec(x_2);
lean_dec(x_1);
x_58 = 0;
x_59 = lean_box(x_58);
return x_59;
}
else
{
x_3 = x_51;
goto _start;
}
}
}
else
{
lean_object* x_61; uint8_t x_62; 
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_61 = l_Lean_MetavarContext_isWellFormed___main(x_1, x_2, x_50);
x_62 = lean_unbox(x_61);
lean_dec(x_61);
if (x_62 == 0)
{
uint8_t x_63; lean_object* x_64; 
lean_dec(x_51);
lean_dec(x_2);
lean_dec(x_1);
x_63 = 0;
x_64 = lean_box(x_63);
return x_64;
}
else
{
x_3 = x_51;
goto _start;
}
}
}
case 8:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_66 = lean_ctor_get(x_3, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_3, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_3, 3);
lean_inc(x_68);
x_69 = l_Lean_Expr_hasExprMVar(x_3);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = l_Lean_Expr_hasFVar(x_3);
lean_dec(x_3);
if (x_70 == 0)
{
uint8_t x_71; lean_object* x_72; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_2);
lean_dec(x_1);
x_71 = 0;
x_72 = lean_box(x_71);
return x_72;
}
else
{
lean_object* x_73; uint8_t x_74; 
lean_inc(x_2);
lean_inc(x_1);
x_73 = l_Lean_MetavarContext_isWellFormed___main(x_1, x_2, x_66);
x_74 = lean_unbox(x_73);
lean_dec(x_73);
if (x_74 == 0)
{
uint8_t x_75; lean_object* x_76; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_2);
lean_dec(x_1);
x_75 = 0;
x_76 = lean_box(x_75);
return x_76;
}
else
{
lean_object* x_77; uint8_t x_78; 
lean_inc(x_2);
lean_inc(x_1);
x_77 = l_Lean_MetavarContext_isWellFormed___main(x_1, x_2, x_67);
x_78 = lean_unbox(x_77);
lean_dec(x_77);
if (x_78 == 0)
{
uint8_t x_79; lean_object* x_80; 
lean_dec(x_68);
lean_dec(x_2);
lean_dec(x_1);
x_79 = 0;
x_80 = lean_box(x_79);
return x_80;
}
else
{
x_3 = x_68;
goto _start;
}
}
}
}
else
{
lean_object* x_82; uint8_t x_83; 
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_82 = l_Lean_MetavarContext_isWellFormed___main(x_1, x_2, x_66);
x_83 = lean_unbox(x_82);
lean_dec(x_82);
if (x_83 == 0)
{
uint8_t x_84; lean_object* x_85; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_2);
lean_dec(x_1);
x_84 = 0;
x_85 = lean_box(x_84);
return x_85;
}
else
{
lean_object* x_86; uint8_t x_87; 
lean_inc(x_2);
lean_inc(x_1);
x_86 = l_Lean_MetavarContext_isWellFormed___main(x_1, x_2, x_67);
x_87 = lean_unbox(x_86);
lean_dec(x_86);
if (x_87 == 0)
{
uint8_t x_88; lean_object* x_89; 
lean_dec(x_68);
lean_dec(x_2);
lean_dec(x_1);
x_88 = 0;
x_89 = lean_box(x_88);
return x_89;
}
else
{
x_3 = x_68;
goto _start;
}
}
}
}
case 10:
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_3, 1);
lean_inc(x_91);
lean_dec(x_3);
x_3 = x_91;
goto _start;
}
case 11:
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_3, 2);
lean_inc(x_93);
lean_dec(x_3);
x_3 = x_93;
goto _start;
}
case 12:
{
uint8_t x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_95 = l_Bool_Inhabited;
x_96 = lean_box(x_95);
x_97 = l_unreachable_x21___rarg(x_96);
return x_97;
}
default: 
{
uint8_t x_98; lean_object* x_99; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_98 = 1;
x_99 = lean_box(x_98);
return x_99;
}
}
}
}
lean_object* l_Lean_MetavarContext_isWellFormed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MetavarContext_isWellFormed___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* initialize_Init_Control_Reader(lean_object*);
lean_object* initialize_Init_Data_Nat(lean_object*);
lean_object* initialize_Init_Data_Option(lean_object*);
lean_object* initialize_Init_Lean_Data_NameGenerator(lean_object*);
lean_object* initialize_Init_Lean_Util_MonadCache(lean_object*);
lean_object* initialize_Init_Lean_LocalContext(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_MetavarContext(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Reader(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Data_NameGenerator(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Util_MonadCache(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_LocalContext(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_LocalInstance_hasBeq___closed__1 = _init_l_Lean_LocalInstance_hasBeq___closed__1();
lean_mark_persistent(l_Lean_LocalInstance_hasBeq___closed__1);
l_Lean_LocalInstance_hasBeq = _init_l_Lean_LocalInstance_hasBeq();
lean_mark_persistent(l_Lean_LocalInstance_hasBeq);
l_Lean_MetavarDecl_Inhabited___closed__1 = _init_l_Lean_MetavarDecl_Inhabited___closed__1();
lean_mark_persistent(l_Lean_MetavarDecl_Inhabited___closed__1);
l_Lean_MetavarDecl_Inhabited = _init_l_Lean_MetavarDecl_Inhabited();
lean_mark_persistent(l_Lean_MetavarDecl_Inhabited);
l_Lean_MetavarContext_Inhabited___closed__1 = _init_l_Lean_MetavarContext_Inhabited___closed__1();
lean_mark_persistent(l_Lean_MetavarContext_Inhabited___closed__1);
l_Lean_MetavarContext_Inhabited = _init_l_Lean_MetavarContext_Inhabited();
lean_mark_persistent(l_Lean_MetavarContext_Inhabited);
l_Lean_MetavarContext_getDecl___closed__1 = _init_l_Lean_MetavarContext_getDecl___closed__1();
lean_mark_persistent(l_Lean_MetavarContext_getDecl___closed__1);
l_Lean_MetavarContext_getDecl___closed__2 = _init_l_Lean_MetavarContext_getDecl___closed__2();
lean_mark_persistent(l_Lean_MetavarContext_getDecl___closed__2);
l_Lean_MetavarContext_getDecl___closed__3 = _init_l_Lean_MetavarContext_getDecl___closed__3();
lean_mark_persistent(l_Lean_MetavarContext_getDecl___closed__3);
l_Lean_MetavarContext_getLevelDepth___closed__1 = _init_l_Lean_MetavarContext_getLevelDepth___closed__1();
lean_mark_persistent(l_Lean_MetavarContext_getLevelDepth___closed__1);
l_Lean_MetavarContext_isLevelAssignable___closed__1 = _init_l_Lean_MetavarContext_isLevelAssignable___closed__1();
lean_mark_persistent(l_Lean_MetavarContext_isLevelAssignable___closed__1);
l_Lean_MetavarContext_isLevelAssignable___closed__2 = _init_l_Lean_MetavarContext_isLevelAssignable___closed__2();
lean_mark_persistent(l_Lean_MetavarContext_isLevelAssignable___closed__2);
l___private_Init_Lean_MetavarContext_5__instantiateDelayedAux___main___closed__1 = _init_l___private_Init_Lean_MetavarContext_5__instantiateDelayedAux___main___closed__1();
lean_mark_persistent(l___private_Init_Lean_MetavarContext_5__instantiateDelayedAux___main___closed__1);
l___private_Init_Lean_MetavarContext_5__instantiateDelayedAux___main___closed__2 = _init_l___private_Init_Lean_MetavarContext_5__instantiateDelayedAux___main___closed__2();
lean_mark_persistent(l___private_Init_Lean_MetavarContext_5__instantiateDelayedAux___main___closed__2);
l___private_Init_Lean_MetavarContext_5__instantiateDelayedAux___main___closed__3 = _init_l___private_Init_Lean_MetavarContext_5__instantiateDelayedAux___main___closed__3();
lean_mark_persistent(l___private_Init_Lean_MetavarContext_5__instantiateDelayedAux___main___closed__3);
l_Lean_MetavarContext_instantiateMVars___closed__1 = _init_l_Lean_MetavarContext_instantiateMVars___closed__1();
lean_mark_persistent(l_Lean_MetavarContext_instantiateMVars___closed__1);
l_Lean_MetavarContext_exprDependsOn___closed__1 = _init_l_Lean_MetavarContext_exprDependsOn___closed__1();
lean_mark_persistent(l_Lean_MetavarContext_exprDependsOn___closed__1);
l_Lean_MetavarContext_MkBinding_Exception_toString___closed__1 = _init_l_Lean_MetavarContext_MkBinding_Exception_toString___closed__1();
lean_mark_persistent(l_Lean_MetavarContext_MkBinding_Exception_toString___closed__1);
l_Lean_MetavarContext_MkBinding_Exception_toString___closed__2 = _init_l_Lean_MetavarContext_MkBinding_Exception_toString___closed__2();
lean_mark_persistent(l_Lean_MetavarContext_MkBinding_Exception_toString___closed__2);
l_Lean_MetavarContext_MkBinding_Exception_toString___closed__3 = _init_l_Lean_MetavarContext_MkBinding_Exception_toString___closed__3();
lean_mark_persistent(l_Lean_MetavarContext_MkBinding_Exception_toString___closed__3);
l_Lean_MetavarContext_MkBinding_Exception_toString___closed__4 = _init_l_Lean_MetavarContext_MkBinding_Exception_toString___closed__4();
lean_mark_persistent(l_Lean_MetavarContext_MkBinding_Exception_toString___closed__4);
l_Lean_MetavarContext_MkBinding_Exception_toString___closed__5 = _init_l_Lean_MetavarContext_MkBinding_Exception_toString___closed__5();
lean_mark_persistent(l_Lean_MetavarContext_MkBinding_Exception_toString___closed__5);
l_Lean_MetavarContext_MkBinding_Exception_toString___closed__6 = _init_l_Lean_MetavarContext_MkBinding_Exception_toString___closed__6();
lean_mark_persistent(l_Lean_MetavarContext_MkBinding_Exception_toString___closed__6);
l_Lean_MetavarContext_MkBinding_Exception_hasToString___closed__1 = _init_l_Lean_MetavarContext_MkBinding_Exception_hasToString___closed__1();
lean_mark_persistent(l_Lean_MetavarContext_MkBinding_Exception_hasToString___closed__1);
l_Lean_MetavarContext_MkBinding_Exception_hasToString = _init_l_Lean_MetavarContext_MkBinding_Exception_hasToString();
lean_mark_persistent(l_Lean_MetavarContext_MkBinding_Exception_hasToString);
l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter___closed__1 = _init_l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter___closed__1();
lean_mark_persistent(l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter___closed__1);
l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter___closed__2 = _init_l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter___closed__2();
lean_mark_persistent(l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter___closed__2);
l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter___closed__3 = _init_l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter___closed__3();
lean_mark_persistent(l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter___closed__3);
l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter___closed__4 = _init_l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter___closed__4();
lean_mark_persistent(l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter___closed__4);
l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter = _init_l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter();
lean_mark_persistent(l_Lean_MetavarContext_MkBinding_Lean_MonadHashMapCacheAdapter);
l_Lean_MetavarContext_MkBinding_mkBinding___lambda__1___closed__1 = _init_l_Lean_MetavarContext_MkBinding_mkBinding___lambda__1___closed__1();
lean_mark_persistent(l_Lean_MetavarContext_MkBinding_mkBinding___lambda__1___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
